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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___y_779_; lean_object* v_values_783_; uint8_t v_closed_784_; uint8_t v___x_785_; uint8_t v___x_786_; 
v_values_783_ = lean_ctor_get(v_a_777_, 0);
v_closed_784_ = lean_ctor_get_uint8(v_a_777_, sizeof(void*)*2);
v___x_785_ = l_Std_Queue_isEmpty___redArg(v_values_783_);
v___x_786_ = lean_bool_not(v___x_785_);
if (v___x_786_ == 0)
{
v___y_779_ = v_closed_784_;
goto v___jp_778_;
}
else
{
v___y_779_ = v___x_786_;
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
lean_object* v_a_1166_; lean_object* v_values_1167_; uint8_t v_closed_1168_; uint8_t v___x_1169_; uint8_t v___x_1170_; 
v_a_1166_ = lean_ctor_get(v_x_1150_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v_x_1150_, 1);
v_values_1167_ = lean_ctor_get(v_a_1166_, 0);
lean_inc_ref(v_values_1167_);
v_closed_1168_ = lean_ctor_get_uint8(v_a_1166_, sizeof(void*)*2);
lean_dec(v_a_1166_);
v___x_1169_ = l_Std_Queue_isEmpty___redArg(v_values_1167_);
lean_dec_ref(v_values_1167_);
v___x_1170_ = lean_bool_not(v___x_1169_);
if (v___x_1170_ == 0)
{
v___y_1153_ = v_closed_1168_;
goto v___jp_1152_;
}
else
{
v___y_1153_ = v___x_1170_;
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
if (lean_obj_tag(v_x_1383_) == 0)
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v_x_1383_);
return v___x_1385_;
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1397_; 
v_a_1386_ = lean_ctor_get(v_x_1383_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_x_1383_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1388_ = v_x_1383_;
v_isShared_1389_ = v_isSharedCheck_1397_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v_x_1383_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1397_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
uint8_t v___x_1390_; uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1390_ = lean_unbox(v_a_1386_);
lean_dec(v_a_1386_);
v___x_1391_ = lean_bool_not(v___x_1390_);
v___x_1392_ = lean_box(v___x_1391_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1392_);
v___x_1394_ = v___x_1388_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object* v_x_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_tail_1401_, lean_object* v_x_1402_, lean_object* v_head_1403_, lean_object* v_x_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1401_, v_x_1402_, v_head_1403_, v_x_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object* v_x_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v_x_1414_);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
else
{
lean_object* v_head_1418_; lean_object* v_tail_1419_; lean_object* v___f_1420_; lean_object* v_val_1422_; 
v_head_1418_ = lean_ctor_get(v_x_1413_, 0);
lean_inc_n(v_head_1418_, 2);
v_tail_1419_ = lean_ctor_get(v_x_1413_, 1);
lean_inc(v_tail_1419_);
lean_dec_ref_known(v_x_1413_, 2);
v___f_1420_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1420_, 0, v_tail_1419_);
lean_closure_set(v___f_1420_, 1, v_x_1414_);
lean_closure_set(v___f_1420_, 2, v_head_1418_);
if (lean_obj_tag(v_head_1418_) == 0)
{
lean_object* v___x_1426_; 
lean_dec_ref_known(v_head_1418_, 1);
v___x_1426_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_1422_ = v___x_1426_;
goto v___jp_1421_;
}
else
{
lean_object* v_finished_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1441_; 
v_finished_1427_ = lean_ctor_get(v_head_1418_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_head_1418_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1429_ = v_head_1418_;
v_isShared_1430_ = v_isSharedCheck_1441_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_finished_1427_);
lean_dec(v_head_1418_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1441_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_finished_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; lean_object* v___x_1435_; 
v_finished_1431_ = lean_ctor_get(v_finished_1427_, 0);
lean_inc(v_finished_1431_);
lean_dec_ref(v_finished_1427_);
v___x_1432_ = lean_st_ref_get(v_finished_1431_);
lean_dec(v_finished_1431_);
v___f_1433_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1432_);
v___x_1435_ = v___x_1429_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1432_);
v___x_1435_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = 0;
v___x_1439_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1437_, v___x_1438_, v___x_1436_, v___f_1433_);
v_val_1422_ = v___x_1439_;
goto v___jp_1421_;
}
}
}
v___jp_1421_:
{
lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = 0;
v___x_1425_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1423_, v___x_1424_, v_val_1422_, v___f_1420_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1442_, lean_object* v_x_1443_, lean_object* v_head_1444_, lean_object* v_x_1445_){
_start:
{
if (lean_obj_tag(v_x_1445_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
lean_dec_ref(v_head_1444_);
lean_dec(v_x_1443_);
lean_dec(v_tail_1442_);
v_a_1447_ = lean_ctor_get(v_x_1445_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_x_1445_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1449_ = v_x_1445_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v_x_1445_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
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
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
}
else
{
lean_object* v_a_1456_; uint8_t v___x_1457_; 
v_a_1456_ = lean_ctor_get(v_x_1445_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v_x_1445_, 1);
v___x_1457_ = lean_unbox(v_a_1456_);
lean_dec(v_a_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1458_; 
lean_dec_ref(v_head_1444_);
v___x_1458_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1442_, v_x_1443_);
return v___x_1458_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_head_1444_);
lean_ctor_set(v___x_1459_, 1, v_x_1443_);
v___x_1460_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1442_, v___x_1459_);
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1461_, v_x_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_1465_, lean_object* v___x_1466_, lean_object* v___f_1467_, lean_object* v_x_1468_){
_start:
{
if (lean_obj_tag(v_x_1468_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___f_1467_);
lean_dec(v___x_1466_);
lean_dec(v_eList_1465_);
v_a_1470_ = lean_ctor_get(v_x_1468_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_x_1468_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1472_ = v_x_1468_;
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v_x_1468_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1478_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; 
v_a_1479_ = lean_ctor_get(v_x_1468_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v_x_1468_, 1);
lean_inc(v___x_1466_);
v___x_1480_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1465_, v___x_1466_);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = 0;
v___x_1483_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1481_, v___x_1482_, v___x_1480_, v___f_1467_);
v___f_1484_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1484_, 0, v_a_1479_);
lean_closure_set(v___f_1484_, 1, v___x_1466_);
v___x_1485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1481_, v___x_1482_, v___x_1483_, v___f_1484_);
return v___x_1485_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_1486_, lean_object* v___x_1487_, lean_object* v___f_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v_eList_1486_, v___x_1487_, v___f_1488_, v_x_1489_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_eList_1496_; lean_object* v_dList_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; 
v_eList_1496_ = lean_ctor_get(v_q_1493_, 0);
lean_inc(v_eList_1496_);
v_dList_1497_ = lean_ctor_get(v_q_1493_, 1);
lean_inc(v_dList_1497_);
lean_dec_ref(v_q_1493_);
v___x_1498_ = lean_box(0);
v___x_1499_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1497_, v___x_1498_);
v___f_1500_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = 0;
v___x_1503_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1501_, v___x_1502_, v___x_1499_, v___f_1500_);
v___f_1504_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1504_, 0, v_eList_1496_);
lean_closure_set(v___f_1504_, 1, v___x_1498_);
lean_closure_set(v___f_1504_, 2, v___f_1500_);
v___x_1505_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1501_, v___x_1502_, v___x_1503_, v___f_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1506_, v___y_1507_);
lean_dec(v___y_1507_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1510_, lean_object* v_x_1511_){
_start:
{
if (lean_obj_tag(v_x_1511_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
v_a_1513_ = lean_ctor_get(v_x_1511_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1515_ = v_x_1511_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v_x_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v_values_1523_; lean_object* v_consumers_1524_; uint8_t v_closed_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; 
v_a_1522_ = lean_ctor_get(v_x_1511_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v_x_1511_, 1);
v_values_1523_ = lean_ctor_get(v_a_1522_, 0);
lean_inc_ref(v_values_1523_);
v_consumers_1524_ = lean_ctor_get(v_a_1522_, 1);
lean_inc_ref(v_consumers_1524_);
v_closed_1525_ = lean_ctor_get_uint8(v_a_1522_, sizeof(void*)*2);
lean_dec(v_a_1522_);
v___x_1526_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1524_, v___y_1510_);
v___x_1527_ = lean_box(v_closed_1525_);
lean_inc(v___y_1510_);
v___f_1528_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1528_, 0, v_values_1523_);
lean_closure_set(v___f_1528_, 1, v___x_1527_);
lean_closure_set(v___f_1528_, 2, v___y_1510_);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = 0;
v___x_1531_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1529_, v___x_1530_, v___x_1526_, v___f_1528_);
return v___x_1531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1532_, lean_object* v_x_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1532_, v_x_1533_);
lean_dec(v___y_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v___f_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1538_ = lean_st_ref_get(v___y_1536_);
lean_inc(v___y_1536_);
v___f_1539_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1539_, 0, v___y_1536_);
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = 0;
v___x_1544_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1542_, v___x_1543_, v___x_1541_, v___f_1539_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1545_);
lean_dec(v___y_1545_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1554_){
_start:
{
lean_object* v___f_1555_; lean_object* v___f_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___f_1555_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref_n(v_ch_1554_, 2);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1556_, 0, v___f_1555_);
lean_closure_set(v___f_1556_, 1, v_ch_1554_);
v___f_1557_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1558_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
v___x_1559_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1559_, 0, lean_box(0));
lean_closure_set(v___x_1559_, 1, lean_box(0));
lean_closure_set(v___x_1559_, 2, v_ch_1554_);
lean_closure_set(v___x_1559_, 3, v___f_1557_);
v___x_1560_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1560_, 0, lean_box(0));
lean_closure_set(v___x_1560_, 1, lean_box(0));
lean_closure_set(v___x_1560_, 2, v_ch_1554_);
lean_closure_set(v___x_1560_, 3, v___f_1558_);
v___x_1561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___f_1556_);
lean_ctor_set(v___x_1561_, 2, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1562_, lean_object* v_ch_1563_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1565_, lean_object* v_q_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1566_, v___y_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1570_, lean_object* v_q_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1570_, v_q_1571_, v___y_1572_);
lean_dec(v___y_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1576_, v_x_1577_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1581_, v_x_1582_, v_x_1583_, v___y_1584_);
lean_dec(v___y_1584_);
return v_res_1586_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Std_Queue_empty(lean_box(0));
return v___x_1587_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = 0;
v___x_1589_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1590_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*2, v___x_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1);
v___x_1593_ = l_Std_Mutex_new___redArg(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; lean_object* v_producers_1615_; lean_object* v_consumers_1616_; uint8_t v_closed_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1640_; 
v___x_1614_ = lean_st_ref_get(v___y_1612_);
v_producers_1615_ = lean_ctor_get(v___x_1614_, 0);
v_consumers_1616_ = lean_ctor_get(v___x_1614_, 1);
v_closed_1617_ = lean_ctor_get_uint8(v___x_1614_, sizeof(void*)*2);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1619_ = v___x_1614_;
v_isShared_1620_ = v_isSharedCheck_1640_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_consumers_1616_);
lean_inc(v_producers_1615_);
lean_dec(v___x_1614_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1640_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1616_);
if (lean_obj_tag(v___x_1621_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1638_; 
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1638_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_val_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1638_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v_fst_1626_; lean_object* v_snd_1627_; lean_object* v___x_1629_; 
v_fst_1626_ = lean_ctor_get(v_val_1622_, 0);
lean_inc(v_fst_1626_);
v_snd_1627_ = lean_ctor_get(v_val_1622_, 1);
lean_inc(v_snd_1627_);
lean_dec(v_val_1622_);
lean_inc(v_v_1611_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_v_1611_);
v___x_1629_ = v___x_1624_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_v_1611_);
v___x_1629_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
uint8_t v___x_1630_; lean_object* v___x_1632_; 
v___x_1630_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1626_, v___x_1629_);
lean_dec(v_fst_1626_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 1, v_snd_1627_);
v___x_1632_ = v___x_1619_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_producers_1615_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_snd_1627_);
lean_ctor_set_uint8(v_reuseFailAlloc_1636_, sizeof(void*)*2, v_closed_1617_);
v___x_1632_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_st_ref_set(v___y_1612_, v___x_1632_);
if (v___x_1630_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_1635_; 
lean_dec(v_v_1611_);
v___x_1635_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v___x_1639_; 
lean_dec(v___x_1621_);
lean_del_object(v___x_1619_);
lean_dec_ref(v_producers_1615_);
lean_dec(v_v_1611_);
v___x_1639_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1641_, v___y_1642_);
lean_dec(v___y_1642_);
return v_res_1644_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v_fst_1649_; 
v___x_1648_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1645_, v_a_1646_);
v_fst_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_fst_1649_);
lean_dec_ref(v___x_1648_);
if (lean_obj_tag(v_fst_1649_) == 0)
{
uint8_t v___x_1650_; 
v___x_1650_ = 1;
return v___x_1650_;
}
else
{
lean_object* v_val_1651_; uint8_t v___x_1652_; 
v_val_1651_ = lean_ctor_get(v_fst_1649_, 0);
lean_inc(v_val_1651_);
lean_dec_ref_known(v_fst_1649_, 1);
v___x_1652_ = lean_unbox(v_val_1651_);
lean_dec(v_val_1651_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
uint8_t v_res_1656_; lean_object* v_r_1657_; 
v_res_1656_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1653_, v_a_1654_);
lean_dec(v_a_1654_);
v_r_1657_ = lean_box(v_res_1656_);
return v_r_1657_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1658_, lean_object* v_v_1659_, lean_object* v_a_1660_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1659_, v_a_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_v_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1663_, v_v_1664_, v_a_1665_);
lean_dec(v_a_1665_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1669_, lean_object* v_v_1670_, lean_object* v_inst_1671_, lean_object* v_a_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1670_, v___y_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1676_, lean_object* v_v_1677_, lean_object* v_inst_1678_, lean_object* v_a_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1676_, v_v_1677_, v_inst_1678_, v_a_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v_a_1679_);
return v_res_1682_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; uint8_t v_closed_1687_; 
v___x_1686_ = lean_st_ref_get(v___y_1684_);
v_closed_1687_ = lean_ctor_get_uint8(v___x_1686_, sizeof(void*)*2);
lean_dec(v___x_1686_);
if (v_closed_1687_ == 0)
{
uint8_t v___x_1688_; 
v___x_1688_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1683_, v___y_1684_);
return v___x_1688_;
}
else
{
uint8_t v___x_1689_; 
lean_dec(v_v_1683_);
v___x_1689_ = 0;
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_res_1693_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1690_, v___y_1691_);
lean_dec(v___y_1691_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1695_, lean_object* v_v_1696_){
_start:
{
lean_object* v___f_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___f_1698_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1698_, 0, v_v_1696_);
v___x_1699_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1695_, v___f_1698_);
v___x_1700_ = lean_unbox(v___x_1699_);
lean_dec(v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1701_, lean_object* v_v_1702_, lean_object* v_a_1703_){
_start:
{
uint8_t v_res_1704_; lean_object* v_r_1705_; 
v_res_1704_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1701_, v_v_1702_);
v_r_1705_ = lean_box(v_res_1704_);
return v_r_1705_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1706_, lean_object* v_ch_1707_, lean_object* v_v_1708_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1707_, v_v_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1711_, lean_object* v_ch_1712_, lean_object* v_v_1713_, lean_object* v_a_1714_){
_start:
{
uint8_t v_res_1715_; lean_object* v_r_1716_; 
v_res_1715_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1711_, v_ch_1712_, v_v_1713_);
v_r_1716_ = lean_box(v_res_1715_);
return v_r_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
goto v___jp_1718_;
}
else
{
lean_object* v_val_1720_; uint8_t v___x_1721_; 
v_val_1720_ = lean_ctor_get(v_x_1717_, 0);
v___x_1721_ = lean_unbox(v_val_1720_);
if (v___x_1721_ == 0)
{
goto v___jp_1718_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1722_;
}
}
v___jp_1718_:
{
lean_object* v___x_1719_; 
v___x_1719_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1723_);
lean_dec(v_x_1723_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1725_, lean_object* v___f_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; uint8_t v_closed_1730_; 
v___x_1729_ = lean_st_ref_get(v___y_1727_);
v_closed_1730_ = lean_ctor_get_uint8(v___x_1729_, sizeof(void*)*2);
lean_dec(v___x_1729_);
if (v_closed_1730_ == 0)
{
uint8_t v___x_1731_; 
lean_inc(v_v_1725_);
v___x_1731_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1725_, v___y_1727_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_producers_1734_; lean_object* v_consumers_1735_; uint8_t v_closed_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1750_; 
v___x_1732_ = lean_io_promise_new();
v___x_1733_ = lean_st_ref_take(v___y_1727_);
v_producers_1734_ = lean_ctor_get(v___x_1733_, 0);
v_consumers_1735_ = lean_ctor_get(v___x_1733_, 1);
v_closed_1736_ = lean_ctor_get_uint8(v___x_1733_, sizeof(void*)*2);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1738_ = v___x_1733_;
v_isShared_1739_ = v_isSharedCheck_1750_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_consumers_1735_);
lean_inc(v_producers_1734_);
lean_dec(v___x_1733_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1750_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
lean_inc(v___x_1732_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v_v_1725_);
lean_ctor_set(v___x_1740_, 1, v___x_1732_);
v___x_1741_ = l_Std_Queue_enqueue___redArg(v___x_1740_, v_producers_1734_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1741_);
v___x_1743_ = v___x_1738_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_consumers_1735_);
lean_ctor_set_uint8(v_reuseFailAlloc_1749_, sizeof(void*)*2, v_closed_1736_);
v___x_1743_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1744_ = lean_st_ref_set(v___y_1727_, v___x_1743_);
v___x_1745_ = 1;
v___x_1746_ = lean_io_promise_result_opt(v___x_1732_);
lean_dec(v___x_1732_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_task_map(v___f_1726_, v___x_1746_, v___x_1747_, v___x_1745_);
return v___x_1748_;
}
}
}
else
{
lean_object* v___x_1751_; 
lean_dec_ref(v___f_1726_);
lean_dec(v_v_1725_);
v___x_1751_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1751_;
}
}
else
{
lean_object* v___x_1752_; 
lean_dec_ref(v___f_1726_);
lean_dec(v_v_1725_);
v___x_1752_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1753_, lean_object* v___f_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1753_, v___f_1754_, v___y_1755_);
lean_dec(v___y_1755_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1759_, lean_object* v_v_1760_){
_start:
{
lean_object* v___f_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; 
v___f_1762_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1763_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1763_, 0, v_v_1760_);
lean_closure_set(v___f_1763_, 1, v___f_1762_);
v___x_1764_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1759_, v___f_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1765_, lean_object* v_v_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1765_, v_v_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1769_, lean_object* v_ch_1770_, lean_object* v_v_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1770_, v_v_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_ch_1775_, lean_object* v_v_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1774_, v_ch_1775_, v_v_1776_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1779_, size_t v_sz_1780_, size_t v_i_1781_, lean_object* v_b_1782_){
_start:
{
uint8_t v___x_1784_; 
v___x_1784_ = lean_usize_dec_lt(v_i_1781_, v_sz_1780_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_b_1782_);
return v___x_1785_;
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; size_t v___x_1790_; size_t v___x_1791_; 
v_a_1786_ = lean_array_uget_borrowed(v_as_1779_, v_i_1781_);
v___x_1787_ = lean_box(0);
v___x_1788_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1786_, v___x_1787_);
v___x_1789_ = lean_box(0);
v___x_1790_ = ((size_t)1ULL);
v___x_1791_ = lean_usize_add(v_i_1781_, v___x_1790_);
v_i_1781_ = v___x_1791_;
v_b_1782_ = v___x_1789_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1793_, lean_object* v_sz_1794_, lean_object* v_i_1795_, lean_object* v_b_1796_, lean_object* v___y_1797_){
_start:
{
size_t v_sz_boxed_1798_; size_t v_i_boxed_1799_; lean_object* v_res_1800_; 
v_sz_boxed_1798_ = lean_unbox_usize(v_sz_1794_);
lean_dec(v_sz_1794_);
v_i_boxed_1799_ = lean_unbox_usize(v_i_1795_);
lean_dec(v_i_1795_);
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1793_, v_sz_boxed_1798_, v_i_boxed_1799_, v_b_1796_);
lean_dec_ref(v_as_1793_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; uint8_t v_closed_1804_; 
v___x_1803_ = lean_st_ref_get(v___y_1801_);
v_closed_1804_ = lean_ctor_get_uint8(v___x_1803_, sizeof(void*)*2);
if (v_closed_1804_ == 0)
{
lean_object* v_producers_1805_; lean_object* v_consumers_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1829_; 
v_producers_1805_ = lean_ctor_get(v___x_1803_, 0);
v_consumers_1806_ = lean_ctor_get(v___x_1803_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1808_ = v___x_1803_;
v_isShared_1809_ = v_isSharedCheck_1829_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_consumers_1806_);
lean_inc(v_producers_1805_);
lean_dec(v___x_1803_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1829_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; size_t v_sz_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1810_ = l_Std_Queue_toArray___redArg(v_consumers_1806_);
v___x_1811_ = lean_box(0);
v_sz_1812_ = lean_array_size(v___x_1810_);
v___x_1813_ = ((size_t)0ULL);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1810_, v_sz_1812_, v___x_1813_, v___x_1811_);
lean_dec_ref(v___x_1810_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1827_; 
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v___x_1814_, 0);
lean_dec(v_unused_1828_);
v___x_1816_ = v___x_1814_;
v_isShared_1817_ = v_isSharedCheck_1827_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v___x_1814_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1827_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
v___x_1819_ = 1;
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 1, v___x_1818_);
v___x_1821_ = v___x_1808_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_producers_1805_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1818_);
v___x_1821_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*2, v___x_1819_);
v___x_1822_ = lean_st_ref_set(v___y_1801_, v___x_1821_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1811_);
v___x_1824_ = v___x_1816_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1811_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_del_object(v___x_1808_);
lean_dec_ref(v_producers_1805_);
return v___x_1814_;
}
}
}
else
{
uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v___x_1803_);
v___x_1830_ = 1;
v___x_1831_ = lean_box(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1833_);
lean_dec(v___y_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1837_){
_start:
{
lean_object* v___f_1839_; lean_object* v___x_1840_; 
v___f_1839_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1840_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1837_, v___f_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1844_, lean_object* v_ch_1845_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1845_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_ch_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1848_, v_ch_1849_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1852_, lean_object* v_as_1853_, size_t v_sz_1854_, size_t v_i_1855_, lean_object* v_b_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1853_, v_sz_1854_, v_i_1855_, v_b_1856_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1860_, lean_object* v_as_1861_, lean_object* v_sz_1862_, lean_object* v_i_1863_, lean_object* v_b_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
size_t v_sz_boxed_1867_; size_t v_i_boxed_1868_; lean_object* v_res_1869_; 
v_sz_boxed_1867_ = lean_unbox_usize(v_sz_1862_);
lean_dec(v_sz_1862_);
v_i_boxed_1868_ = lean_unbox_usize(v_i_1863_);
lean_dec(v_i_1863_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1860_, v_as_1861_, v_sz_boxed_1867_, v_i_boxed_1868_, v_b_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v_as_1861_);
return v_res_1869_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; uint8_t v_closed_1873_; 
v___x_1872_ = lean_st_ref_get(v___y_1870_);
v_closed_1873_ = lean_ctor_get_uint8(v___x_1872_, sizeof(void*)*2);
lean_dec(v___x_1872_);
return v_closed_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
uint8_t v_res_1876_; lean_object* v_r_1877_; 
v_res_1876_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1874_);
lean_dec(v___y_1874_);
v_r_1877_ = lean_box(v_res_1876_);
return v_r_1877_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1879_){
_start:
{
lean_object* v___f_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___f_1881_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1882_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1879_, v___f_1881_);
v___x_1883_ = lean_unbox(v___x_1882_);
lean_dec(v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1884_, lean_object* v_a_1885_){
_start:
{
uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_res_1886_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1884_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1888_, lean_object* v_ch_1889_){
_start:
{
uint8_t v___x_1891_; 
v___x_1891_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_ch_1893_, lean_object* v_a_1894_){
_start:
{
uint8_t v_res_1895_; lean_object* v_r_1896_; 
v_res_1895_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1892_, v_ch_1893_);
v_r_1896_ = lean_box(v_res_1895_);
return v_r_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1897_, lean_object* v_inst_1898_, lean_object* v_toBind_1899_, lean_object* v___f_1900_, lean_object* v_a_1901_){
_start:
{
uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1902_ = 1;
v___x_1903_ = lean_box(v___x_1902_);
v___x_1904_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1904_, 0, lean_box(0));
lean_closure_set(v___x_1904_, 1, v___x_1903_);
lean_closure_set(v___x_1904_, 2, v_snd_1897_);
v___x_1905_ = lean_apply_2(v_inst_1898_, lean_box(0), v___x_1904_);
v___x_1906_ = lean_apply_4(v_toBind_1899_, lean_box(0), lean_box(0), v___x_1905_, v___f_1900_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1907_, lean_object* v_inst_1908_, lean_object* v_toBind_1909_, lean_object* v_a_1910_, lean_object* v_inst_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_producers_1913_; lean_object* v_consumers_1914_; uint8_t v_closed_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1936_; 
v_producers_1913_ = lean_ctor_get(v_a_1912_, 0);
v_consumers_1914_ = lean_ctor_get(v_a_1912_, 1);
v_closed_1915_ = lean_ctor_get_uint8(v_a_1912_, sizeof(void*)*2);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_a_1912_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1917_ = v_a_1912_;
v_isShared_1918_ = v_isSharedCheck_1936_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_consumers_1914_);
lean_inc(v_producers_1913_);
lean_dec(v_a_1912_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1936_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1913_);
if (lean_obj_tag(v___x_1919_) == 1)
{
lean_object* v_val_1920_; lean_object* v_fst_1921_; lean_object* v_snd_1922_; lean_object* v_fst_1923_; lean_object* v_snd_1924_; lean_object* v___f_1925_; lean_object* v___f_1926_; lean_object* v___x_1928_; 
v_val_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_val_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v_fst_1921_ = lean_ctor_get(v_val_1920_, 0);
lean_inc(v_fst_1921_);
v_snd_1922_ = lean_ctor_get(v_val_1920_, 1);
lean_inc(v_snd_1922_);
lean_dec(v_val_1920_);
v_fst_1923_ = lean_ctor_get(v_fst_1921_, 0);
lean_inc(v_fst_1923_);
v_snd_1924_ = lean_ctor_get(v_fst_1921_, 1);
lean_inc(v_snd_1924_);
lean_dec(v_fst_1921_);
v___f_1925_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1925_, 0, v_toApplicative_1907_);
lean_closure_set(v___f_1925_, 1, v_fst_1923_);
lean_inc(v_toBind_1909_);
v___f_1926_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1926_, 0, v_snd_1924_);
lean_closure_set(v___f_1926_, 1, v_inst_1908_);
lean_closure_set(v___f_1926_, 2, v_toBind_1909_);
lean_closure_set(v___f_1926_, 3, v___f_1925_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v_snd_1922_);
v___x_1928_ = v___x_1917_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_snd_1922_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_consumers_1914_);
lean_ctor_set_uint8(v_reuseFailAlloc_1932_, sizeof(void*)*2, v_closed_1915_);
v___x_1928_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_inc(v_a_1910_);
v___x_1929_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1929_, 0, lean_box(0));
lean_closure_set(v___x_1929_, 1, lean_box(0));
lean_closure_set(v___x_1929_, 2, v_a_1910_);
lean_closure_set(v___x_1929_, 3, v___x_1928_);
v___x_1930_ = lean_apply_2(v_inst_1911_, lean_box(0), v___x_1929_);
v___x_1931_ = lean_apply_4(v_toBind_1909_, lean_box(0), lean_box(0), v___x_1930_, v___f_1926_);
return v___x_1931_;
}
}
else
{
lean_object* v_toPure_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_dec(v___x_1919_);
lean_del_object(v___x_1917_);
lean_dec_ref(v_consumers_1914_);
lean_dec(v_inst_1911_);
lean_dec(v_toBind_1909_);
lean_dec(v_inst_1908_);
v_toPure_1933_ = lean_ctor_get(v_toApplicative_1907_, 1);
lean_inc(v_toPure_1933_);
lean_dec_ref(v_toApplicative_1907_);
v___x_1934_ = lean_box(0);
v___x_1935_ = lean_apply_2(v_toPure_1933_, lean_box(0), v___x_1934_);
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_1937_, lean_object* v_inst_1938_, lean_object* v_toBind_1939_, lean_object* v_a_1940_, lean_object* v_inst_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(v_toApplicative_1937_, v_inst_1938_, v_toBind_1939_, v_a_1940_, v_inst_1941_, v_a_1942_);
lean_dec(v_a_1940_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_, lean_object* v_a_1947_){
_start:
{
lean_object* v_toApplicative_1948_; lean_object* v_toBind_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_toApplicative_1948_ = lean_ctor_get(v_inst_1944_, 0);
lean_inc_ref(v_toApplicative_1948_);
v_toBind_1949_ = lean_ctor_get(v_inst_1944_, 1);
lean_inc_n(v_toBind_1949_, 2);
lean_dec_ref(v_inst_1944_);
lean_inc(v_inst_1945_);
lean_inc_n(v_a_1947_, 2);
v___f_1950_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1950_, 0, v_toApplicative_1948_);
lean_closure_set(v___f_1950_, 1, v_inst_1946_);
lean_closure_set(v___f_1950_, 2, v_toBind_1949_);
lean_closure_set(v___f_1950_, 3, v_a_1947_);
lean_closure_set(v___f_1950_, 4, v_inst_1945_);
v___x_1951_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1951_, 0, lean_box(0));
lean_closure_set(v___x_1951_, 1, lean_box(0));
lean_closure_set(v___x_1951_, 2, v_a_1947_);
v___x_1952_ = lean_apply_2(v_inst_1945_, lean_box(0), v___x_1951_);
v___x_1953_ = lean_apply_4(v_toBind_1949_, lean_box(0), lean_box(0), v___x_1952_, v___f_1950_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1954_, v_inst_1955_, v_inst_1956_, v_a_1957_);
lean_dec(v_a_1957_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_1959_, lean_object* v_00_u03b1_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1961_, v_inst_1962_, v_inst_1963_, v_a_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object* v_m_1966_, lean_object* v_00_u03b1_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(v_m_1966_, v_00_u03b1_1967_, v_inst_1968_, v_inst_1969_, v_inst_1970_, v_a_1971_);
lean_dec(v_a_1971_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1975_; lean_object* v_producers_1976_; lean_object* v_consumers_1977_; uint8_t v_closed_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2003_; 
v___x_1975_ = lean_st_ref_get(v_a_1973_);
v_producers_1976_ = lean_ctor_get(v___x_1975_, 0);
v_consumers_1977_ = lean_ctor_get(v___x_1975_, 1);
v_closed_1978_ = lean_ctor_get_uint8(v___x_1975_, sizeof(void*)*2);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1980_ = v___x_1975_;
v_isShared_1981_ = v_isSharedCheck_2003_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_consumers_1977_);
lean_inc(v_producers_1976_);
lean_dec(v___x_1975_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2003_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1976_);
if (lean_obj_tag(v___x_1982_) == 1)
{
lean_object* v_val_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2001_; 
v_val_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2001_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_val_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2001_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v_fst_1989_; lean_object* v_snd_1990_; lean_object* v___x_1992_; 
v_fst_1987_ = lean_ctor_get(v_val_1983_, 0);
lean_inc(v_fst_1987_);
v_snd_1988_ = lean_ctor_get(v_val_1983_, 1);
lean_inc(v_snd_1988_);
lean_dec(v_val_1983_);
v_fst_1989_ = lean_ctor_get(v_fst_1987_, 0);
lean_inc(v_fst_1989_);
v_snd_1990_ = lean_ctor_get(v_fst_1987_, 1);
lean_inc(v_snd_1990_);
lean_dec(v_fst_1987_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v_snd_1988_);
v___x_1992_ = v___x_1980_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_snd_1988_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_consumers_1977_);
lean_ctor_set_uint8(v_reuseFailAlloc_2000_, sizeof(void*)*2, v_closed_1978_);
v___x_1992_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1993_ = lean_st_ref_set(v_a_1973_, v___x_1992_);
v___x_1994_ = 1;
v___x_1995_ = lean_box(v___x_1994_);
v___x_1996_ = lean_io_promise_resolve(v___x_1995_, v_snd_1990_);
lean_dec(v_snd_1990_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v_fst_1989_);
v___x_1998_ = v___x_1985_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_fst_1989_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v___x_1982_);
lean_del_object(v___x_1980_);
lean_dec_ref(v_consumers_1977_);
v___x_2002_ = lean_box(0);
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2004_);
lean_dec(v_a_2004_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_2011_, lean_object* v_a_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_2011_, v_a_2012_);
lean_dec(v_a_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_2016_){
_start:
{
lean_object* v___f_2018_; lean_object* v___x_2019_; 
v___f_2018_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_2019_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2016_, v___f_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_2023_, lean_object* v_ch_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2024_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_2027_, lean_object* v_ch_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_2027_, v_ch_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_st_ref_get(v___y_2032_);
v___x_2035_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_2032_);
if (lean_obj_tag(v___x_2035_) == 1)
{
lean_object* v___x_2036_; 
lean_dec(v___x_2034_);
lean_dec_ref(v___f_2031_);
v___x_2036_ = lean_task_pure(v___x_2035_);
return v___x_2036_;
}
else
{
lean_object* v_producers_2037_; lean_object* v_consumers_2038_; uint8_t v_closed_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v___x_2035_);
v_producers_2037_ = lean_ctor_get(v___x_2034_, 0);
v_consumers_2038_ = lean_ctor_get(v___x_2034_, 1);
v_closed_2039_ = lean_ctor_get_uint8(v___x_2034_, sizeof(void*)*2);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2041_ = v___x_2034_;
v_isShared_2042_ = v_isSharedCheck_2055_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_consumers_2038_);
lean_inc(v_producers_2037_);
lean_dec(v___x_2034_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2055_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
uint8_t v___x_2043_; 
v___x_2043_ = lean_bool_not(v_closed_2039_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; 
lean_del_object(v___x_2041_);
lean_dec_ref(v_consumers_2038_);
lean_dec_ref(v_producers_2037_);
lean_dec_ref(v___f_2031_);
v___x_2044_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2045_ = lean_io_promise_new();
lean_inc(v___x_2045_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
v___x_2047_ = l_Std_Queue_enqueue___redArg(v___x_2046_, v_consumers_2038_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 1, v___x_2047_);
v___x_2049_ = v___x_2041_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_producers_2037_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*2, v_closed_2039_);
v___x_2049_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2050_ = lean_st_ref_set(v___y_2032_, v___x_2049_);
v___x_2051_ = lean_io_promise_result_opt(v___x_2045_);
lean_dec(v___x_2045_);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_task_map(v___f_2031_, v___x_2051_, v___x_2052_, v___x_2043_);
return v___x_2053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2056_, v___y_2057_);
lean_dec(v___y_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2062_){
_start:
{
lean_object* v___f_2064_; lean_object* v___x_2065_; 
v___f_2064_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2065_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2062_, v___f_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2066_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2069_, lean_object* v_ch_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2070_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2073_, lean_object* v_ch_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2073_, v_ch_2074_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2077_, lean_object* v_a_2078_){
_start:
{
uint8_t v___y_2080_; lean_object* v_producers_2084_; uint8_t v_closed_2085_; uint8_t v___x_2086_; uint8_t v___x_2087_; 
v_producers_2084_ = lean_ctor_get(v_a_2078_, 0);
v_closed_2085_ = lean_ctor_get_uint8(v_a_2078_, sizeof(void*)*2);
v___x_2086_ = l_Std_Queue_isEmpty___redArg(v_producers_2084_);
v___x_2087_ = lean_bool_not(v___x_2086_);
if (v___x_2087_ == 0)
{
v___y_2080_ = v_closed_2085_;
goto v___jp_2079_;
}
else
{
v___y_2080_ = v___x_2087_;
goto v___jp_2079_;
}
v___jp_2079_:
{
lean_object* v_toPure_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_toPure_2081_ = lean_ctor_get(v_toApplicative_2077_, 1);
lean_inc(v_toPure_2081_);
lean_dec_ref(v_toApplicative_2077_);
v___x_2082_ = lean_box(v___y_2080_);
v___x_2083_ = lean_apply_2(v_toPure_2081_, lean_box(0), v___x_2082_);
return v___x_2083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2088_, v_a_2089_);
lean_dec_ref(v_a_2089_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_toApplicative_2094_; lean_object* v_toBind_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_toApplicative_2094_ = lean_ctor_get(v_inst_2091_, 0);
lean_inc_ref(v_toApplicative_2094_);
v_toBind_2095_ = lean_ctor_get(v_inst_2091_, 1);
lean_inc(v_toBind_2095_);
lean_dec_ref(v_inst_2091_);
v___f_2096_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2096_, 0, v_toApplicative_2094_);
lean_inc(v_a_2093_);
v___x_2097_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2097_, 0, lean_box(0));
lean_closure_set(v___x_2097_, 1, lean_box(0));
lean_closure_set(v___x_2097_, 2, v_a_2093_);
v___x_2098_ = lean_apply_2(v_inst_2092_, lean_box(0), v___x_2097_);
v___x_2099_ = lean_apply_4(v_toBind_2095_, lean_box(0), lean_box(0), v___x_2098_, v___f_2096_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(v_inst_2100_, v_inst_2101_, v_a_2102_);
lean_dec(v_a_2102_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2104_, lean_object* v_00_u03b1_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_toApplicative_2109_; lean_object* v_toBind_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_toApplicative_2109_ = lean_ctor_get(v_inst_2106_, 0);
lean_inc_ref(v_toApplicative_2109_);
v_toBind_2110_ = lean_ctor_get(v_inst_2106_, 1);
lean_inc(v_toBind_2110_);
lean_dec_ref(v_inst_2106_);
v___f_2111_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2111_, 0, v_toApplicative_2109_);
lean_inc(v_a_2108_);
v___x_2112_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2112_, 0, lean_box(0));
lean_closure_set(v___x_2112_, 1, lean_box(0));
lean_closure_set(v___x_2112_, 2, v_a_2108_);
v___x_2113_ = lean_apply_2(v_inst_2107_, lean_box(0), v___x_2112_);
v___x_2114_ = lean_apply_4(v_toBind_2110_, lean_box(0), lean_box(0), v___x_2113_, v___f_2111_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object* v_m_2115_, lean_object* v_00_u03b1_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(v_m_2115_, v_00_u03b1_2116_, v_inst_2117_, v_inst_2118_, v_a_2119_);
lean_dec(v_a_2119_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2121_, lean_object* v___f_2122_, lean_object* v_x_2123_){
_start:
{
if (lean_obj_tag(v_x_2123_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v___f_2122_);
v_a_2125_ = lean_ctor_get(v_x_2123_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_x_2123_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2127_ = v_x_2123_;
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v_x_2123_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
}
else
{
lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2147_; 
v_isSharedCheck_2147_ = !lean_is_exclusive(v_x_2123_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v_x_2123_, 0);
lean_dec(v_unused_2148_);
v___x_2135_ = v_x_2123_;
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
else
{
lean_dec(v_x_2123_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2147_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2137_ = 1;
v___x_2138_ = lean_box(v___x_2137_);
v___x_2139_ = lean_io_promise_resolve(v___x_2138_, v_snd_2121_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2139_);
v___x_2141_ = v___x_2135_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = 0;
v___x_2145_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2143_, v___x_2144_, v___x_2142_, v___f_2122_);
return v___x_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2149_, lean_object* v___f_2150_, lean_object* v_x_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2149_, v___f_2150_, v_x_2151_);
lean_dec(v_snd_2149_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2154_, lean_object* v_x_2155_){
_start:
{
if (lean_obj_tag(v_x_2155_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2165_; 
v_a_2157_ = lean_ctor_get(v_x_2155_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_x_2155_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2159_ = v_x_2155_;
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v_x_2155_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2203_; 
v_a_2166_ = lean_ctor_get(v_x_2155_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2155_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2168_ = v_x_2155_;
v_isShared_2169_ = v_isSharedCheck_2203_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v_x_2155_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2203_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_producers_2170_; lean_object* v_consumers_2171_; uint8_t v_closed_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2202_; 
v_producers_2170_ = lean_ctor_get(v_a_2166_, 0);
v_consumers_2171_ = lean_ctor_get(v_a_2166_, 1);
v_closed_2172_ = lean_ctor_get_uint8(v_a_2166_, sizeof(void*)*2);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_a_2166_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2174_ = v_a_2166_;
v_isShared_2175_ = v_isSharedCheck_2202_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_consumers_2171_);
lean_inc(v_producers_2170_);
lean_dec(v_a_2166_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2202_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2170_);
if (lean_obj_tag(v___x_2176_) == 1)
{
lean_object* v_val_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2200_; 
v_val_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2200_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_val_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2200_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_fst_2181_; lean_object* v_snd_2182_; lean_object* v_fst_2183_; lean_object* v_snd_2184_; lean_object* v___x_2186_; 
v_fst_2181_ = lean_ctor_get(v_val_2177_, 0);
lean_inc(v_fst_2181_);
v_snd_2182_ = lean_ctor_get(v_val_2177_, 1);
lean_inc(v_snd_2182_);
lean_dec(v_val_2177_);
v_fst_2183_ = lean_ctor_get(v_fst_2181_, 0);
lean_inc(v_fst_2183_);
v_snd_2184_ = lean_ctor_get(v_fst_2181_, 1);
lean_inc(v_snd_2184_);
lean_dec(v_fst_2181_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v_snd_2182_);
v___x_2186_ = v___x_2174_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_snd_2182_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_consumers_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*2, v_closed_2172_);
v___x_2186_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; lean_object* v___f_2188_; lean_object* v___f_2189_; lean_object* v___x_2191_; 
v___x_2187_ = lean_st_ref_set(v_a_2154_, v___x_2186_);
v___f_2188_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2188_, 0, v_fst_2183_);
v___f_2189_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2189_, 0, v_snd_2184_);
lean_closure_set(v___f_2189_, 1, v___f_2188_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2187_);
v___x_2191_ = v___x_2168_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2187_);
v___x_2191_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set_tag(v___x_2179_, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2191_);
v___x_2193_ = v___x_2179_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; uint8_t v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = 0;
v___x_2196_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2194_, v___x_2195_, v___x_2193_, v___f_2189_);
return v___x_2196_;
}
}
}
}
}
else
{
lean_object* v___x_2201_; 
lean_dec(v___x_2176_);
lean_del_object(v___x_2174_);
lean_dec_ref(v_consumers_2171_);
lean_del_object(v___x_2168_);
v___x_2201_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2204_, lean_object* v_x_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2204_, v_x_2205_);
lean_dec(v_a_2204_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2208_){
_start:
{
lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; 
v___x_2210_ = lean_st_ref_get(v_a_2208_);
lean_inc(v_a_2208_);
v___f_2211_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2211_, 0, v_a_2208_);
v___x_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = 0;
v___x_2216_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2214_, v___x_2215_, v___x_2213_, v___f_2211_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2217_);
lean_dec(v_a_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2224_, lean_object* v_a_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2224_, v_a_2225_);
lean_dec(v_a_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2228_, lean_object* v___y_2229_, lean_object* v___f_2230_, lean_object* v_x_2231_){
_start:
{
if (lean_obj_tag(v_x_2231_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref(v___f_2230_);
lean_dec_ref(v_lose_2228_);
v_a_2233_ = lean_ctor_get(v_x_2231_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_x_2231_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2235_ = v_x_2231_;
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v_x_2231_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
}
}
else
{
lean_object* v_a_2242_; uint8_t v___x_2243_; 
v_a_2242_ = lean_ctor_get(v_x_2231_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v_x_2231_, 1);
v___x_2243_ = lean_unbox(v_a_2242_);
lean_dec(v_a_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; 
lean_dec_ref(v___f_2230_);
lean_inc(v___y_2229_);
v___x_2244_ = lean_apply_2(v_lose_2228_, v___y_2229_, lean_box(0));
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; 
lean_dec_ref(v_lose_2228_);
v___x_2245_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2229_);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = 0;
v___x_2248_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2246_, v___x_2247_, v___x_2245_, v___f_2230_);
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2249_, lean_object* v___y_2250_, lean_object* v___f_2251_, lean_object* v_x_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2249_, v___y_2250_, v___f_2251_, v_x_2252_);
lean_dec(v___y_2250_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2255_, lean_object* v_lose_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_finished_2259_; lean_object* v_promise_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; uint8_t v___y_2265_; uint8_t v___x_2275_; 
v_finished_2259_ = lean_ctor_get(v_w_2255_, 0);
lean_inc(v_finished_2259_);
v_promise_2260_ = lean_ctor_get(v_w_2255_, 1);
lean_inc(v_promise_2260_);
lean_dec_ref(v_w_2255_);
v___x_2261_ = lean_st_ref_take(v_finished_2259_);
v___f_2262_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2262_, 0, v_promise_2260_);
lean_inc(v___y_2257_);
v___f_2263_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2263_, 0, v_lose_2256_);
lean_closure_set(v___f_2263_, 1, v___y_2257_);
lean_closure_set(v___f_2263_, 2, v___f_2262_);
v___x_2275_ = lean_unbox(v___x_2261_);
lean_dec(v___x_2261_);
if (v___x_2275_ == 0)
{
uint8_t v___x_2276_; 
v___x_2276_ = 1;
v___y_2265_ = v___x_2276_;
goto v___jp_2264_;
}
else
{
uint8_t v___x_2277_; 
v___x_2277_ = 0;
v___y_2265_ = v___x_2277_;
goto v___jp_2264_;
}
v___jp_2264_:
{
uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; 
v___x_2266_ = 1;
v___x_2267_ = lean_box(v___x_2266_);
v___x_2268_ = lean_st_ref_set(v_finished_2259_, v___x_2267_);
lean_dec(v_finished_2259_);
v___x_2269_ = lean_box(v___y_2265_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = 0;
v___x_2274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2272_, v___x_2273_, v___x_2271_, v___f_2263_);
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2278_, lean_object* v_lose_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2278_, v_lose_2279_, v___y_2280_);
lean_dec(v___y_2280_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2283_, lean_object* v_w_2284_, lean_object* v_lose_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2284_, v_lose_2285_, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2289_, lean_object* v_w_2290_, lean_object* v_lose_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2289_, v_w_2290_, v_lose_2291_, v___y_2292_);
lean_dec(v___y_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2295_){
_start:
{
uint8_t v___y_2298_; 
if (lean_obj_tag(v_x_2295_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2310_; 
v_a_2302_ = lean_ctor_get(v_x_2295_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_x_2295_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2304_ = v_x_2295_;
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v_x_2295_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2310_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
return v___x_2308_;
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v_producers_2312_; uint8_t v_closed_2313_; uint8_t v___x_2314_; uint8_t v___x_2315_; 
v_a_2311_ = lean_ctor_get(v_x_2295_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v_x_2295_, 1);
v_producers_2312_ = lean_ctor_get(v_a_2311_, 0);
lean_inc_ref(v_producers_2312_);
v_closed_2313_ = lean_ctor_get_uint8(v_a_2311_, sizeof(void*)*2);
lean_dec(v_a_2311_);
v___x_2314_ = l_Std_Queue_isEmpty___redArg(v_producers_2312_);
lean_dec_ref(v_producers_2312_);
v___x_2315_ = lean_bool_not(v___x_2314_);
if (v___x_2315_ == 0)
{
v___y_2298_ = v_closed_2313_;
goto v___jp_2297_;
}
else
{
v___y_2298_ = v___x_2315_;
goto v___jp_2297_;
}
}
v___jp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_box(v___y_2298_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2316_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2319_, lean_object* v_waiter_2320_, lean_object* v_x_2321_){
_start:
{
if (lean_obj_tag(v_x_2321_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_waiter_2320_);
v_a_2323_ = lean_ctor_get(v_x_2321_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_x_2321_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2325_ = v_x_2321_;
v_isShared_2326_ = v_isSharedCheck_2331_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v_x_2321_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2331_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
}
}
else
{
lean_object* v_a_2332_; uint8_t v___x_2333_; 
v_a_2332_ = lean_ctor_get(v_x_2321_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v_x_2321_, 1);
v___x_2333_ = lean_unbox(v_a_2332_);
lean_dec(v_a_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; lean_object* v_producers_2335_; lean_object* v_consumers_2336_; uint8_t v_closed_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2348_; 
v___x_2334_ = lean_st_ref_take(v___y_2319_);
v_producers_2335_ = lean_ctor_get(v___x_2334_, 0);
v_consumers_2336_ = lean_ctor_get(v___x_2334_, 1);
v_closed_2337_ = lean_ctor_get_uint8(v___x_2334_, sizeof(void*)*2);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2339_ = v___x_2334_;
v_isShared_2340_ = v_isSharedCheck_2348_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_consumers_2336_);
lean_inc(v_producers_2335_);
lean_dec(v___x_2334_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2348_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_waiter_2320_);
v___x_2342_ = l_Std_Queue_enqueue___redArg(v___x_2341_, v_consumers_2336_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 1, v___x_2342_);
v___x_2344_ = v___x_2339_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_producers_2335_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_2342_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*2, v_closed_2337_);
v___x_2344_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_st_ref_set(v___y_2319_, v___x_2344_);
v___x_2346_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_2346_;
}
}
}
else
{
lean_object* v_lose_2349_; lean_object* v___x_2350_; 
v_lose_2349_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_2350_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2320_, v_lose_2349_, v___y_2319_);
return v___x_2350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2351_, lean_object* v_waiter_2352_, lean_object* v_x_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2351_, v_waiter_2352_, v_x_2353_);
lean_dec(v___y_2351_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v___f_2356_, lean_object* v_waiter_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; 
v___x_2360_ = lean_st_ref_get(v___y_2358_);
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = 0;
v___x_2365_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2363_, v___x_2364_, v___x_2362_, v___f_2356_);
lean_inc(v___y_2358_);
v___f_2366_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2366_, 0, v___y_2358_);
lean_closure_set(v___f_2366_, 1, v_waiter_2357_);
v___x_2367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2363_, v___x_2364_, v___x_2365_, v___f_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v___f_2368_, lean_object* v_waiter_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v___f_2368_, v_waiter_2369_, v___y_2370_);
lean_dec(v___y_2370_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2373_, lean_object* v_ch_2374_, lean_object* v_waiter_2375_){
_start:
{
lean_object* v___f_2377_; lean_object* v___x_2378_; 
v___f_2377_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2377_, 0, v___f_2373_);
lean_closure_set(v___f_2377_, 1, v_waiter_2375_);
v___x_2378_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2374_, v___f_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2379_, lean_object* v_ch_2380_, lean_object* v_waiter_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2379_, v_ch_2380_, v_waiter_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2384_, lean_object* v___f_2385_, lean_object* v_x_2386_){
_start:
{
if (lean_obj_tag(v_x_2386_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___f_2385_);
v_a_2388_ = lean_ctor_get(v_x_2386_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_x_2386_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2390_ = v_x_2386_;
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v_x_2386_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
}
else
{
lean_object* v_a_2397_; uint8_t v___x_2398_; 
v_a_2397_ = lean_ctor_get(v_x_2386_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v_x_2386_, 1);
v___x_2398_ = lean_unbox(v_a_2397_);
lean_dec(v_a_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_dec_ref(v___f_2385_);
v___x_2399_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2399_;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; 
v___x_2400_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2384_);
v___x_2401_ = lean_unsigned_to_nat(0u);
v___x_2402_ = 0;
v___x_2403_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2401_, v___x_2402_, v___x_2400_, v___f_2385_);
return v___x_2403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2404_, lean_object* v___f_2405_, lean_object* v_x_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2404_, v___f_2405_, v_x_2406_);
lean_dec(v___y_2404_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2409_, lean_object* v___f_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___f_2419_; lean_object* v___x_2420_; 
v___x_2413_ = lean_st_ref_get(v___y_2411_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
v___x_2416_ = lean_unsigned_to_nat(0u);
v___x_2417_ = 0;
v___x_2418_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2416_, v___x_2417_, v___x_2415_, v___f_2409_);
lean_inc(v___y_2411_);
v___f_2419_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2419_, 0, v___y_2411_);
lean_closure_set(v___f_2419_, 1, v___f_2410_);
v___x_2420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2416_, v___x_2417_, v___x_2418_, v___f_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2421_, lean_object* v___f_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2421_, v___f_2422_, v___y_2423_);
lean_dec(v___y_2423_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2426_, uint8_t v_closed_2427_, lean_object* v___y_2428_, lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref(v_producers_2426_);
v_a_2431_ = lean_ctor_get(v_x_2429_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_x_2429_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2433_ = v_x_2429_;
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v_x_2429_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2450_; 
v_a_2440_ = lean_ctor_get(v_x_2429_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_x_2429_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2442_ = v_x_2429_;
v_isShared_2443_ = v_isSharedCheck_2450_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v_x_2429_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2450_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2444_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2444_, 0, v_producers_2426_);
lean_ctor_set(v___x_2444_, 1, v_a_2440_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*2, v_closed_2427_);
v___x_2445_ = lean_st_ref_set(v___y_2428_, v___x_2444_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2445_);
v___x_2447_ = v___x_2442_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; 
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2451_, lean_object* v_closed_2452_, lean_object* v___y_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_){
_start:
{
uint8_t v_closed_boxed_2456_; lean_object* v_res_2457_; 
v_closed_boxed_2456_ = lean_unbox(v_closed_2452_);
v_res_2457_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2451_, v_closed_boxed_2456_, v___y_2453_, v_x_2454_);
lean_dec(v___y_2453_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2458_, lean_object* v_x_2459_, lean_object* v_head_2460_, lean_object* v_x_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2458_, v_x_2459_, v_head_2460_, v_x_2461_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2464_, lean_object* v_x_2465_){
_start:
{
if (lean_obj_tag(v_x_2464_) == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_x_2465_);
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
return v___x_2468_;
}
else
{
lean_object* v_head_2469_; lean_object* v_tail_2470_; lean_object* v___f_2471_; lean_object* v_val_2473_; 
v_head_2469_ = lean_ctor_get(v_x_2464_, 0);
lean_inc_n(v_head_2469_, 2);
v_tail_2470_ = lean_ctor_get(v_x_2464_, 1);
lean_inc(v_tail_2470_);
lean_dec_ref_known(v_x_2464_, 2);
v___f_2471_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2471_, 0, v_tail_2470_);
lean_closure_set(v___f_2471_, 1, v_x_2465_);
lean_closure_set(v___f_2471_, 2, v_head_2469_);
if (lean_obj_tag(v_head_2469_) == 0)
{
lean_object* v___x_2477_; 
lean_dec_ref_known(v_head_2469_, 1);
v___x_2477_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_2473_ = v___x_2477_;
goto v___jp_2472_;
}
else
{
lean_object* v_finished_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2492_; 
v_finished_2478_ = lean_ctor_get(v_head_2469_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_head_2469_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2480_ = v_head_2469_;
v_isShared_2481_ = v_isSharedCheck_2492_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_finished_2478_);
lean_dec(v_head_2469_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2492_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_finished_2482_; lean_object* v___x_2483_; lean_object* v___f_2484_; lean_object* v___x_2486_; 
v_finished_2482_ = lean_ctor_get(v_finished_2478_, 0);
lean_inc(v_finished_2482_);
lean_dec_ref(v_finished_2478_);
v___x_2483_ = lean_st_ref_get(v_finished_2482_);
lean_dec(v_finished_2482_);
v___f_2484_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2483_);
v___x_2486_ = v___x_2480_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2483_);
v___x_2486_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = 0;
v___x_2490_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2488_, v___x_2489_, v___x_2487_, v___f_2484_);
v_val_2473_ = v___x_2490_;
goto v___jp_2472_;
}
}
}
v___jp_2472_:
{
lean_object* v___x_2474_; uint8_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = 0;
v___x_2476_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2474_, v___x_2475_, v_val_2473_, v___f_2471_);
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2493_, lean_object* v_x_2494_, lean_object* v_head_2495_, lean_object* v_x_2496_){
_start:
{
if (lean_obj_tag(v_x_2496_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2506_; 
lean_dec_ref(v_head_2495_);
lean_dec(v_x_2494_);
lean_dec(v_tail_2493_);
v_a_2498_ = lean_ctor_get(v_x_2496_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_x_2496_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2500_ = v_x_2496_;
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v_x_2496_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2506_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
}
else
{
lean_object* v_a_2507_; uint8_t v___x_2508_; 
v_a_2507_ = lean_ctor_get(v_x_2496_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v_x_2496_, 1);
v___x_2508_ = lean_unbox(v_a_2507_);
lean_dec(v_a_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
lean_dec_ref(v_head_2495_);
v___x_2509_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2493_, v_x_2494_);
return v___x_2509_;
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2510_, 0, v_head_2495_);
lean_ctor_set(v___x_2510_, 1, v_x_2494_);
v___x_2511_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2493_, v___x_2510_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2512_, lean_object* v_x_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2512_, v_x_2513_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v_eList_2516_, lean_object* v___x_2517_, lean_object* v___f_2518_, lean_object* v_x_2519_){
_start:
{
if (lean_obj_tag(v_x_2519_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v___f_2518_);
lean_dec(v___x_2517_);
lean_dec(v_eList_2516_);
v_a_2521_ = lean_ctor_get(v_x_2519_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_x_2519_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2523_ = v_x_2519_;
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v_x_2519_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2529_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
return v___x_2527_;
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___f_2535_; lean_object* v___x_2536_; 
v_a_2530_ = lean_ctor_get(v_x_2519_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v_x_2519_, 1);
lean_inc(v___x_2517_);
v___x_2531_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2516_, v___x_2517_);
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = 0;
v___x_2534_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2532_, v___x_2533_, v___x_2531_, v___f_2518_);
v___f_2535_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2535_, 0, v_a_2530_);
lean_closure_set(v___f_2535_, 1, v___x_2517_);
v___x_2536_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2532_, v___x_2533_, v___x_2534_, v___f_2535_);
return v___x_2536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_eList_2537_, lean_object* v___x_2538_, lean_object* v___f_2539_, lean_object* v_x_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v_eList_2537_, v___x_2538_, v___f_2539_, v_x_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_eList_2546_; lean_object* v_dList_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; 
v_eList_2546_ = lean_ctor_get(v_q_2543_, 0);
lean_inc(v_eList_2546_);
v_dList_2547_ = lean_ctor_get(v_q_2543_, 1);
lean_inc(v_dList_2547_);
lean_dec_ref(v_q_2543_);
v___x_2548_ = lean_box(0);
v___x_2549_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2547_, v___x_2548_);
v___f_2550_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = 0;
v___x_2553_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2551_, v___x_2552_, v___x_2549_, v___f_2550_);
v___f_2554_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2554_, 0, v_eList_2546_);
lean_closure_set(v___f_2554_, 1, v___x_2548_);
lean_closure_set(v___f_2554_, 2, v___f_2550_);
v___x_2555_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2551_, v___x_2552_, v___x_2553_, v___f_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2556_, v___y_2557_);
lean_dec(v___y_2557_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2560_, lean_object* v_x_2561_){
_start:
{
if (lean_obj_tag(v_x_2561_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2571_; 
v_a_2563_ = lean_ctor_get(v_x_2561_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_x_2561_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2565_ = v_x_2561_;
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v_x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2571_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
return v___x_2569_;
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v_producers_2573_; lean_object* v_consumers_2574_; uint8_t v_closed_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; lean_object* v___x_2581_; 
v_a_2572_ = lean_ctor_get(v_x_2561_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v_x_2561_, 1);
v_producers_2573_ = lean_ctor_get(v_a_2572_, 0);
lean_inc_ref(v_producers_2573_);
v_consumers_2574_ = lean_ctor_get(v_a_2572_, 1);
lean_inc_ref(v_consumers_2574_);
v_closed_2575_ = lean_ctor_get_uint8(v_a_2572_, sizeof(void*)*2);
lean_dec(v_a_2572_);
v___x_2576_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2574_, v___y_2560_);
v___x_2577_ = lean_box(v_closed_2575_);
lean_inc(v___y_2560_);
v___f_2578_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2578_, 0, v_producers_2573_);
lean_closure_set(v___f_2578_, 1, v___x_2577_);
lean_closure_set(v___f_2578_, 2, v___y_2560_);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = 0;
v___x_2581_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2579_, v___x_2580_, v___x_2576_, v___f_2578_);
return v___x_2581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2582_, lean_object* v_x_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2582_, v_x_2583_);
lean_dec(v___y_2582_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; lean_object* v___f_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; 
v___x_2588_ = lean_st_ref_get(v___y_2586_);
lean_inc(v___y_2586_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2589_, 0, v___y_2586_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = 0;
v___x_2594_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2592_, v___x_2593_, v___x_2591_, v___f_2589_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2595_);
lean_dec(v___y_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2603_){
_start:
{
lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___f_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___f_2604_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref_n(v_ch_2603_, 2);
v___f_2605_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2605_, 0, v___f_2604_);
lean_closure_set(v___f_2605_, 1, v_ch_2603_);
v___f_2606_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2607_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
v___x_2608_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2608_, 0, lean_box(0));
lean_closure_set(v___x_2608_, 1, lean_box(0));
lean_closure_set(v___x_2608_, 2, v_ch_2603_);
lean_closure_set(v___x_2608_, 3, v___f_2606_);
v___x_2609_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2609_, 0, lean_box(0));
lean_closure_set(v___x_2609_, 1, lean_box(0));
lean_closure_set(v___x_2609_, 2, v_ch_2603_);
lean_closure_set(v___x_2609_, 3, v___f_2607_);
v___x_2610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___f_2605_);
lean_ctor_set(v___x_2610_, 2, v___x_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2611_, lean_object* v_ch_2612_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2614_, lean_object* v_q_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2615_, v___y_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2619_, lean_object* v_q_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2619_, v_q_2620_, v___y_2621_);
lean_dec(v___y_2621_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___x_2629_; 
v___x_2629_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2625_, v_x_2626_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2630_, v_x_2631_, v_x_2632_, v___y_2633_);
lean_dec(v___y_2633_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2636_, uint8_t v_b_2637_){
_start:
{
lean_object* v_promise_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_promise_2639_ = lean_ctor_get(v_c_2636_, 0);
v___x_2640_ = lean_box(v_b_2637_);
v___x_2641_ = lean_io_promise_resolve(v___x_2640_, v_promise_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2642_, lean_object* v_b_2643_, lean_object* v_a_2644_){
_start:
{
uint8_t v_b_boxed_2645_; lean_object* v_res_2646_; 
v_b_boxed_2645_ = lean_unbox(v_b_2643_);
v_res_2646_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2642_, v_b_boxed_2645_);
lean_dec_ref(v_c_2642_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2647_, lean_object* v_c_2648_, uint8_t v_b_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2648_, v_b_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2652_, lean_object* v_c_2653_, lean_object* v_b_2654_, lean_object* v_a_2655_){
_start:
{
uint8_t v_b_boxed_2656_; lean_object* v_res_2657_; 
v_b_boxed_2656_ = lean_unbox(v_b_2654_);
v_res_2657_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2652_, v_c_2653_, v_b_boxed_2656_);
lean_dec_ref(v_c_2653_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2658_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = lean_st_mk_ref(v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2662_);
lean_dec(v_x_2662_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2665_, lean_object* v_f_2666_, lean_object* v_xs_2667_, lean_object* v_k_2668_, lean_object* v_acc_2669_){
_start:
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_nat_dec_lt(v_k_2668_, v_n_2665_);
if (v___x_2671_ == 0)
{
lean_dec(v_k_2668_);
lean_dec_ref(v_f_2666_);
return v_acc_2669_;
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2672_ = lean_array_fget_borrowed(v_xs_2667_, v_k_2668_);
lean_inc_ref(v_f_2666_);
lean_inc(v___x_2672_);
v___x_2673_ = lean_apply_2(v_f_2666_, v___x_2672_, lean_box(0));
v___x_2674_ = lean_unsigned_to_nat(1u);
v___x_2675_ = lean_nat_add(v_k_2668_, v___x_2674_);
lean_dec(v_k_2668_);
v___x_2676_ = lean_array_push(v_acc_2669_, v___x_2673_);
v_k_2668_ = v___x_2675_;
v_acc_2669_ = v___x_2676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2678_, lean_object* v_f_2679_, lean_object* v_xs_2680_, lean_object* v_k_2681_, lean_object* v_acc_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2678_, v_f_2679_, v_xs_2680_, v_k_2681_, v_acc_2682_);
lean_dec_ref(v_xs_2680_);
lean_dec(v_n_2678_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2688_){
_start:
{
lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___f_2690_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2688_);
v___x_2691_ = l_Array_range(v_capacity_2688_);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2694_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2688_, v___f_2690_, v___x_2691_, v___x_2692_, v___x_2693_);
lean_dec_ref(v___x_2691_);
v___x_2695_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2696_ = 0;
v___x_2697_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2695_);
lean_ctor_set(v___x_2697_, 2, v_capacity_2688_);
lean_ctor_set(v___x_2697_, 3, v___x_2694_);
lean_ctor_set(v___x_2697_, 4, v___x_2692_);
lean_ctor_set(v___x_2697_, 5, v___x_2692_);
lean_ctor_set(v___x_2697_, 6, v___x_2692_);
lean_ctor_set_uint8(v___x_2697_, sizeof(void*)*7, v___x_2696_);
v___x_2698_ = l_Std_Mutex_new___redArg(v___x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2699_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2702_, lean_object* v_capacity_2703_, lean_object* v_hcap_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2703_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2707_, lean_object* v_capacity_2708_, lean_object* v_hcap_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2707_, v_capacity_2708_, v_hcap_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2712_, lean_object* v_00_u03b2_2713_, lean_object* v_n_2714_, lean_object* v_f_2715_, lean_object* v_xs_2716_, lean_object* v_k_2717_, lean_object* v_h_2718_, lean_object* v_acc_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2714_, v_f_2715_, v_xs_2716_, v_k_2717_, v_acc_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_00_u03b2_2723_, lean_object* v_n_2724_, lean_object* v_f_2725_, lean_object* v_xs_2726_, lean_object* v_k_2727_, lean_object* v_h_2728_, lean_object* v_acc_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2722_, v_00_u03b2_2723_, v_n_2724_, v_f_2725_, v_xs_2726_, v_k_2727_, v_h_2728_, v_acc_2729_);
lean_dec_ref(v_xs_2726_);
lean_dec(v_n_2724_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2732_, lean_object* v_cap_2733_){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2735_ = lean_nat_add(v_idx_2732_, v___x_2734_);
v___x_2736_ = lean_nat_dec_eq(v___x_2735_, v_cap_2733_);
if (v___x_2736_ == 0)
{
return v___x_2735_;
}
else
{
lean_object* v___x_2737_; 
lean_dec(v___x_2735_);
v___x_2737_ = lean_unsigned_to_nat(0u);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2738_, lean_object* v_cap_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2738_, v_cap_2739_);
lean_dec(v_cap_2739_);
lean_dec(v_idx_2738_);
return v_res_2740_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_st_2745_; lean_object* v___y_2746_; lean_object* v___x_2749_; lean_object* v_producers_2750_; lean_object* v_consumers_2751_; lean_object* v_capacity_2752_; lean_object* v_buf_2753_; lean_object* v_bufCount_2754_; lean_object* v_sendIdx_2755_; lean_object* v_recvIdx_2756_; uint8_t v_closed_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2783_; 
v___x_2749_ = lean_st_ref_get(v_a_2742_);
v_producers_2750_ = lean_ctor_get(v___x_2749_, 0);
v_consumers_2751_ = lean_ctor_get(v___x_2749_, 1);
v_capacity_2752_ = lean_ctor_get(v___x_2749_, 2);
v_buf_2753_ = lean_ctor_get(v___x_2749_, 3);
v_bufCount_2754_ = lean_ctor_get(v___x_2749_, 4);
v_sendIdx_2755_ = lean_ctor_get(v___x_2749_, 5);
v_recvIdx_2756_ = lean_ctor_get(v___x_2749_, 6);
v_closed_2757_ = lean_ctor_get_uint8(v___x_2749_, sizeof(void*)*7);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2759_ = v___x_2749_;
v_isShared_2760_ = v_isSharedCheck_2783_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_recvIdx_2756_);
lean_inc(v_sendIdx_2755_);
lean_inc(v_bufCount_2754_);
lean_inc(v_buf_2753_);
lean_inc(v_capacity_2752_);
lean_inc(v_consumers_2751_);
lean_inc(v_producers_2750_);
lean_dec(v___x_2749_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2783_;
goto v_resetjp_2758_;
}
v___jp_2744_:
{
lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2747_ = lean_st_ref_set(v___y_2746_, v_st_2745_);
v___x_2748_ = 1;
return v___x_2748_;
}
v_resetjp_2758_:
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_nat_dec_eq(v_bufCount_2754_, v_capacity_2752_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___y_2768_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2762_ = lean_array_fget_borrowed(v_buf_2753_, v_sendIdx_2755_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_v_2741_);
v___x_2764_ = lean_st_ref_set(v___x_2762_, v___x_2763_);
v___x_2765_ = lean_unsigned_to_nat(1u);
v___x_2766_ = lean_nat_add(v_bufCount_2754_, v___x_2765_);
lean_dec(v_bufCount_2754_);
v___x_2779_ = lean_nat_add(v_sendIdx_2755_, v___x_2765_);
lean_dec(v_sendIdx_2755_);
v___x_2780_ = lean_nat_dec_eq(v___x_2779_, v_capacity_2752_);
if (v___x_2780_ == 0)
{
v___y_2768_ = v___x_2779_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2781_; 
lean_dec(v___x_2779_);
v___x_2781_ = lean_unsigned_to_nat(0u);
v___y_2768_ = v___x_2781_;
goto v___jp_2767_;
}
v___jp_2767_:
{
lean_object* v___x_2770_; 
lean_inc(v_recvIdx_2756_);
lean_inc(v___y_2768_);
lean_inc(v___x_2766_);
lean_inc_ref(v_buf_2753_);
lean_inc(v_capacity_2752_);
lean_inc_ref(v_consumers_2751_);
lean_inc_ref(v_producers_2750_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 5, v___y_2768_);
lean_ctor_set(v___x_2759_, 4, v___x_2766_);
v___x_2770_ = v___x_2759_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_producers_2750_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_consumers_2751_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_capacity_2752_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v_buf_2753_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2778_, 5, v___y_2768_);
lean_ctor_set(v_reuseFailAlloc_2778_, 6, v_recvIdx_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2778_, sizeof(void*)*7, v_closed_2757_);
v___x_2770_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2751_);
if (lean_obj_tag(v___x_2771_) == 1)
{
lean_object* v_val_2772_; lean_object* v_fst_2773_; lean_object* v_snd_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec_ref(v___x_2770_);
v_val_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_val_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v_fst_2773_ = lean_ctor_get(v_val_2772_, 0);
lean_inc(v_fst_2773_);
v_snd_2774_ = lean_ctor_get(v_val_2772_, 1);
lean_inc(v_snd_2774_);
lean_dec(v_val_2772_);
v___x_2775_ = 1;
v___x_2776_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2773_, v___x_2775_);
lean_dec(v_fst_2773_);
v___x_2777_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2777_, 0, v_producers_2750_);
lean_ctor_set(v___x_2777_, 1, v_snd_2774_);
lean_ctor_set(v___x_2777_, 2, v_capacity_2752_);
lean_ctor_set(v___x_2777_, 3, v_buf_2753_);
lean_ctor_set(v___x_2777_, 4, v___x_2766_);
lean_ctor_set(v___x_2777_, 5, v___y_2768_);
lean_ctor_set(v___x_2777_, 6, v_recvIdx_2756_);
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*7, v_closed_2757_);
v_st_2745_ = v___x_2777_;
v___y_2746_ = v_a_2742_;
goto v___jp_2744_;
}
else
{
lean_dec(v___x_2771_);
lean_dec(v___y_2768_);
lean_dec(v___x_2766_);
lean_dec(v_recvIdx_2756_);
lean_dec_ref(v_buf_2753_);
lean_dec(v_capacity_2752_);
lean_dec_ref(v_producers_2750_);
v_st_2745_ = v___x_2770_;
v___y_2746_ = v_a_2742_;
goto v___jp_2744_;
}
}
}
}
else
{
uint8_t v___x_2782_; 
lean_del_object(v___x_2759_);
lean_dec(v_recvIdx_2756_);
lean_dec(v_sendIdx_2755_);
lean_dec(v_bufCount_2754_);
lean_dec_ref(v_buf_2753_);
lean_dec(v_capacity_2752_);
lean_dec_ref(v_consumers_2751_);
lean_dec_ref(v_producers_2750_);
lean_dec(v_v_2741_);
v___x_2782_ = 0;
return v___x_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2784_, v_a_2785_);
lean_dec(v_a_2785_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2789_, lean_object* v_v_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v___x_2793_; 
v___x_2793_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2790_, v_a_2791_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2794_, lean_object* v_v_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
uint8_t v_res_2798_; lean_object* v_r_2799_; 
v_res_2798_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2794_, v_v_2795_, v_a_2796_);
lean_dec(v_a_2796_);
v_r_2799_ = lean_box(v_res_2798_);
return v_r_2799_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___x_2803_; uint8_t v_closed_2804_; 
v___x_2803_ = lean_st_ref_get(v___y_2801_);
v_closed_2804_ = lean_ctor_get_uint8(v___x_2803_, sizeof(void*)*7);
lean_dec(v___x_2803_);
if (v_closed_2804_ == 0)
{
uint8_t v___x_2805_; 
v___x_2805_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2800_, v___y_2801_);
return v___x_2805_;
}
else
{
uint8_t v___x_2806_; 
lean_dec(v_v_2800_);
v___x_2806_ = 0;
return v___x_2806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
uint8_t v_res_2810_; lean_object* v_r_2811_; 
v_res_2810_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2807_, v___y_2808_);
lean_dec(v___y_2808_);
v_r_2811_ = lean_box(v_res_2810_);
return v_r_2811_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2812_, lean_object* v_v_2813_){
_start:
{
lean_object* v___f_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___f_2815_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2815_, 0, v_v_2813_);
v___x_2816_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2812_, v___f_2815_);
v___x_2817_ = lean_unbox(v___x_2816_);
lean_dec(v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2818_, lean_object* v_v_2819_, lean_object* v_a_2820_){
_start:
{
uint8_t v_res_2821_; lean_object* v_r_2822_; 
v_res_2821_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2818_, v_v_2819_);
v_r_2822_ = lean_box(v_res_2821_);
return v_r_2822_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2823_, lean_object* v_ch_2824_, lean_object* v_v_2825_){
_start:
{
uint8_t v___x_2827_; 
v___x_2827_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2824_, v_v_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_ch_2829_, lean_object* v_v_2830_, lean_object* v_a_2831_){
_start:
{
uint8_t v_res_2832_; lean_object* v_r_2833_; 
v_res_2832_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(v_00_u03b1_2828_, v_ch_2829_, v_v_2830_);
v_r_2833_ = lean_box(v_res_2832_);
return v_r_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object* v_v_2834_, lean_object* v___f_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___x_2838_; uint8_t v_closed_2839_; 
v___x_2838_ = lean_st_ref_get(v___y_2836_);
v_closed_2839_ = lean_ctor_get_uint8(v___x_2838_, sizeof(void*)*7);
lean_dec(v___x_2838_);
if (v_closed_2839_ == 0)
{
uint8_t v___x_2840_; 
v___x_2840_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2834_, v___y_2836_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v_producers_2843_; lean_object* v_consumers_2844_; lean_object* v_capacity_2845_; lean_object* v_buf_2846_; lean_object* v_bufCount_2847_; lean_object* v_sendIdx_2848_; lean_object* v_recvIdx_2849_; uint8_t v_closed_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2862_; 
v___x_2841_ = lean_io_promise_new();
v___x_2842_ = lean_st_ref_take(v___y_2836_);
v_producers_2843_ = lean_ctor_get(v___x_2842_, 0);
v_consumers_2844_ = lean_ctor_get(v___x_2842_, 1);
v_capacity_2845_ = lean_ctor_get(v___x_2842_, 2);
v_buf_2846_ = lean_ctor_get(v___x_2842_, 3);
v_bufCount_2847_ = lean_ctor_get(v___x_2842_, 4);
v_sendIdx_2848_ = lean_ctor_get(v___x_2842_, 5);
v_recvIdx_2849_ = lean_ctor_get(v___x_2842_, 6);
v_closed_2850_ = lean_ctor_get_uint8(v___x_2842_, sizeof(void*)*7);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2852_ = v___x_2842_;
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_recvIdx_2849_);
lean_inc(v_sendIdx_2848_);
lean_inc(v_bufCount_2847_);
lean_inc(v_buf_2846_);
lean_inc(v_capacity_2845_);
lean_inc(v_consumers_2844_);
lean_inc(v_producers_2843_);
lean_dec(v___x_2842_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2856_; 
lean_inc(v___x_2841_);
v___x_2854_ = l_Std_Queue_enqueue___redArg(v___x_2841_, v_producers_2843_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2854_);
v___x_2856_ = v___x_2852_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_consumers_2844_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_capacity_2845_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_buf_2846_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_bufCount_2847_);
lean_ctor_set(v_reuseFailAlloc_2861_, 5, v_sendIdx_2848_);
lean_ctor_set(v_reuseFailAlloc_2861_, 6, v_recvIdx_2849_);
lean_ctor_set_uint8(v_reuseFailAlloc_2861_, sizeof(void*)*7, v_closed_2850_);
v___x_2856_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2857_ = lean_st_ref_set(v___y_2836_, v___x_2856_);
v___x_2858_ = lean_io_promise_result_opt(v___x_2841_);
lean_dec(v___x_2841_);
v___x_2859_ = lean_unsigned_to_nat(0u);
v___x_2860_ = lean_io_bind_task(v___x_2858_, v___f_2835_, v___x_2859_, v___x_2840_);
return v___x_2860_;
}
}
}
else
{
lean_object* v___x_2863_; 
lean_dec_ref(v___f_2835_);
v___x_2863_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_2863_;
}
}
else
{
lean_object* v___x_2864_; 
lean_dec_ref(v___f_2835_);
lean_dec(v_v_2834_);
v___x_2864_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_2865_, lean_object* v___f_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2865_, v___f_2866_, v___y_2867_);
lean_dec(v___y_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object* v_ch_2870_, lean_object* v_v_2871_, lean_object* v_res_2872_){
_start:
{
if (lean_obj_tag(v_res_2872_) == 0)
{
lean_dec(v_v_2871_);
lean_dec_ref(v_ch_2870_);
goto v___jp_2874_;
}
else
{
lean_object* v_val_2876_; uint8_t v___x_2877_; 
v_val_2876_ = lean_ctor_get(v_res_2872_, 0);
v___x_2877_ = lean_unbox(v_val_2876_);
if (v___x_2877_ == 0)
{
lean_dec(v_v_2871_);
lean_dec_ref(v_ch_2870_);
goto v___jp_2874_;
}
else
{
lean_object* v___x_2878_; 
v___x_2878_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2870_, v_v_2871_);
return v___x_2878_;
}
}
v___jp_2874_:
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_2879_, lean_object* v_v_2880_, lean_object* v_res_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2879_, v_v_2880_, v_res_2881_);
lean_dec(v_res_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object* v_ch_2884_, lean_object* v_v_2885_){
_start:
{
lean_object* v___f_2887_; lean_object* v___f_2888_; lean_object* v___x_2889_; 
lean_inc(v_v_2885_);
lean_inc_ref(v_ch_2884_);
v___f_2887_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2887_, 0, v_ch_2884_);
lean_closure_set(v___f_2887_, 1, v_v_2885_);
v___f_2888_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2888_, 0, v_v_2885_);
lean_closure_set(v___f_2888_, 1, v___f_2887_);
v___x_2889_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2884_, v___f_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object* v_ch_2890_, lean_object* v_v_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2890_, v_v_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object* v_00_u03b1_2894_, lean_object* v_ch_2895_, lean_object* v_v_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2895_, v_v_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object* v_00_u03b1_2899_, lean_object* v_ch_2900_, lean_object* v_v_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(v_00_u03b1_2899_, v_ch_2900_, v_v_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_2904_, lean_object* v_as_2905_, size_t v_sz_2906_, size_t v_i_2907_, lean_object* v_b_2908_){
_start:
{
uint8_t v___x_2910_; 
v___x_2910_ = lean_usize_dec_lt(v_i_2907_, v_sz_2906_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v_b_2908_);
return v___x_2911_;
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; size_t v___x_2915_; size_t v___x_2916_; 
v_a_2912_ = lean_array_uget_borrowed(v_as_2905_, v_i_2907_);
v___x_2913_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2912_, v___x_2904_);
v___x_2914_ = lean_box(0);
v___x_2915_ = ((size_t)1ULL);
v___x_2916_ = lean_usize_add(v_i_2907_, v___x_2915_);
v_i_2907_ = v___x_2916_;
v_b_2908_ = v___x_2914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2918_, lean_object* v_as_2919_, lean_object* v_sz_2920_, lean_object* v_i_2921_, lean_object* v_b_2922_, lean_object* v___y_2923_){
_start:
{
uint8_t v___x_1136__boxed_2924_; size_t v_sz_boxed_2925_; size_t v_i_boxed_2926_; lean_object* v_res_2927_; 
v___x_1136__boxed_2924_ = lean_unbox(v___x_2918_);
v_sz_boxed_2925_ = lean_unbox_usize(v_sz_2920_);
lean_dec(v_sz_2920_);
v_i_boxed_2926_ = lean_unbox_usize(v_i_2921_);
lean_dec(v_i_2921_);
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1136__boxed_2924_, v_as_2919_, v_sz_boxed_2925_, v_i_boxed_2926_, v_b_2922_);
lean_dec_ref(v_as_2919_);
return v_res_2927_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Std_Queue_empty(lean_box(0));
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; uint8_t v_closed_2932_; 
v___x_2931_ = lean_st_ref_get(v___y_2929_);
v_closed_2932_ = lean_ctor_get_uint8(v___x_2931_, sizeof(void*)*7);
if (v_closed_2932_ == 0)
{
lean_object* v_producers_2933_; lean_object* v_consumers_2934_; lean_object* v_capacity_2935_; lean_object* v_buf_2936_; lean_object* v_bufCount_2937_; lean_object* v_sendIdx_2938_; lean_object* v_recvIdx_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2962_; 
v_producers_2933_ = lean_ctor_get(v___x_2931_, 0);
v_consumers_2934_ = lean_ctor_get(v___x_2931_, 1);
v_capacity_2935_ = lean_ctor_get(v___x_2931_, 2);
v_buf_2936_ = lean_ctor_get(v___x_2931_, 3);
v_bufCount_2937_ = lean_ctor_get(v___x_2931_, 4);
v_sendIdx_2938_ = lean_ctor_get(v___x_2931_, 5);
v_recvIdx_2939_ = lean_ctor_get(v___x_2931_, 6);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2941_ = v___x_2931_;
v_isShared_2942_ = v_isSharedCheck_2962_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_recvIdx_2939_);
lean_inc(v_sendIdx_2938_);
lean_inc(v_bufCount_2937_);
lean_inc(v_buf_2936_);
lean_inc(v_capacity_2935_);
lean_inc(v_consumers_2934_);
lean_inc(v_producers_2933_);
lean_dec(v___x_2931_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2962_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; size_t v_sz_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v___x_2943_ = l_Std_Queue_toArray___redArg(v_consumers_2934_);
v___x_2944_ = lean_box(0);
v_sz_2945_ = lean_array_size(v___x_2943_);
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2932_, v___x_2943_, v_sz_2945_, v___x_2946_, v___x_2944_);
lean_dec_ref(v___x_2943_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2960_; 
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v___x_2947_, 0);
lean_dec(v_unused_2961_);
v___x_2949_ = v___x_2947_;
v_isShared_2950_ = v_isSharedCheck_2960_;
goto v_resetjp_2948_;
}
else
{
lean_dec(v___x_2947_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2960_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; uint8_t v___x_2952_; lean_object* v___x_2954_; 
v___x_2951_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0);
v___x_2952_ = 1;
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2951_);
v___x_2954_ = v___x_2941_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_producers_2933_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2959_, 2, v_capacity_2935_);
lean_ctor_set(v_reuseFailAlloc_2959_, 3, v_buf_2936_);
lean_ctor_set(v_reuseFailAlloc_2959_, 4, v_bufCount_2937_);
lean_ctor_set(v_reuseFailAlloc_2959_, 5, v_sendIdx_2938_);
lean_ctor_set(v_reuseFailAlloc_2959_, 6, v_recvIdx_2939_);
v___x_2954_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
lean_ctor_set_uint8(v___x_2954_, sizeof(void*)*7, v___x_2952_);
v___x_2955_ = lean_st_ref_set(v___y_2929_, v___x_2954_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2944_);
v___x_2957_ = v___x_2949_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2944_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_del_object(v___x_2941_);
lean_dec(v_recvIdx_2939_);
lean_dec(v_sendIdx_2938_);
lean_dec(v_bufCount_2937_);
lean_dec_ref(v_buf_2936_);
lean_dec(v_capacity_2935_);
lean_dec_ref(v_producers_2933_);
return v___x_2947_;
}
}
}
else
{
uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v___x_2931_);
v___x_2963_ = 1;
v___x_2964_ = lean_box(v___x_2963_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2966_);
lean_dec(v___y_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2970_){
_start:
{
lean_object* v___f_2972_; lean_object* v___x_2973_; 
v___f_2972_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2973_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2970_, v___f_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2977_, lean_object* v_ch_2978_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2981_, lean_object* v_ch_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2981_, v_ch_2982_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2985_, uint8_t v___x_2986_, lean_object* v_as_2987_, size_t v_sz_2988_, size_t v_i_2989_, lean_object* v_b_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2986_, v_as_2987_, v_sz_2988_, v_i_2989_, v_b_2990_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2994_, lean_object* v___x_2995_, lean_object* v_as_2996_, lean_object* v_sz_2997_, lean_object* v_i_2998_, lean_object* v_b_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
uint8_t v___x_1234__boxed_3002_; size_t v_sz_boxed_3003_; size_t v_i_boxed_3004_; lean_object* v_res_3005_; 
v___x_1234__boxed_3002_ = lean_unbox(v___x_2995_);
v_sz_boxed_3003_ = lean_unbox_usize(v_sz_2997_);
lean_dec(v_sz_2997_);
v_i_boxed_3004_ = lean_unbox_usize(v_i_2998_);
lean_dec(v_i_2998_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2994_, v___x_1234__boxed_3002_, v_as_2996_, v_sz_boxed_3003_, v_i_boxed_3004_, v_b_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v_as_2996_);
return v_res_3005_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_3006_){
_start:
{
lean_object* v___x_3008_; uint8_t v_closed_3009_; 
v___x_3008_ = lean_st_ref_get(v___y_3006_);
v_closed_3009_ = lean_ctor_get_uint8(v___x_3008_, sizeof(void*)*7);
lean_dec(v___x_3008_);
return v_closed_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
uint8_t v_res_3012_; lean_object* v_r_3013_; 
v_res_3012_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_3010_);
lean_dec(v___y_3010_);
v_r_3013_ = lean_box(v_res_3012_);
return v_r_3013_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_3015_){
_start:
{
lean_object* v___f_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___f_3017_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_3018_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3015_, v___f_3017_);
v___x_3019_ = lean_unbox(v___x_3018_);
lean_dec(v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_3020_, lean_object* v_a_3021_){
_start:
{
uint8_t v_res_3022_; lean_object* v_r_3023_; 
v_res_3022_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3020_);
v_r_3023_ = lean_box(v_res_3022_);
return v_r_3023_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_3024_, lean_object* v_ch_3025_){
_start:
{
uint8_t v___x_3027_; 
v___x_3027_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3025_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_3028_, lean_object* v_ch_3029_, lean_object* v_a_3030_){
_start:
{
uint8_t v_res_3031_; lean_object* v_r_3032_; 
v_res_3031_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_3028_, v_ch_3029_);
v_r_3032_ = lean_box(v_res_3031_);
return v_r_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_toPure_3036_; lean_object* v___x_3037_; 
v_toPure_3036_ = lean_ctor_get(v_toApplicative_3033_, 1);
lean_inc(v_toPure_3036_);
lean_dec_ref(v_toApplicative_3033_);
v___x_3037_ = lean_apply_2(v_toPure_3036_, lean_box(0), v_a_3034_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_3038_, lean_object* v_toBind_3039_, lean_object* v___f_3040_, lean_object* v_____r_3041_, lean_object* v_st_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_inc(v___y_3043_);
v___x_3044_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_3044_, 0, lean_box(0));
lean_closure_set(v___x_3044_, 1, lean_box(0));
lean_closure_set(v___x_3044_, 2, v___y_3043_);
lean_closure_set(v___x_3044_, 3, v_st_3042_);
v___x_3045_ = lean_apply_2(v_inst_3038_, lean_box(0), v___x_3044_);
v___x_3046_ = lean_apply_4(v_toBind_3039_, lean_box(0), lean_box(0), v___x_3045_, v___f_3040_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_3047_, lean_object* v_toBind_3048_, lean_object* v___f_3049_, lean_object* v_____r_3050_, lean_object* v_st_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3047_, v_toBind_3048_, v___f_3049_, v_____r_3050_, v_st_3051_, v___y_3052_);
lean_dec(v___y_3052_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_3054_, lean_object* v_consumers_3055_, lean_object* v_capacity_3056_, lean_object* v_buf_3057_, lean_object* v___x_3058_, lean_object* v_sendIdx_3059_, lean_object* v___y_3060_, uint8_t v_closed_3061_, lean_object* v___f_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3065_, 0, v_snd_3054_);
lean_ctor_set(v___x_3065_, 1, v_consumers_3055_);
lean_ctor_set(v___x_3065_, 2, v_capacity_3056_);
lean_ctor_set(v___x_3065_, 3, v_buf_3057_);
lean_ctor_set(v___x_3065_, 4, v___x_3058_);
lean_ctor_set(v___x_3065_, 5, v_sendIdx_3059_);
lean_ctor_set(v___x_3065_, 6, v___y_3060_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*7, v_closed_3061_);
v___x_3066_ = lean_box(0);
lean_inc(v_a_3063_);
v___x_3067_ = lean_apply_3(v___f_3062_, v___x_3066_, v___x_3065_, v_a_3063_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3068_, lean_object* v_consumers_3069_, lean_object* v_capacity_3070_, lean_object* v_buf_3071_, lean_object* v___x_3072_, lean_object* v_sendIdx_3073_, lean_object* v___y_3074_, lean_object* v_closed_3075_, lean_object* v___f_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
uint8_t v_closed_boxed_3079_; lean_object* v_res_3080_; 
v_closed_boxed_3079_ = lean_unbox(v_closed_3075_);
v_res_3080_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3068_, v_consumers_3069_, v_capacity_3070_, v_buf_3071_, v___x_3072_, v_sendIdx_3073_, v___y_3074_, v_closed_boxed_3079_, v___f_3076_, v_a_3077_, v_a_3078_);
lean_dec(v_a_3077_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3081_, lean_object* v_inst_3082_, lean_object* v_toBind_3083_, lean_object* v_bufCount_3084_, lean_object* v_producers_3085_, lean_object* v_consumers_3086_, lean_object* v_capacity_3087_, lean_object* v_buf_3088_, lean_object* v_sendIdx_3089_, uint8_t v_closed_3090_, lean_object* v_a_3091_, uint8_t v___x_3092_, lean_object* v_inst_3093_, lean_object* v_recvIdx_3094_, lean_object* v___x_3095_, lean_object* v_a_3096_){
_start:
{
lean_object* v___f_3097_; lean_object* v___f_3098_; lean_object* v___y_3100_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___f_3097_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3097_, 0, v_toApplicative_3081_);
lean_closure_set(v___f_3097_, 1, v_a_3096_);
lean_inc_ref(v___f_3097_);
lean_inc(v_toBind_3083_);
lean_inc(v_inst_3082_);
v___f_3098_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3098_, 0, v_inst_3082_);
lean_closure_set(v___f_3098_, 1, v_toBind_3083_);
lean_closure_set(v___f_3098_, 2, v___f_3097_);
v___x_3116_ = lean_unsigned_to_nat(1u);
v___x_3117_ = lean_nat_add(v_recvIdx_3094_, v___x_3116_);
v___x_3118_ = lean_nat_dec_eq(v___x_3117_, v_capacity_3087_);
if (v___x_3118_ == 0)
{
lean_dec(v___x_3095_);
v___y_3100_ = v___x_3117_;
goto v___jp_3099_;
}
else
{
lean_dec(v___x_3117_);
v___y_3100_ = v___x_3095_;
goto v___jp_3099_;
}
v___jp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3101_ = lean_unsigned_to_nat(1u);
v___x_3102_ = lean_nat_sub(v_bufCount_3084_, v___x_3101_);
lean_inc(v___y_3100_);
lean_inc(v_sendIdx_3089_);
lean_inc(v___x_3102_);
lean_inc_ref(v_buf_3088_);
lean_inc(v_capacity_3087_);
lean_inc_ref(v_consumers_3086_);
lean_inc_ref(v_producers_3085_);
v___x_3103_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3103_, 0, v_producers_3085_);
lean_ctor_set(v___x_3103_, 1, v_consumers_3086_);
lean_ctor_set(v___x_3103_, 2, v_capacity_3087_);
lean_ctor_set(v___x_3103_, 3, v_buf_3088_);
lean_ctor_set(v___x_3103_, 4, v___x_3102_);
lean_ctor_set(v___x_3103_, 5, v_sendIdx_3089_);
lean_ctor_set(v___x_3103_, 6, v___y_3100_);
lean_ctor_set_uint8(v___x_3103_, sizeof(void*)*7, v_closed_3090_);
v___x_3104_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3085_);
if (lean_obj_tag(v___x_3104_) == 1)
{
lean_object* v_val_3105_; lean_object* v_fst_3106_; lean_object* v_snd_3107_; lean_object* v___x_3108_; lean_object* v___f_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec_ref_known(v___x_3103_, 7);
lean_dec_ref(v___f_3097_);
lean_dec(v_inst_3082_);
v_val_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_val_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v_fst_3106_ = lean_ctor_get(v_val_3105_, 0);
lean_inc(v_fst_3106_);
v_snd_3107_ = lean_ctor_get(v_val_3105_, 1);
lean_inc(v_snd_3107_);
lean_dec(v_val_3105_);
v___x_3108_ = lean_box(v_closed_3090_);
lean_inc(v_a_3091_);
v___f_3109_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3109_, 0, v_snd_3107_);
lean_closure_set(v___f_3109_, 1, v_consumers_3086_);
lean_closure_set(v___f_3109_, 2, v_capacity_3087_);
lean_closure_set(v___f_3109_, 3, v_buf_3088_);
lean_closure_set(v___f_3109_, 4, v___x_3102_);
lean_closure_set(v___f_3109_, 5, v_sendIdx_3089_);
lean_closure_set(v___f_3109_, 6, v___y_3100_);
lean_closure_set(v___f_3109_, 7, v___x_3108_);
lean_closure_set(v___f_3109_, 8, v___f_3098_);
lean_closure_set(v___f_3109_, 9, v_a_3091_);
v___x_3110_ = lean_box(v___x_3092_);
v___x_3111_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3111_, 0, lean_box(0));
lean_closure_set(v___x_3111_, 1, v___x_3110_);
lean_closure_set(v___x_3111_, 2, v_fst_3106_);
v___x_3112_ = lean_apply_2(v_inst_3093_, lean_box(0), v___x_3111_);
v___x_3113_ = lean_apply_4(v_toBind_3083_, lean_box(0), lean_box(0), v___x_3112_, v___f_3109_);
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_dec(v___x_3104_);
lean_dec(v___x_3102_);
lean_dec(v___y_3100_);
lean_dec_ref(v___f_3098_);
lean_dec(v_inst_3093_);
lean_dec(v_sendIdx_3089_);
lean_dec_ref(v_buf_3088_);
lean_dec(v_capacity_3087_);
lean_dec_ref(v_consumers_3086_);
v___x_3114_ = lean_box(0);
v___x_3115_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3082_, v_toBind_3083_, v___f_3097_, v___x_3114_, v___x_3103_, v_a_3091_);
return v___x_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3119_, lean_object* v_inst_3120_, lean_object* v_toBind_3121_, lean_object* v_bufCount_3122_, lean_object* v_producers_3123_, lean_object* v_consumers_3124_, lean_object* v_capacity_3125_, lean_object* v_buf_3126_, lean_object* v_sendIdx_3127_, lean_object* v_closed_3128_, lean_object* v_a_3129_, lean_object* v___x_3130_, lean_object* v_inst_3131_, lean_object* v_recvIdx_3132_, lean_object* v___x_3133_, lean_object* v_a_3134_){
_start:
{
uint8_t v_closed_boxed_3135_; uint8_t v___x_679__boxed_3136_; lean_object* v_res_3137_; 
v_closed_boxed_3135_ = lean_unbox(v_closed_3128_);
v___x_679__boxed_3136_ = lean_unbox(v___x_3130_);
v_res_3137_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3119_, v_inst_3120_, v_toBind_3121_, v_bufCount_3122_, v_producers_3123_, v_consumers_3124_, v_capacity_3125_, v_buf_3126_, v_sendIdx_3127_, v_closed_boxed_3135_, v_a_3129_, v___x_679__boxed_3136_, v_inst_3131_, v_recvIdx_3132_, v___x_3133_, v_a_3134_);
lean_dec(v_recvIdx_3132_);
lean_dec(v_a_3129_);
lean_dec(v_bufCount_3122_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3138_, lean_object* v_inst_3139_, lean_object* v_toBind_3140_, lean_object* v_a_3141_, lean_object* v_inst_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_producers_3144_; lean_object* v_consumers_3145_; lean_object* v_capacity_3146_; lean_object* v_buf_3147_; lean_object* v_bufCount_3148_; lean_object* v_sendIdx_3149_; lean_object* v_recvIdx_3150_; uint8_t v_closed_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v_producers_3144_ = lean_ctor_get(v_a_3143_, 0);
lean_inc_ref(v_producers_3144_);
v_consumers_3145_ = lean_ctor_get(v_a_3143_, 1);
lean_inc_ref(v_consumers_3145_);
v_capacity_3146_ = lean_ctor_get(v_a_3143_, 2);
lean_inc(v_capacity_3146_);
v_buf_3147_ = lean_ctor_get(v_a_3143_, 3);
lean_inc_ref(v_buf_3147_);
v_bufCount_3148_ = lean_ctor_get(v_a_3143_, 4);
lean_inc(v_bufCount_3148_);
v_sendIdx_3149_ = lean_ctor_get(v_a_3143_, 5);
lean_inc(v_sendIdx_3149_);
v_recvIdx_3150_ = lean_ctor_get(v_a_3143_, 6);
lean_inc(v_recvIdx_3150_);
v_closed_3151_ = lean_ctor_get_uint8(v_a_3143_, sizeof(void*)*7);
lean_dec_ref(v_a_3143_);
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_nat_dec_eq(v_bufCount_3148_, v___x_3152_);
if (v___x_3153_ == 0)
{
uint8_t v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3154_ = 1;
v___x_3155_ = lean_box(v_closed_3151_);
v___x_3156_ = lean_box(v___x_3154_);
lean_inc(v_recvIdx_3150_);
lean_inc(v_a_3141_);
lean_inc_ref(v_buf_3147_);
lean_inc(v_toBind_3140_);
lean_inc(v_inst_3139_);
v___f_3157_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3157_, 0, v_toApplicative_3138_);
lean_closure_set(v___f_3157_, 1, v_inst_3139_);
lean_closure_set(v___f_3157_, 2, v_toBind_3140_);
lean_closure_set(v___f_3157_, 3, v_bufCount_3148_);
lean_closure_set(v___f_3157_, 4, v_producers_3144_);
lean_closure_set(v___f_3157_, 5, v_consumers_3145_);
lean_closure_set(v___f_3157_, 6, v_capacity_3146_);
lean_closure_set(v___f_3157_, 7, v_buf_3147_);
lean_closure_set(v___f_3157_, 8, v_sendIdx_3149_);
lean_closure_set(v___f_3157_, 9, v___x_3155_);
lean_closure_set(v___f_3157_, 10, v_a_3141_);
lean_closure_set(v___f_3157_, 11, v___x_3156_);
lean_closure_set(v___f_3157_, 12, v_inst_3142_);
lean_closure_set(v___f_3157_, 13, v_recvIdx_3150_);
lean_closure_set(v___f_3157_, 14, v___x_3152_);
v___x_3158_ = lean_array_fget(v_buf_3147_, v_recvIdx_3150_);
lean_dec(v_recvIdx_3150_);
lean_dec_ref(v_buf_3147_);
v___x_3159_ = lean_box(0);
v___x_3160_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3160_, 0, lean_box(0));
lean_closure_set(v___x_3160_, 1, lean_box(0));
lean_closure_set(v___x_3160_, 2, v___x_3158_);
lean_closure_set(v___x_3160_, 3, v___x_3159_);
v___x_3161_ = lean_apply_2(v_inst_3139_, lean_box(0), v___x_3160_);
v___x_3162_ = lean_apply_4(v_toBind_3140_, lean_box(0), lean_box(0), v___x_3161_, v___f_3157_);
return v___x_3162_;
}
else
{
lean_object* v_toPure_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v_recvIdx_3150_);
lean_dec(v_sendIdx_3149_);
lean_dec(v_bufCount_3148_);
lean_dec_ref(v_buf_3147_);
lean_dec(v_capacity_3146_);
lean_dec_ref(v_consumers_3145_);
lean_dec_ref(v_producers_3144_);
lean_dec(v_inst_3142_);
lean_dec(v_toBind_3140_);
lean_dec(v_inst_3139_);
v_toPure_3163_ = lean_ctor_get(v_toApplicative_3138_, 1);
lean_inc(v_toPure_3163_);
lean_dec_ref(v_toApplicative_3138_);
v___x_3164_ = lean_box(0);
v___x_3165_ = lean_apply_2(v_toPure_3163_, lean_box(0), v___x_3164_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3166_, lean_object* v_inst_3167_, lean_object* v_toBind_3168_, lean_object* v_a_3169_, lean_object* v_inst_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3166_, v_inst_3167_, v_toBind_3168_, v_a_3169_, v_inst_3170_, v_a_3171_);
lean_dec(v_a_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3173_, lean_object* v_inst_3174_, lean_object* v_inst_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v_toApplicative_3177_; lean_object* v_toBind_3178_; lean_object* v___f_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_toApplicative_3177_ = lean_ctor_get(v_inst_3173_, 0);
lean_inc_ref(v_toApplicative_3177_);
v_toBind_3178_ = lean_ctor_get(v_inst_3173_, 1);
lean_inc_n(v_toBind_3178_, 2);
lean_dec_ref(v_inst_3173_);
lean_inc_n(v_a_3176_, 2);
lean_inc(v_inst_3174_);
v___f_3179_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3179_, 0, v_toApplicative_3177_);
lean_closure_set(v___f_3179_, 1, v_inst_3174_);
lean_closure_set(v___f_3179_, 2, v_toBind_3178_);
lean_closure_set(v___f_3179_, 3, v_a_3176_);
lean_closure_set(v___f_3179_, 4, v_inst_3175_);
v___x_3180_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3180_, 0, lean_box(0));
lean_closure_set(v___x_3180_, 1, lean_box(0));
lean_closure_set(v___x_3180_, 2, v_a_3176_);
v___x_3181_ = lean_apply_2(v_inst_3174_, lean_box(0), v___x_3180_);
v___x_3182_ = lean_apply_4(v_toBind_3178_, lean_box(0), lean_box(0), v___x_3181_, v___f_3179_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3183_, v_inst_3184_, v_inst_3185_, v_a_3186_);
lean_dec(v_a_3186_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3188_, lean_object* v_00_u03b1_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3190_, v_inst_3191_, v_inst_3192_, v_a_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3195_, lean_object* v_00_u03b1_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3195_, v_00_u03b1_3196_, v_inst_3197_, v_inst_3198_, v_inst_3199_, v_a_3200_);
lean_dec(v_a_3200_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3202_){
_start:
{
lean_object* v___x_3204_; lean_object* v_producers_3205_; lean_object* v_consumers_3206_; lean_object* v_capacity_3207_; lean_object* v_buf_3208_; lean_object* v_bufCount_3209_; lean_object* v_sendIdx_3210_; lean_object* v_recvIdx_3211_; uint8_t v_closed_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3244_; 
v___x_3204_ = lean_st_ref_get(v_a_3202_);
v_producers_3205_ = lean_ctor_get(v___x_3204_, 0);
v_consumers_3206_ = lean_ctor_get(v___x_3204_, 1);
v_capacity_3207_ = lean_ctor_get(v___x_3204_, 2);
v_buf_3208_ = lean_ctor_get(v___x_3204_, 3);
v_bufCount_3209_ = lean_ctor_get(v___x_3204_, 4);
v_sendIdx_3210_ = lean_ctor_get(v___x_3204_, 5);
v_recvIdx_3211_ = lean_ctor_get(v___x_3204_, 6);
v_closed_3212_ = lean_ctor_get_uint8(v___x_3204_, sizeof(void*)*7);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3214_ = v___x_3204_;
v_isShared_3215_ = v_isSharedCheck_3244_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_recvIdx_3211_);
lean_inc(v_sendIdx_3210_);
lean_inc(v_bufCount_3209_);
lean_inc(v_buf_3208_);
lean_inc(v_capacity_3207_);
lean_inc(v_consumers_3206_);
lean_inc(v_producers_3205_);
lean_dec(v___x_3204_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3244_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3216_ = lean_unsigned_to_nat(0u);
v___x_3217_ = lean_nat_dec_eq(v_bufCount_3209_, v___x_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v_st_3222_; lean_object* v___y_3223_; uint8_t v___x_3225_; lean_object* v___y_3227_; lean_object* v___x_3240_; lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3218_ = lean_array_fget_borrowed(v_buf_3208_, v_recvIdx_3211_);
v___x_3219_ = lean_box(0);
v___x_3220_ = lean_st_ref_swap(v___x_3218_, v___x_3219_);
v___x_3225_ = 1;
v___x_3240_ = lean_unsigned_to_nat(1u);
v___x_3241_ = lean_nat_add(v_recvIdx_3211_, v___x_3240_);
lean_dec(v_recvIdx_3211_);
v___x_3242_ = lean_nat_dec_eq(v___x_3241_, v_capacity_3207_);
if (v___x_3242_ == 0)
{
v___y_3227_ = v___x_3241_;
goto v___jp_3226_;
}
else
{
lean_dec(v___x_3241_);
v___y_3227_ = v___x_3216_;
goto v___jp_3226_;
}
v___jp_3221_:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_st_ref_set(v___y_3223_, v_st_3222_);
return v___x_3220_;
}
v___jp_3226_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = lean_nat_sub(v_bufCount_3209_, v___x_3228_);
lean_dec(v_bufCount_3209_);
lean_inc(v___y_3227_);
lean_inc(v_sendIdx_3210_);
lean_inc(v___x_3229_);
lean_inc_ref(v_buf_3208_);
lean_inc(v_capacity_3207_);
lean_inc_ref(v_consumers_3206_);
lean_inc_ref(v_producers_3205_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 6, v___y_3227_);
lean_ctor_set(v___x_3214_, 4, v___x_3229_);
v___x_3231_ = v___x_3214_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_producers_3205_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_consumers_3206_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_capacity_3207_);
lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_buf_3208_);
lean_ctor_set(v_reuseFailAlloc_3239_, 4, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3239_, 5, v_sendIdx_3210_);
lean_ctor_set(v_reuseFailAlloc_3239_, 6, v___y_3227_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*7, v_closed_3212_);
v___x_3231_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3205_);
if (lean_obj_tag(v___x_3232_) == 1)
{
lean_object* v_val_3233_; lean_object* v_fst_3234_; lean_object* v_snd_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_dec_ref(v___x_3231_);
v_val_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_val_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v_fst_3234_ = lean_ctor_get(v_val_3233_, 0);
lean_inc(v_fst_3234_);
v_snd_3235_ = lean_ctor_get(v_val_3233_, 1);
lean_inc(v_snd_3235_);
lean_dec(v_val_3233_);
v___x_3236_ = lean_box(v___x_3225_);
v___x_3237_ = lean_io_promise_resolve(v___x_3236_, v_fst_3234_);
lean_dec(v_fst_3234_);
v___x_3238_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3238_, 0, v_snd_3235_);
lean_ctor_set(v___x_3238_, 1, v_consumers_3206_);
lean_ctor_set(v___x_3238_, 2, v_capacity_3207_);
lean_ctor_set(v___x_3238_, 3, v_buf_3208_);
lean_ctor_set(v___x_3238_, 4, v___x_3229_);
lean_ctor_set(v___x_3238_, 5, v_sendIdx_3210_);
lean_ctor_set(v___x_3238_, 6, v___y_3227_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*7, v_closed_3212_);
v_st_3222_ = v___x_3238_;
v___y_3223_ = v_a_3202_;
goto v___jp_3221_;
}
else
{
lean_dec(v___x_3232_);
lean_dec(v___x_3229_);
lean_dec(v___y_3227_);
lean_dec(v_sendIdx_3210_);
lean_dec_ref(v_buf_3208_);
lean_dec(v_capacity_3207_);
lean_dec_ref(v_consumers_3206_);
v_st_3222_ = v___x_3231_;
v___y_3223_ = v_a_3202_;
goto v___jp_3221_;
}
}
}
}
else
{
lean_object* v___x_3243_; 
lean_del_object(v___x_3214_);
lean_dec(v_recvIdx_3211_);
lean_dec(v_sendIdx_3210_);
lean_dec(v_bufCount_3209_);
lean_dec_ref(v_buf_3208_);
lean_dec(v_capacity_3207_);
lean_dec_ref(v_consumers_3206_);
lean_dec_ref(v_producers_3205_);
v___x_3243_ = lean_box(0);
return v___x_3243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3245_);
lean_dec(v_a_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3252_, lean_object* v_a_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3252_, v_a_3253_);
lean_dec(v_a_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3257_){
_start:
{
lean_object* v___f_3259_; lean_object* v___x_3260_; 
v___f_3259_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3260_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3257_, v___f_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3264_, lean_object* v_ch_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3265_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3268_, lean_object* v_ch_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3268_, v_ch_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; 
v___x_3275_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3273_);
if (lean_obj_tag(v___x_3275_) == 1)
{
lean_object* v___x_3276_; 
lean_dec_ref(v___f_3272_);
v___x_3276_ = lean_task_pure(v___x_3275_);
return v___x_3276_;
}
else
{
lean_object* v___x_3277_; uint8_t v_closed_3278_; 
lean_dec(v___x_3275_);
v___x_3277_ = lean_st_ref_get(v___y_3273_);
v_closed_3278_ = lean_ctor_get_uint8(v___x_3277_, sizeof(void*)*7);
lean_dec(v___x_3277_);
if (v_closed_3278_ == 0)
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v_producers_3281_; lean_object* v_consumers_3282_; lean_object* v_capacity_3283_; lean_object* v_buf_3284_; lean_object* v_bufCount_3285_; lean_object* v_sendIdx_3286_; lean_object* v_recvIdx_3287_; uint8_t v_closed_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3302_; 
v___x_3279_ = lean_io_promise_new();
v___x_3280_ = lean_st_ref_take(v___y_3273_);
v_producers_3281_ = lean_ctor_get(v___x_3280_, 0);
v_consumers_3282_ = lean_ctor_get(v___x_3280_, 1);
v_capacity_3283_ = lean_ctor_get(v___x_3280_, 2);
v_buf_3284_ = lean_ctor_get(v___x_3280_, 3);
v_bufCount_3285_ = lean_ctor_get(v___x_3280_, 4);
v_sendIdx_3286_ = lean_ctor_get(v___x_3280_, 5);
v_recvIdx_3287_ = lean_ctor_get(v___x_3280_, 6);
v_closed_3288_ = lean_ctor_get_uint8(v___x_3280_, sizeof(void*)*7);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3290_ = v___x_3280_;
v_isShared_3291_ = v_isSharedCheck_3302_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_recvIdx_3287_);
lean_inc(v_sendIdx_3286_);
lean_inc(v_bufCount_3285_);
lean_inc(v_buf_3284_);
lean_inc(v_capacity_3283_);
lean_inc(v_consumers_3282_);
lean_inc(v_producers_3281_);
lean_dec(v___x_3280_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3302_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3292_ = lean_box(0);
lean_inc(v___x_3279_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3279_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = l_Std_Queue_enqueue___redArg(v___x_3293_, v_consumers_3282_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 1, v___x_3294_);
v___x_3296_ = v___x_3290_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_producers_3281_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_capacity_3283_);
lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_buf_3284_);
lean_ctor_set(v_reuseFailAlloc_3301_, 4, v_bufCount_3285_);
lean_ctor_set(v_reuseFailAlloc_3301_, 5, v_sendIdx_3286_);
lean_ctor_set(v_reuseFailAlloc_3301_, 6, v_recvIdx_3287_);
lean_ctor_set_uint8(v_reuseFailAlloc_3301_, sizeof(void*)*7, v_closed_3288_);
v___x_3296_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3297_ = lean_st_ref_set(v___y_3273_, v___x_3296_);
v___x_3298_ = lean_io_promise_result_opt(v___x_3279_);
lean_dec(v___x_3279_);
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = lean_io_bind_task(v___x_3298_, v___f_3272_, v___x_3299_, v_closed_3278_);
return v___x_3300_;
}
}
}
else
{
lean_object* v___x_3303_; 
lean_dec_ref(v___f_3272_);
v___x_3303_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3304_, v___y_3305_);
lean_dec(v___y_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3308_, lean_object* v_res_3309_){
_start:
{
if (lean_obj_tag(v_res_3309_) == 0)
{
lean_dec_ref(v_ch_3308_);
goto v___jp_3311_;
}
else
{
lean_object* v_val_3313_; uint8_t v___x_3314_; 
v_val_3313_ = lean_ctor_get(v_res_3309_, 0);
v___x_3314_ = lean_unbox(v_val_3313_);
if (v___x_3314_ == 0)
{
lean_dec_ref(v_ch_3308_);
goto v___jp_3311_;
}
else
{
lean_object* v___x_3315_; 
v___x_3315_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3308_);
return v___x_3315_;
}
}
v___jp_3311_:
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3316_, lean_object* v_res_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3316_, v_res_3317_);
lean_dec(v_res_3317_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3320_){
_start:
{
lean_object* v___f_3322_; lean_object* v___f_3323_; lean_object* v___x_3324_; 
lean_inc_ref(v_ch_3320_);
v___f_3322_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3322_, 0, v_ch_3320_);
v___f_3323_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3323_, 0, v___f_3322_);
v___x_3324_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3320_, v___f_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3328_, lean_object* v_ch_3329_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3329_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3332_, lean_object* v_ch_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3332_, v_ch_3333_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3336_, lean_object* v_a_3337_){
_start:
{
uint8_t v___y_3339_; lean_object* v_bufCount_3343_; uint8_t v_closed_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; 
v_bufCount_3343_ = lean_ctor_get(v_a_3337_, 4);
v_closed_3344_ = lean_ctor_get_uint8(v_a_3337_, sizeof(void*)*7);
v___x_3345_ = lean_unsigned_to_nat(0u);
v___x_3346_ = lean_nat_dec_eq(v_bufCount_3343_, v___x_3345_);
v___x_3347_ = lean_bool_not(v___x_3346_);
if (v___x_3347_ == 0)
{
v___y_3339_ = v_closed_3344_;
goto v___jp_3338_;
}
else
{
v___y_3339_ = v___x_3347_;
goto v___jp_3338_;
}
v___jp_3338_:
{
lean_object* v_toPure_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_toPure_3340_ = lean_ctor_get(v_toApplicative_3336_, 1);
lean_inc(v_toPure_3340_);
lean_dec_ref(v_toApplicative_3336_);
v___x_3341_ = lean_box(v___y_3339_);
v___x_3342_ = lean_apply_2(v_toPure_3340_, lean_box(0), v___x_3341_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3348_, v_a_3349_);
lean_dec_ref(v_a_3349_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3351_, lean_object* v_inst_3352_, lean_object* v_a_3353_){
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3360_, lean_object* v_inst_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3360_, v_inst_3361_, v_a_3362_);
lean_dec(v_a_3362_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3364_, lean_object* v_00_u03b1_3365_, lean_object* v_inst_3366_, lean_object* v_inst_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_toApplicative_3369_; lean_object* v_toBind_3370_; lean_object* v___f_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_toApplicative_3369_ = lean_ctor_get(v_inst_3366_, 0);
lean_inc_ref(v_toApplicative_3369_);
v_toBind_3370_ = lean_ctor_get(v_inst_3366_, 1);
lean_inc(v_toBind_3370_);
lean_dec_ref(v_inst_3366_);
v___f_3371_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3371_, 0, v_toApplicative_3369_);
lean_inc(v_a_3368_);
v___x_3372_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3372_, 0, lean_box(0));
lean_closure_set(v___x_3372_, 1, lean_box(0));
lean_closure_set(v___x_3372_, 2, v_a_3368_);
v___x_3373_ = lean_apply_2(v_inst_3367_, lean_box(0), v___x_3372_);
v___x_3374_ = lean_apply_4(v_toBind_3370_, lean_box(0), lean_box(0), v___x_3373_, v___f_3371_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3375_, lean_object* v_00_u03b1_3376_, lean_object* v_inst_3377_, lean_object* v_inst_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3375_, v_00_u03b1_3376_, v_inst_3377_, v_inst_3378_, v_a_3379_);
lean_dec(v_a_3379_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3383_; lean_object* v_producers_3384_; lean_object* v_consumers_3385_; lean_object* v_capacity_3386_; lean_object* v_buf_3387_; lean_object* v_bufCount_3388_; lean_object* v_sendIdx_3389_; lean_object* v_recvIdx_3390_; uint8_t v_closed_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3425_; 
v___x_3383_ = lean_st_ref_get(v_a_3381_);
v_producers_3384_ = lean_ctor_get(v___x_3383_, 0);
v_consumers_3385_ = lean_ctor_get(v___x_3383_, 1);
v_capacity_3386_ = lean_ctor_get(v___x_3383_, 2);
v_buf_3387_ = lean_ctor_get(v___x_3383_, 3);
v_bufCount_3388_ = lean_ctor_get(v___x_3383_, 4);
v_sendIdx_3389_ = lean_ctor_get(v___x_3383_, 5);
v_recvIdx_3390_ = lean_ctor_get(v___x_3383_, 6);
v_closed_3391_ = lean_ctor_get_uint8(v___x_3383_, sizeof(void*)*7);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3393_ = v___x_3383_;
v_isShared_3394_ = v_isSharedCheck_3425_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_recvIdx_3390_);
lean_inc(v_sendIdx_3389_);
lean_inc(v_bufCount_3388_);
lean_inc(v_buf_3387_);
lean_inc(v_capacity_3386_);
lean_inc(v_consumers_3385_);
lean_inc(v_producers_3384_);
lean_dec(v___x_3383_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3425_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = lean_nat_dec_eq(v_bufCount_3388_, v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v_st_3401_; lean_object* v___y_3402_; uint8_t v___x_3405_; lean_object* v___y_3407_; lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3397_ = lean_array_fget_borrowed(v_buf_3387_, v_recvIdx_3390_);
v___x_3398_ = lean_box(0);
v___x_3399_ = lean_st_ref_swap(v___x_3397_, v___x_3398_);
v___x_3405_ = 1;
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_add(v_recvIdx_3390_, v___x_3420_);
lean_dec(v_recvIdx_3390_);
v___x_3422_ = lean_nat_dec_eq(v___x_3421_, v_capacity_3386_);
if (v___x_3422_ == 0)
{
v___y_3407_ = v___x_3421_;
goto v___jp_3406_;
}
else
{
lean_dec(v___x_3421_);
v___y_3407_ = v___x_3395_;
goto v___jp_3406_;
}
v___jp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_st_ref_set(v___y_3402_, v_st_3401_);
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3399_);
return v___x_3404_;
}
v___jp_3406_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3408_ = lean_unsigned_to_nat(1u);
v___x_3409_ = lean_nat_sub(v_bufCount_3388_, v___x_3408_);
lean_dec(v_bufCount_3388_);
lean_inc(v___y_3407_);
lean_inc(v_sendIdx_3389_);
lean_inc(v___x_3409_);
lean_inc_ref(v_buf_3387_);
lean_inc(v_capacity_3386_);
lean_inc_ref(v_consumers_3385_);
lean_inc_ref(v_producers_3384_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 6, v___y_3407_);
lean_ctor_set(v___x_3393_, 4, v___x_3409_);
v___x_3411_ = v___x_3393_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_producers_3384_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_consumers_3385_);
lean_ctor_set(v_reuseFailAlloc_3419_, 2, v_capacity_3386_);
lean_ctor_set(v_reuseFailAlloc_3419_, 3, v_buf_3387_);
lean_ctor_set(v_reuseFailAlloc_3419_, 4, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3419_, 5, v_sendIdx_3389_);
lean_ctor_set(v_reuseFailAlloc_3419_, 6, v___y_3407_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*7, v_closed_3391_);
v___x_3411_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3384_);
if (lean_obj_tag(v___x_3412_) == 1)
{
lean_object* v_val_3413_; lean_object* v_fst_3414_; lean_object* v_snd_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref(v___x_3411_);
v_val_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_val_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v_fst_3414_ = lean_ctor_get(v_val_3413_, 0);
lean_inc(v_fst_3414_);
v_snd_3415_ = lean_ctor_get(v_val_3413_, 1);
lean_inc(v_snd_3415_);
lean_dec(v_val_3413_);
v___x_3416_ = lean_box(v___x_3405_);
v___x_3417_ = lean_io_promise_resolve(v___x_3416_, v_fst_3414_);
lean_dec(v_fst_3414_);
v___x_3418_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3418_, 0, v_snd_3415_);
lean_ctor_set(v___x_3418_, 1, v_consumers_3385_);
lean_ctor_set(v___x_3418_, 2, v_capacity_3386_);
lean_ctor_set(v___x_3418_, 3, v_buf_3387_);
lean_ctor_set(v___x_3418_, 4, v___x_3409_);
lean_ctor_set(v___x_3418_, 5, v_sendIdx_3389_);
lean_ctor_set(v___x_3418_, 6, v___y_3407_);
lean_ctor_set_uint8(v___x_3418_, sizeof(void*)*7, v_closed_3391_);
v_st_3401_ = v___x_3418_;
v___y_3402_ = v_a_3381_;
goto v___jp_3400_;
}
else
{
lean_dec(v___x_3412_);
lean_dec(v___x_3409_);
lean_dec(v___y_3407_);
lean_dec(v_sendIdx_3389_);
lean_dec_ref(v_buf_3387_);
lean_dec(v_capacity_3386_);
lean_dec_ref(v_consumers_3385_);
v_st_3401_ = v___x_3411_;
v___y_3402_ = v_a_3381_;
goto v___jp_3400_;
}
}
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_del_object(v___x_3393_);
lean_dec(v_recvIdx_3390_);
lean_dec(v_sendIdx_3389_);
lean_dec(v_bufCount_3388_);
lean_dec_ref(v_buf_3387_);
lean_dec(v_capacity_3386_);
lean_dec_ref(v_consumers_3385_);
lean_dec_ref(v_producers_3384_);
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3426_);
lean_dec(v_a_3426_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3429_, lean_object* v_a_3430_){
_start:
{
lean_object* v___x_3432_; 
v___x_3432_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3430_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3433_, lean_object* v_a_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3433_, v_a_3434_);
lean_dec(v_a_3434_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3437_, lean_object* v_lose_3438_){
_start:
{
lean_object* v_finished_3440_; lean_object* v_promise_3441_; lean_object* v___x_3442_; uint8_t v___y_3444_; uint8_t v___x_3452_; 
v_finished_3440_ = lean_ctor_get(v_w_3437_, 0);
v_promise_3441_ = lean_ctor_get(v_w_3437_, 1);
v___x_3442_ = lean_st_ref_take(v_finished_3440_);
v___x_3452_ = lean_unbox(v___x_3442_);
lean_dec(v___x_3442_);
if (v___x_3452_ == 0)
{
uint8_t v___x_3453_; 
v___x_3453_ = 1;
v___y_3444_ = v___x_3453_;
goto v___jp_3443_;
}
else
{
uint8_t v___x_3454_; 
v___x_3454_ = 0;
v___y_3444_ = v___x_3454_;
goto v___jp_3443_;
}
v___jp_3443_:
{
uint8_t v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = 1;
v___x_3446_ = lean_box(v___x_3445_);
v___x_3447_ = lean_st_ref_set(v_finished_3440_, v___x_3446_);
if (v___y_3444_ == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_apply_1(v_lose_3438_, lean_box(0));
return v___x_3448_;
}
else
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec_ref(v_lose_3438_);
v___x_3449_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0));
v___x_3450_ = lean_io_promise_resolve(v___x_3449_, v_promise_3441_);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3455_, lean_object* v_lose_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3455_, v_lose_3456_);
lean_dec_ref(v_w_3455_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3459_, lean_object* v_w_3460_, lean_object* v_lose_3461_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3460_, v_lose_3461_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3464_, lean_object* v_w_3465_, lean_object* v_lose_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3464_, v_w_3465_, v_lose_3466_);
lean_dec_ref(v_w_3465_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3469_, lean_object* v_lose_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v_finished_3473_; lean_object* v_promise_3474_; lean_object* v___x_3475_; uint8_t v___y_3477_; uint8_t v___x_3493_; 
v_finished_3473_ = lean_ctor_get(v_w_3469_, 0);
v_promise_3474_ = lean_ctor_get(v_w_3469_, 1);
v___x_3475_ = lean_st_ref_take(v_finished_3473_);
v___x_3493_ = lean_unbox(v___x_3475_);
lean_dec(v___x_3475_);
if (v___x_3493_ == 0)
{
uint8_t v___x_3494_; 
v___x_3494_ = 1;
v___y_3477_ = v___x_3494_;
goto v___jp_3476_;
}
else
{
uint8_t v___x_3495_; 
v___x_3495_ = 0;
v___y_3477_ = v___x_3495_;
goto v___jp_3476_;
}
v___jp_3476_:
{
uint8_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = 1;
v___x_3479_ = lean_box(v___x_3478_);
v___x_3480_ = lean_st_ref_set(v_finished_3473_, v___x_3479_);
if (v___y_3477_ == 0)
{
lean_object* v___x_3481_; 
lean_inc(v___y_3471_);
v___x_3481_ = lean_apply_2(v_lose_3470_, v___y_3471_, lean_box(0));
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v_lose_3470_);
v___x_3482_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3471_);
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3492_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3492_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_a_3483_);
v___x_3488_ = lean_io_promise_resolve(v___x_3487_, v_promise_3474_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3488_);
v___x_3490_ = v___x_3485_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3496_, lean_object* v_lose_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3496_, v_lose_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v_w_3496_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3501_, lean_object* v_w_3502_, lean_object* v_lose_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v___x_3506_; 
v___x_3506_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3502_, v_lose_3503_, v___y_3504_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3507_, lean_object* v_w_3508_, lean_object* v_lose_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3507_, v_w_3508_, v_lose_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v_w_3508_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3513_, lean_object* v_k_3514_){
_start:
{
lean_object* v_ref_3516_; lean_object* v_mutex_3517_; lean_object* v___x_3518_; lean_object* v_r_3519_; 
v_ref_3516_ = lean_ctor_get(v_mutex_3513_, 0);
lean_inc(v_ref_3516_);
v_mutex_3517_ = lean_ctor_get(v_mutex_3513_, 1);
lean_inc(v_mutex_3517_);
lean_dec_ref(v_mutex_3513_);
v___x_3518_ = lean_io_basemutex_lock(v_mutex_3517_);
v_r_3519_ = lean_apply_2(v_k_3514_, v_ref_3516_, lean_box(0));
if (lean_obj_tag(v_r_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3528_; 
v_a_3520_ = lean_ctor_get(v_r_3519_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_r_3519_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3522_ = v_r_3519_;
v_isShared_3523_ = v_isSharedCheck_3528_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v_r_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3528_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3524_ = lean_io_basemutex_unlock(v_mutex_3517_);
lean_dec(v_mutex_3517_);
if (v_isShared_3523_ == 0)
{
v___x_3526_ = v___x_3522_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3520_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3537_; 
v_a_3529_ = lean_ctor_get(v_r_3519_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_r_3519_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3531_ = v_r_3519_;
v_isShared_3532_ = v_isSharedCheck_3537_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v_r_3519_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3537_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = lean_io_basemutex_unlock(v_mutex_3517_);
lean_dec(v_mutex_3517_);
if (v_isShared_3532_ == 0)
{
v___x_3535_ = v___x_3531_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3529_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3538_, lean_object* v_k_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3538_, v_k_3539_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3542_, lean_object* v_00_u03b2_3543_, lean_object* v_mutex_3544_, lean_object* v_k_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3544_, v_k_3545_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3548_, lean_object* v_00_u03b2_3549_, lean_object* v_mutex_3550_, lean_object* v_k_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3548_, v_00_u03b2_3549_, v_mutex_3550_, v_k_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3554_){
_start:
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3554_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3557_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; lean_object* v_producers_3564_; lean_object* v_consumers_3565_; lean_object* v_capacity_3566_; lean_object* v_buf_3567_; lean_object* v_bufCount_3568_; lean_object* v_sendIdx_3569_; lean_object* v_recvIdx_3570_; uint8_t v_closed_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3593_; 
v___x_3563_ = lean_st_ref_get(v___y_3561_);
v_producers_3564_ = lean_ctor_get(v___x_3563_, 0);
v_consumers_3565_ = lean_ctor_get(v___x_3563_, 1);
v_capacity_3566_ = lean_ctor_get(v___x_3563_, 2);
v_buf_3567_ = lean_ctor_get(v___x_3563_, 3);
v_bufCount_3568_ = lean_ctor_get(v___x_3563_, 4);
v_sendIdx_3569_ = lean_ctor_get(v___x_3563_, 5);
v_recvIdx_3570_ = lean_ctor_get(v___x_3563_, 6);
v_closed_3571_ = lean_ctor_get_uint8(v___x_3563_, sizeof(void*)*7);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3573_ = v___x_3563_;
v_isShared_3574_ = v_isSharedCheck_3593_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_recvIdx_3570_);
lean_inc(v_sendIdx_3569_);
lean_inc(v_bufCount_3568_);
lean_inc(v_buf_3567_);
lean_inc(v_capacity_3566_);
lean_inc(v_consumers_3565_);
lean_inc(v_producers_3564_);
lean_dec(v___x_3563_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3593_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3565_);
if (lean_obj_tag(v___x_3575_) == 1)
{
lean_object* v_val_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3590_; 
v_val_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3590_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_val_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3590_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v_fst_3580_; lean_object* v_snd_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
v_fst_3580_ = lean_ctor_get(v_val_3576_, 0);
lean_inc(v_fst_3580_);
v_snd_3581_ = lean_ctor_get(v_val_3576_, 1);
lean_inc(v_snd_3581_);
lean_dec(v_val_3576_);
v___x_3582_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3580_, v_____do__lift_3560_);
lean_dec(v_fst_3580_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v_snd_3581_);
v___x_3584_ = v___x_3573_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_producers_3564_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_snd_3581_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_capacity_3566_);
lean_ctor_set(v_reuseFailAlloc_3589_, 3, v_buf_3567_);
lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_bufCount_3568_);
lean_ctor_set(v_reuseFailAlloc_3589_, 5, v_sendIdx_3569_);
lean_ctor_set(v_reuseFailAlloc_3589_, 6, v_recvIdx_3570_);
lean_ctor_set_uint8(v_reuseFailAlloc_3589_, sizeof(void*)*7, v_closed_3571_);
v___x_3584_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3587_; 
v___x_3585_ = lean_st_ref_set(v___y_3561_, v___x_3584_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set_tag(v___x_3578_, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3585_);
v___x_3587_ = v___x_3578_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
lean_dec(v___x_3575_);
lean_del_object(v___x_3573_);
lean_dec(v_recvIdx_3570_);
lean_dec(v_sendIdx_3569_);
lean_dec(v_bufCount_3568_);
lean_dec_ref(v_buf_3567_);
lean_dec(v_capacity_3566_);
lean_dec_ref(v_producers_3564_);
v___x_3591_ = lean_box(0);
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
return v___x_3592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
uint8_t v_____do__lift_3921__boxed_3597_; lean_object* v_res_3598_; 
v_____do__lift_3921__boxed_3597_ = lean_unbox(v_____do__lift_3594_);
v_res_3598_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3921__boxed_3597_, v___y_3595_);
lean_dec(v___y_3595_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3599_, lean_object* v___f_3600_, uint8_t v_____do__lift_3601_, lean_object* v___y_3602_){
_start:
{
if (v_____do__lift_3601_ == 0)
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v_producers_3606_; lean_object* v_consumers_3607_; lean_object* v_capacity_3608_; lean_object* v_buf_3609_; lean_object* v_bufCount_3610_; lean_object* v_sendIdx_3611_; lean_object* v_recvIdx_3612_; uint8_t v_closed_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3627_; 
v___x_3604_ = lean_io_promise_new();
v___x_3605_ = lean_st_ref_take(v___y_3602_);
v_producers_3606_ = lean_ctor_get(v___x_3605_, 0);
v_consumers_3607_ = lean_ctor_get(v___x_3605_, 1);
v_capacity_3608_ = lean_ctor_get(v___x_3605_, 2);
v_buf_3609_ = lean_ctor_get(v___x_3605_, 3);
v_bufCount_3610_ = lean_ctor_get(v___x_3605_, 4);
v_sendIdx_3611_ = lean_ctor_get(v___x_3605_, 5);
v_recvIdx_3612_ = lean_ctor_get(v___x_3605_, 6);
v_closed_3613_ = lean_ctor_get_uint8(v___x_3605_, sizeof(void*)*7);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3615_ = v___x_3605_;
v_isShared_3616_ = v_isSharedCheck_3627_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_recvIdx_3612_);
lean_inc(v_sendIdx_3611_);
lean_inc(v_bufCount_3610_);
lean_inc(v_buf_3609_);
lean_inc(v_capacity_3608_);
lean_inc(v_consumers_3607_);
lean_inc(v_producers_3606_);
lean_dec(v___x_3605_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3627_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
v___x_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3617_, 0, v_waiter_3599_);
lean_inc(v___x_3604_);
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3604_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = l_Std_Queue_enqueue___redArg(v___x_3618_, v_consumers_3607_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 1, v___x_3619_);
v___x_3621_ = v___x_3615_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_producers_3606_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_capacity_3608_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_buf_3609_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_bufCount_3610_);
lean_ctor_set(v_reuseFailAlloc_3626_, 5, v_sendIdx_3611_);
lean_ctor_set(v_reuseFailAlloc_3626_, 6, v_recvIdx_3612_);
lean_ctor_set_uint8(v_reuseFailAlloc_3626_, sizeof(void*)*7, v_closed_3613_);
v___x_3621_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3622_ = lean_st_ref_set(v___y_3602_, v___x_3621_);
v___x_3623_ = lean_io_promise_result_opt(v___x_3604_);
lean_dec(v___x_3604_);
v___x_3624_ = lean_unsigned_to_nat(0u);
v___x_3625_ = l_EIO_chainTask___redArg(v___x_3623_, v___f_3600_, v___x_3624_, v_____do__lift_3601_);
return v___x_3625_;
}
}
}
else
{
lean_object* v___x_3628_; lean_object* v_lose_3629_; lean_object* v___x_3630_; 
lean_dec_ref(v___f_3600_);
v___x_3628_ = lean_box(v_____do__lift_3601_);
v_lose_3629_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3629_, 0, v___x_3628_);
v___x_3630_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3599_, v_lose_3629_, v___y_3602_);
lean_dec_ref(v_waiter_3599_);
return v___x_3630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3631_, lean_object* v___f_3632_, lean_object* v_____do__lift_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
uint8_t v_____do__lift_3977__boxed_3636_; lean_object* v_res_3637_; 
v_____do__lift_3977__boxed_3636_ = lean_unbox(v_____do__lift_3633_);
v_res_3637_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3631_, v___f_3632_, v_____do__lift_3977__boxed_3636_, v___y_3634_);
lean_dec(v___y_3634_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; lean_object* v_bufCount_3642_; uint8_t v_closed_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; uint8_t v___x_3646_; 
v___x_3641_ = lean_st_ref_get(v___y_3639_);
v_bufCount_3642_ = lean_ctor_get(v___x_3641_, 4);
lean_inc(v_bufCount_3642_);
v_closed_3643_ = lean_ctor_get_uint8(v___x_3641_, sizeof(void*)*7);
lean_dec(v___x_3641_);
v___x_3644_ = lean_unsigned_to_nat(0u);
v___x_3645_ = lean_nat_dec_eq(v_bufCount_3642_, v___x_3644_);
lean_dec(v_bufCount_3642_);
v___x_3646_ = lean_bool_not(v___x_3645_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_box(v_closed_3643_);
lean_inc(v___y_3639_);
v___x_3648_ = lean_apply_3(v___f_3638_, v___x_3647_, v___y_3639_, lean_box(0));
return v___x_3648_;
}
else
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = lean_box(v___x_3646_);
lean_inc(v___y_3639_);
v___x_3650_ = lean_apply_3(v___f_3638_, v___x_3649_, v___y_3639_, lean_box(0));
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3651_, v___y_3652_);
lean_dec(v___y_3652_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3657_, lean_object* v_ch_3658_, lean_object* v_x_3659_){
_start:
{
if (lean_obj_tag(v_x_3659_) == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
lean_dec_ref(v_ch_3658_);
lean_dec_ref(v_waiter_3657_);
v___x_3661_ = lean_box(0);
v___x_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
return v___x_3662_;
}
else
{
lean_object* v_val_3663_; uint8_t v___x_3664_; 
v_val_3663_ = lean_ctor_get(v_x_3659_, 0);
v___x_3664_ = lean_unbox(v_val_3663_);
if (v___x_3664_ == 0)
{
lean_object* v___f_3665_; lean_object* v___x_3666_; 
lean_dec_ref(v_ch_3658_);
v___f_3665_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3666_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3657_, v___f_3665_);
lean_dec_ref(v_waiter_3657_);
return v___x_3666_;
}
else
{
lean_object* v___x_3667_; 
v___x_3667_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3658_, v_waiter_3657_);
return v___x_3667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3668_, lean_object* v_ch_3669_, lean_object* v_x_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3668_, v_ch_3669_, v_x_3670_);
lean_dec(v_x_3670_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3673_, lean_object* v_waiter_3674_){
_start:
{
lean_object* v___f_3676_; lean_object* v___f_3677_; lean_object* v___f_3678_; lean_object* v___x_3679_; 
lean_inc_ref(v_ch_3673_);
lean_inc_ref(v_waiter_3674_);
v___f_3676_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3676_, 0, v_waiter_3674_);
lean_closure_set(v___f_3676_, 1, v_ch_3673_);
v___f_3677_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3677_, 0, v_waiter_3674_);
lean_closure_set(v___f_3677_, 1, v___f_3676_);
v___f_3678_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3678_, 0, v___f_3677_);
v___x_3679_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3673_, v___f_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3680_, lean_object* v_waiter_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3680_, v_waiter_3681_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3684_, lean_object* v_ch_3685_, lean_object* v_waiter_3686_){
_start:
{
lean_object* v___x_3688_; 
v___x_3688_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3685_, v_waiter_3686_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3689_, lean_object* v_ch_3690_, lean_object* v_waiter_3691_, lean_object* v_a_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3689_, v_ch_3690_, v_waiter_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3694_, lean_object* v_x_3695_){
_start:
{
if (lean_obj_tag(v_x_3695_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3705_; 
lean_dec_ref(v_x_3694_);
v_a_3697_ = lean_ctor_get(v_x_3695_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_x_3695_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3699_ = v_x_3695_;
v_isShared_3700_ = v_isSharedCheck_3705_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v_x_3695_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3705_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
}
}
else
{
lean_object* v___x_3706_; 
lean_dec_ref_known(v_x_3695_, 1);
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v_x_3694_);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3707_, lean_object* v_x_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3707_, v_x_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3711_, uint8_t v___x_3712_, lean_object* v___f_3713_, lean_object* v_____r_3714_, lean_object* v_st_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3718_ = lean_st_ref_set(v___y_3716_, v_st_3715_);
v___x_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
v___x_3721_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3711_, v___x_3712_, v___x_3720_, v___f_3713_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3722_, lean_object* v___x_3723_, lean_object* v___f_3724_, lean_object* v_____r_3725_, lean_object* v_st_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
uint8_t v___x_6357__boxed_3729_; lean_object* v_res_3730_; 
v___x_6357__boxed_3729_ = lean_unbox(v___x_3723_);
v_res_3730_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3722_, v___x_6357__boxed_3729_, v___f_3724_, v_____r_3725_, v_st_3726_, v___y_3727_);
lean_dec(v___y_3727_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3731_, lean_object* v_consumers_3732_, lean_object* v_capacity_3733_, lean_object* v_buf_3734_, lean_object* v___x_3735_, lean_object* v_sendIdx_3736_, lean_object* v___y_3737_, uint8_t v_closed_3738_, lean_object* v___f_3739_, lean_object* v_a_3740_, lean_object* v_x_3741_){
_start:
{
if (lean_obj_tag(v_x_3741_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3751_; 
lean_dec_ref(v___f_3739_);
lean_dec(v___y_3737_);
lean_dec(v_sendIdx_3736_);
lean_dec(v___x_3735_);
lean_dec_ref(v_buf_3734_);
lean_dec(v_capacity_3733_);
lean_dec_ref(v_consumers_3732_);
lean_dec_ref(v_snd_3731_);
v_a_3743_ = lean_ctor_get(v_x_3741_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_x_3741_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3745_ = v_x_3741_;
v_isShared_3746_ = v_isSharedCheck_3751_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v_x_3741_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3751_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
}
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec_ref_known(v_x_3741_, 1);
v___x_3752_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3752_, 0, v_snd_3731_);
lean_ctor_set(v___x_3752_, 1, v_consumers_3732_);
lean_ctor_set(v___x_3752_, 2, v_capacity_3733_);
lean_ctor_set(v___x_3752_, 3, v_buf_3734_);
lean_ctor_set(v___x_3752_, 4, v___x_3735_);
lean_ctor_set(v___x_3752_, 5, v_sendIdx_3736_);
lean_ctor_set(v___x_3752_, 6, v___y_3737_);
lean_ctor_set_uint8(v___x_3752_, sizeof(void*)*7, v_closed_3738_);
v___x_3753_ = lean_box(0);
lean_inc(v_a_3740_);
v___x_3754_ = lean_apply_4(v___f_3739_, v___x_3753_, v___x_3752_, v_a_3740_, lean_box(0));
return v___x_3754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3755_, lean_object* v_consumers_3756_, lean_object* v_capacity_3757_, lean_object* v_buf_3758_, lean_object* v___x_3759_, lean_object* v_sendIdx_3760_, lean_object* v___y_3761_, lean_object* v_closed_3762_, lean_object* v___f_3763_, lean_object* v_a_3764_, lean_object* v_x_3765_, lean_object* v___y_3766_){
_start:
{
uint8_t v_closed_boxed_3767_; lean_object* v_res_3768_; 
v_closed_boxed_3767_ = lean_unbox(v_closed_3762_);
v_res_3768_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3755_, v_consumers_3756_, v_capacity_3757_, v_buf_3758_, v___x_3759_, v_sendIdx_3760_, v___y_3761_, v_closed_boxed_3767_, v___f_3763_, v_a_3764_, v_x_3765_);
lean_dec(v_a_3764_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3769_, uint8_t v___x_3770_, lean_object* v_bufCount_3771_, lean_object* v_producers_3772_, lean_object* v_consumers_3773_, lean_object* v_capacity_3774_, lean_object* v_buf_3775_, lean_object* v_sendIdx_3776_, uint8_t v_closed_3777_, uint8_t v___x_3778_, lean_object* v_a_3779_, lean_object* v_recvIdx_3780_, lean_object* v_x_3781_){
_start:
{
if (lean_obj_tag(v_x_3781_) == 0)
{
lean_object* v___x_3783_; 
lean_dec(v_sendIdx_3776_);
lean_dec_ref(v_buf_3775_);
lean_dec(v_capacity_3774_);
lean_dec_ref(v_consumers_3773_);
lean_dec_ref(v_producers_3772_);
lean_dec(v___x_3769_);
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v_x_3781_);
return v___x_3783_;
}
else
{
lean_object* v___f_3784_; lean_object* v___x_3785_; lean_object* v___f_3786_; lean_object* v___y_3788_; lean_object* v___x_3811_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v___f_3784_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3784_, 0, v_x_3781_);
v___x_3785_ = lean_box(v___x_3770_);
lean_inc_ref(v___f_3784_);
lean_inc(v___x_3769_);
v___f_3786_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3786_, 0, v___x_3769_);
lean_closure_set(v___f_3786_, 1, v___x_3785_);
lean_closure_set(v___f_3786_, 2, v___f_3784_);
v___x_3811_ = lean_unsigned_to_nat(1u);
v___x_3812_ = lean_nat_add(v_recvIdx_3780_, v___x_3811_);
v___x_3813_ = lean_nat_dec_eq(v___x_3812_, v_capacity_3774_);
if (v___x_3813_ == 0)
{
v___y_3788_ = v___x_3812_;
goto v___jp_3787_;
}
else
{
lean_dec(v___x_3812_);
lean_inc(v___x_3769_);
v___y_3788_ = v___x_3769_;
goto v___jp_3787_;
}
v___jp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3789_ = lean_unsigned_to_nat(1u);
v___x_3790_ = lean_nat_sub(v_bufCount_3771_, v___x_3789_);
lean_inc(v___y_3788_);
lean_inc(v_sendIdx_3776_);
lean_inc(v___x_3790_);
lean_inc_ref(v_buf_3775_);
lean_inc(v_capacity_3774_);
lean_inc_ref(v_consumers_3773_);
lean_inc_ref(v_producers_3772_);
v___x_3791_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3791_, 0, v_producers_3772_);
lean_ctor_set(v___x_3791_, 1, v_consumers_3773_);
lean_ctor_set(v___x_3791_, 2, v_capacity_3774_);
lean_ctor_set(v___x_3791_, 3, v_buf_3775_);
lean_ctor_set(v___x_3791_, 4, v___x_3790_);
lean_ctor_set(v___x_3791_, 5, v_sendIdx_3776_);
lean_ctor_set(v___x_3791_, 6, v___y_3788_);
lean_ctor_set_uint8(v___x_3791_, sizeof(void*)*7, v_closed_3777_);
v___x_3792_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3772_);
if (lean_obj_tag(v___x_3792_) == 1)
{
lean_object* v_val_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref_known(v___x_3791_, 7);
lean_dec_ref(v___f_3784_);
v_val_3793_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3795_ = v___x_3792_;
v_isShared_3796_ = v_isSharedCheck_3808_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_val_3793_);
lean_dec(v___x_3792_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3808_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v_fst_3797_; lean_object* v_snd_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___f_3802_; lean_object* v___x_3804_; 
v_fst_3797_ = lean_ctor_get(v_val_3793_, 0);
lean_inc(v_fst_3797_);
v_snd_3798_ = lean_ctor_get(v_val_3793_, 1);
lean_inc(v_snd_3798_);
lean_dec(v_val_3793_);
v___x_3799_ = lean_box(v___x_3778_);
v___x_3800_ = lean_io_promise_resolve(v___x_3799_, v_fst_3797_);
lean_dec(v_fst_3797_);
v___x_3801_ = lean_box(v_closed_3777_);
lean_inc(v_a_3779_);
v___f_3802_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3802_, 0, v_snd_3798_);
lean_closure_set(v___f_3802_, 1, v_consumers_3773_);
lean_closure_set(v___f_3802_, 2, v_capacity_3774_);
lean_closure_set(v___f_3802_, 3, v_buf_3775_);
lean_closure_set(v___f_3802_, 4, v___x_3790_);
lean_closure_set(v___f_3802_, 5, v_sendIdx_3776_);
lean_closure_set(v___f_3802_, 6, v___y_3788_);
lean_closure_set(v___f_3802_, 7, v___x_3801_);
lean_closure_set(v___f_3802_, 8, v___f_3786_);
lean_closure_set(v___f_3802_, 9, v_a_3779_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v___x_3800_);
v___x_3804_ = v___x_3795_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3800_);
v___x_3804_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3805_, 0, v___x_3804_);
v___x_3806_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3769_, v___x_3770_, v___x_3805_, v___f_3802_);
return v___x_3806_;
}
}
}
else
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
lean_dec(v___x_3792_);
lean_dec(v___x_3790_);
lean_dec(v___y_3788_);
lean_dec_ref(v___f_3786_);
lean_dec(v_sendIdx_3776_);
lean_dec_ref(v_buf_3775_);
lean_dec(v_capacity_3774_);
lean_dec_ref(v_consumers_3773_);
v___x_3809_ = lean_box(0);
v___x_3810_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3769_, v___x_3770_, v___f_3784_, v___x_3809_, v___x_3791_, v_a_3779_);
return v___x_3810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3814_, lean_object* v___x_3815_, lean_object* v_bufCount_3816_, lean_object* v_producers_3817_, lean_object* v_consumers_3818_, lean_object* v_capacity_3819_, lean_object* v_buf_3820_, lean_object* v_sendIdx_3821_, lean_object* v_closed_3822_, lean_object* v___x_3823_, lean_object* v_a_3824_, lean_object* v_recvIdx_3825_, lean_object* v_x_3826_, lean_object* v___y_3827_){
_start:
{
uint8_t v___x_6426__boxed_3828_; uint8_t v_closed_boxed_3829_; uint8_t v___x_6427__boxed_3830_; lean_object* v_res_3831_; 
v___x_6426__boxed_3828_ = lean_unbox(v___x_3815_);
v_closed_boxed_3829_ = lean_unbox(v_closed_3822_);
v___x_6427__boxed_3830_ = lean_unbox(v___x_3823_);
v_res_3831_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3814_, v___x_6426__boxed_3828_, v_bufCount_3816_, v_producers_3817_, v_consumers_3818_, v_capacity_3819_, v_buf_3820_, v_sendIdx_3821_, v_closed_boxed_3829_, v___x_6427__boxed_3830_, v_a_3824_, v_recvIdx_3825_, v_x_3826_);
lean_dec(v_recvIdx_3825_);
lean_dec(v_a_3824_);
lean_dec(v_bufCount_3816_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3832_, lean_object* v_x_3833_){
_start:
{
if (lean_obj_tag(v_x_3833_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3843_; 
v_a_3835_ = lean_ctor_get(v_x_3833_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_x_3833_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3837_ = v_x_3833_;
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v_x_3833_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
return v___x_3841_;
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3872_; 
v_a_3844_ = lean_ctor_get(v_x_3833_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_x_3833_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3846_ = v_x_3833_;
v_isShared_3847_ = v_isSharedCheck_3872_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v_x_3833_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3872_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v_producers_3848_; lean_object* v_consumers_3849_; lean_object* v_capacity_3850_; lean_object* v_buf_3851_; lean_object* v_bufCount_3852_; lean_object* v_sendIdx_3853_; lean_object* v_recvIdx_3854_; uint8_t v_closed_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v_producers_3848_ = lean_ctor_get(v_a_3844_, 0);
lean_inc_ref(v_producers_3848_);
v_consumers_3849_ = lean_ctor_get(v_a_3844_, 1);
lean_inc_ref(v_consumers_3849_);
v_capacity_3850_ = lean_ctor_get(v_a_3844_, 2);
lean_inc(v_capacity_3850_);
v_buf_3851_ = lean_ctor_get(v_a_3844_, 3);
lean_inc_ref(v_buf_3851_);
v_bufCount_3852_ = lean_ctor_get(v_a_3844_, 4);
lean_inc(v_bufCount_3852_);
v_sendIdx_3853_ = lean_ctor_get(v_a_3844_, 5);
lean_inc(v_sendIdx_3853_);
v_recvIdx_3854_ = lean_ctor_get(v_a_3844_, 6);
lean_inc(v_recvIdx_3854_);
v_closed_3855_ = lean_ctor_get_uint8(v_a_3844_, sizeof(void*)*7);
lean_dec(v_a_3844_);
v___x_3856_ = lean_unsigned_to_nat(0u);
v___x_3857_ = lean_nat_dec_eq(v_bufCount_3852_, v___x_3856_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___f_3865_; lean_object* v___x_3867_; 
v___x_3858_ = lean_array_fget_borrowed(v_buf_3851_, v_recvIdx_3854_);
v___x_3859_ = lean_box(0);
v___x_3860_ = lean_st_ref_swap(v___x_3858_, v___x_3859_);
v___x_3861_ = 1;
v___x_3862_ = lean_box(v___x_3857_);
v___x_3863_ = lean_box(v_closed_3855_);
v___x_3864_ = lean_box(v___x_3861_);
lean_inc(v_a_3832_);
v___f_3865_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3865_, 0, v___x_3856_);
lean_closure_set(v___f_3865_, 1, v___x_3862_);
lean_closure_set(v___f_3865_, 2, v_bufCount_3852_);
lean_closure_set(v___f_3865_, 3, v_producers_3848_);
lean_closure_set(v___f_3865_, 4, v_consumers_3849_);
lean_closure_set(v___f_3865_, 5, v_capacity_3850_);
lean_closure_set(v___f_3865_, 6, v_buf_3851_);
lean_closure_set(v___f_3865_, 7, v_sendIdx_3853_);
lean_closure_set(v___f_3865_, 8, v___x_3863_);
lean_closure_set(v___f_3865_, 9, v___x_3864_);
lean_closure_set(v___f_3865_, 10, v_a_3832_);
lean_closure_set(v___f_3865_, 11, v_recvIdx_3854_);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 0, v___x_3860_);
v___x_3867_ = v___x_3846_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3860_);
v___x_3867_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
v___x_3869_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3856_, v___x_3857_, v___x_3868_, v___f_3865_);
return v___x_3869_;
}
}
else
{
lean_object* v___x_3871_; 
lean_dec(v_recvIdx_3854_);
lean_dec(v_sendIdx_3853_);
lean_dec(v_bufCount_3852_);
lean_dec_ref(v_buf_3851_);
lean_dec(v_capacity_3850_);
lean_dec_ref(v_consumers_3849_);
lean_dec_ref(v_producers_3848_);
lean_del_object(v___x_3846_);
v___x_3871_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_3871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3873_, lean_object* v_x_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3873_, v_x_3874_);
lean_dec(v_a_3873_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3877_){
_start:
{
lean_object* v___x_3879_; lean_object* v___f_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; uint8_t v___x_3884_; lean_object* v___x_3885_; 
v___x_3879_ = lean_st_ref_get(v_a_3877_);
lean_inc(v_a_3877_);
v___f_3880_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3880_, 0, v_a_3877_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = 0;
v___x_3885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3883_, v___x_3884_, v___x_3882_, v___f_3880_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3886_);
lean_dec(v_a_3886_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3890_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3893_, lean_object* v_a_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3893_, v_a_3894_);
lean_dec(v_a_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3897_, lean_object* v_x_3898_){
_start:
{
lean_object* v_val_3901_; lean_object* v___x_3903_; 
v___x_3903_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3897_, v_x_3898_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3903_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set_tag(v___x_3906_, 1);
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
v_val_3901_ = v___x_3909_;
goto v___jp_3900_;
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
v_a_3912_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3903_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3903_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
lean_ctor_set_tag(v___x_3914_, 0);
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
v_val_3901_ = v___x_3917_;
goto v___jp_3900_;
}
}
}
v___jp_3900_:
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3902_, 0, v_val_3901_);
return v___x_3902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3920_, lean_object* v_x_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3920_, v_x_3921_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v_x_3924_){
_start:
{
uint8_t v___y_3927_; 
if (lean_obj_tag(v_x_3924_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3939_; 
v_a_3931_ = lean_ctor_get(v_x_3924_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_x_3924_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3933_ = v_x_3924_;
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v_x_3924_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v_bufCount_3941_; uint8_t v_closed_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; uint8_t v___x_3945_; 
v_a_3940_ = lean_ctor_get(v_x_3924_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v_x_3924_, 1);
v_bufCount_3941_ = lean_ctor_get(v_a_3940_, 4);
lean_inc(v_bufCount_3941_);
v_closed_3942_ = lean_ctor_get_uint8(v_a_3940_, sizeof(void*)*7);
lean_dec(v_a_3940_);
v___x_3943_ = lean_unsigned_to_nat(0u);
v___x_3944_ = lean_nat_dec_eq(v_bufCount_3941_, v___x_3943_);
lean_dec(v_bufCount_3941_);
v___x_3945_ = lean_bool_not(v___x_3944_);
if (v___x_3945_ == 0)
{
v___y_3927_ = v_closed_3942_;
goto v___jp_3926_;
}
else
{
v___y_3927_ = v___x_3945_;
goto v___jp_3926_;
}
}
v___jp_3926_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3928_ = lean_box(v___y_3927_);
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
v___x_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
return v___x_3930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v_x_3946_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___y_3949_, lean_object* v___f_3950_, lean_object* v_x_3951_){
_start:
{
if (lean_obj_tag(v_x_3951_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref(v___f_3950_);
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
lean_object* v_a_3962_; uint8_t v___x_3963_; 
v_a_3962_ = lean_ctor_get(v_x_3951_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v_x_3951_, 1);
v___x_3963_ = lean_unbox(v_a_3962_);
lean_dec(v_a_3962_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; 
lean_dec_ref(v___f_3950_);
v___x_3964_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3964_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3965_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3949_);
v___x_3966_ = lean_unsigned_to_nat(0u);
v___x_3967_ = 0;
v___x_3968_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3966_, v___x_3967_, v___x_3965_, v___f_3950_);
return v___x_3968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___y_3969_, lean_object* v___f_3970_, lean_object* v_x_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___y_3969_, v___f_3970_, v_x_3971_);
lean_dec(v___y_3969_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3974_, lean_object* v___f_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; lean_object* v___x_3983_; lean_object* v___f_3984_; lean_object* v___x_3985_; 
v___x_3978_ = lean_st_ref_get(v___y_3976_);
v___x_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
v___x_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
v___x_3981_ = lean_unsigned_to_nat(0u);
v___x_3982_ = 0;
v___x_3983_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3981_, v___x_3982_, v___x_3980_, v___f_3974_);
lean_inc(v___y_3976_);
v___f_3984_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3984_, 0, v___y_3976_);
lean_closure_set(v___f_3984_, 1, v___f_3975_);
v___x_3985_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3981_, v___x_3982_, v___x_3983_, v___f_3984_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3986_, lean_object* v___f_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3986_, v___f_3987_, v___y_3988_);
lean_dec(v___y_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3991_, lean_object* v_capacity_3992_, lean_object* v_buf_3993_, lean_object* v_bufCount_3994_, lean_object* v_sendIdx_3995_, lean_object* v_recvIdx_3996_, uint8_t v_closed_3997_, lean_object* v___y_3998_, lean_object* v_x_3999_){
_start:
{
if (lean_obj_tag(v_x_3999_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4009_; 
lean_dec(v_recvIdx_3996_);
lean_dec(v_sendIdx_3995_);
lean_dec(v_bufCount_3994_);
lean_dec_ref(v_buf_3993_);
lean_dec(v_capacity_3992_);
lean_dec_ref(v_producers_3991_);
v_a_4001_ = lean_ctor_get(v_x_3999_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_x_3999_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4003_ = v_x_3999_;
v_isShared_4004_ = v_isSharedCheck_4009_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v_x_3999_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4009_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4007_; 
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
return v___x_4007_;
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4020_; 
v_a_4010_ = lean_ctor_get(v_x_3999_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v_x_3999_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4012_ = v_x_3999_;
v_isShared_4013_ = v_isSharedCheck_4020_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v_x_3999_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4020_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4017_; 
v___x_4014_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_4014_, 0, v_producers_3991_);
lean_ctor_set(v___x_4014_, 1, v_a_4010_);
lean_ctor_set(v___x_4014_, 2, v_capacity_3992_);
lean_ctor_set(v___x_4014_, 3, v_buf_3993_);
lean_ctor_set(v___x_4014_, 4, v_bufCount_3994_);
lean_ctor_set(v___x_4014_, 5, v_sendIdx_3995_);
lean_ctor_set(v___x_4014_, 6, v_recvIdx_3996_);
lean_ctor_set_uint8(v___x_4014_, sizeof(void*)*7, v_closed_3997_);
v___x_4015_ = lean_st_ref_set(v___y_3998_, v___x_4014_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4015_);
v___x_4017_ = v___x_4012_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4015_);
v___x_4017_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
lean_object* v___x_4018_; 
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_4021_, lean_object* v_capacity_4022_, lean_object* v_buf_4023_, lean_object* v_bufCount_4024_, lean_object* v_sendIdx_4025_, lean_object* v_recvIdx_4026_, lean_object* v_closed_4027_, lean_object* v___y_4028_, lean_object* v_x_4029_, lean_object* v___y_4030_){
_start:
{
uint8_t v_closed_boxed_4031_; lean_object* v_res_4032_; 
v_closed_boxed_4031_ = lean_unbox(v_closed_4027_);
v_res_4032_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_4021_, v_capacity_4022_, v_buf_4023_, v_bufCount_4024_, v_sendIdx_4025_, v_recvIdx_4026_, v_closed_boxed_4031_, v___y_4028_, v_x_4029_);
lean_dec(v___y_4028_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_4033_, lean_object* v_x_4034_, lean_object* v_head_4035_, lean_object* v_x_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_4033_, v_x_4034_, v_head_4035_, v_x_4036_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_4039_, lean_object* v_x_4040_){
_start:
{
if (lean_obj_tag(v_x_4039_) == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4042_, 0, v_x_4040_);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
return v___x_4043_;
}
else
{
lean_object* v_head_4044_; lean_object* v_tail_4045_; lean_object* v_waiter_4046_; lean_object* v___f_4047_; lean_object* v_val_4049_; 
v_head_4044_ = lean_ctor_get(v_x_4039_, 0);
lean_inc(v_head_4044_);
v_tail_4045_ = lean_ctor_get(v_x_4039_, 1);
lean_inc(v_tail_4045_);
lean_dec_ref_known(v_x_4039_, 2);
v_waiter_4046_ = lean_ctor_get(v_head_4044_, 1);
lean_inc(v_waiter_4046_);
v___f_4047_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4047_, 0, v_tail_4045_);
lean_closure_set(v___f_4047_, 1, v_x_4040_);
lean_closure_set(v___f_4047_, 2, v_head_4044_);
if (lean_obj_tag(v_waiter_4046_) == 0)
{
lean_object* v___x_4053_; 
v___x_4053_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_4049_ = v___x_4053_;
goto v___jp_4048_;
}
else
{
lean_object* v_val_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4068_; 
v_val_4054_ = lean_ctor_get(v_waiter_4046_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v_waiter_4046_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4056_ = v_waiter_4046_;
v_isShared_4057_ = v_isSharedCheck_4068_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_val_4054_);
lean_dec(v_waiter_4046_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4068_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v_finished_4058_; lean_object* v___x_4059_; lean_object* v___f_4060_; lean_object* v___x_4062_; 
v_finished_4058_ = lean_ctor_get(v_val_4054_, 0);
lean_inc(v_finished_4058_);
lean_dec(v_val_4054_);
v___x_4059_ = lean_st_ref_get(v_finished_4058_);
lean_dec(v_finished_4058_);
v___f_4060_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 0, v___x_4059_);
v___x_4062_ = v___x_4056_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4059_);
v___x_4062_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; lean_object* v___x_4066_; 
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
v___x_4064_ = lean_unsigned_to_nat(0u);
v___x_4065_ = 0;
v___x_4066_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4064_, v___x_4065_, v___x_4063_, v___f_4060_);
v_val_4049_ = v___x_4066_;
goto v___jp_4048_;
}
}
}
v___jp_4048_:
{
lean_object* v___x_4050_; uint8_t v___x_4051_; lean_object* v___x_4052_; 
v___x_4050_ = lean_unsigned_to_nat(0u);
v___x_4051_ = 0;
v___x_4052_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4050_, v___x_4051_, v_val_4049_, v___f_4047_);
return v___x_4052_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_4069_, lean_object* v_x_4070_, lean_object* v_head_4071_, lean_object* v_x_4072_){
_start:
{
if (lean_obj_tag(v_x_4072_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4082_; 
lean_dec_ref(v_head_4071_);
lean_dec(v_x_4070_);
lean_dec(v_tail_4069_);
v_a_4074_ = lean_ctor_get(v_x_4072_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_x_4072_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4076_ = v_x_4072_;
v_isShared_4077_ = v_isSharedCheck_4082_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v_x_4072_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4082_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4074_);
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
else
{
lean_object* v_a_4083_; uint8_t v___x_4084_; 
v_a_4083_ = lean_ctor_get(v_x_4072_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v_x_4072_, 1);
v___x_4084_ = lean_unbox(v_a_4083_);
lean_dec(v_a_4083_);
if (v___x_4084_ == 0)
{
lean_object* v___x_4085_; 
lean_dec_ref(v_head_4071_);
v___x_4085_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4069_, v_x_4070_);
return v___x_4085_;
}
else
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4086_, 0, v_head_4071_);
lean_ctor_set(v___x_4086_, 1, v_x_4070_);
v___x_4087_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4069_, v___x_4086_);
return v___x_4087_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4088_, lean_object* v_x_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4088_, v_x_4089_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4092_){
_start:
{
if (lean_obj_tag(v_x_4092_) == 0)
{
lean_object* v___x_4094_; 
v___x_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4094_, 0, v_x_4092_);
return v___x_4094_;
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4104_; 
v_a_4095_ = lean_ctor_get(v_x_4092_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_x_4092_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4097_ = v_x_4092_;
v_isShared_4098_ = v_isSharedCheck_4104_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v_x_4092_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4104_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4099_ = l_List_reverse___redArg(v_a_4095_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4099_);
v___x_4101_ = v___x_4097_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
return v___x_4102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4105_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4108_, lean_object* v___x_4109_, lean_object* v_x_4110_){
_start:
{
if (lean_obj_tag(v_x_4110_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v___x_4109_);
lean_dec(v_a_4108_);
v_a_4112_ = lean_ctor_get(v_x_4110_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v_x_4110_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4114_ = v_x_4110_;
v_isShared_4115_ = v_isSharedCheck_4120_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v_x_4110_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4120_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
return v___x_4118_;
}
}
}
else
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4137_; 
v_a_4121_ = lean_ctor_get(v_x_4110_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_x_4110_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4123_ = v_x_4110_;
v_isShared_4124_ = v_isSharedCheck_4137_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v_x_4110_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4137_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
uint8_t v___x_4125_; 
v___x_4125_ = l_List_isEmpty___redArg(v_a_4108_);
if (v___x_4125_ == 0)
{
lean_object* v___x_4126_; lean_object* v___x_4128_; 
lean_dec(v___x_4109_);
v___x_4126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4126_, 0, v_a_4121_);
lean_ctor_set(v___x_4126_, 1, v_a_4108_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 0, v___x_4126_);
v___x_4128_ = v___x_4123_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
return v___x_4129_;
}
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4134_; 
lean_dec(v_a_4108_);
v___x_4131_ = l_List_reverse___redArg(v_a_4121_);
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4109_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 0, v___x_4132_);
v___x_4134_ = v___x_4123_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
lean_object* v___x_4135_; 
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4138_, lean_object* v___x_4139_, lean_object* v_x_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4138_, v___x_4139_, v_x_4140_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_eList_4143_, lean_object* v___x_4144_, lean_object* v___f_4145_, lean_object* v_x_4146_){
_start:
{
if (lean_obj_tag(v_x_4146_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4156_; 
lean_dec_ref(v___f_4145_);
lean_dec(v___x_4144_);
lean_dec(v_eList_4143_);
v_a_4148_ = lean_ctor_get(v_x_4146_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v_x_4146_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4150_ = v_x_4146_;
v_isShared_4151_ = v_isSharedCheck_4156_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v_x_4146_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4156_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4153_; 
if (v_isShared_4151_ == 0)
{
v___x_4153_ = v___x_4150_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4148_);
v___x_4153_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
lean_object* v___x_4154_; 
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4153_);
return v___x_4154_;
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; uint8_t v___x_4160_; lean_object* v___x_4161_; lean_object* v___f_4162_; lean_object* v___x_4163_; 
v_a_4157_ = lean_ctor_get(v_x_4146_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v_x_4146_, 1);
lean_inc(v___x_4144_);
v___x_4158_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4143_, v___x_4144_);
v___x_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = 0;
v___x_4161_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4159_, v___x_4160_, v___x_4158_, v___f_4145_);
v___f_4162_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4162_, 0, v_a_4157_);
lean_closure_set(v___f_4162_, 1, v___x_4144_);
v___x_4163_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4159_, v___x_4160_, v___x_4161_, v___f_4162_);
return v___x_4163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_eList_4164_, lean_object* v___x_4165_, lean_object* v___f_4166_, lean_object* v_x_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v_eList_4164_, v___x_4165_, v___f_4166_, v_x_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_eList_4174_; lean_object* v_dList_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___f_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; lean_object* v___x_4181_; lean_object* v___f_4182_; lean_object* v___x_4183_; 
v_eList_4174_ = lean_ctor_get(v_q_4171_, 0);
lean_inc(v_eList_4174_);
v_dList_4175_ = lean_ctor_get(v_q_4171_, 1);
lean_inc(v_dList_4175_);
lean_dec_ref(v_q_4171_);
v___x_4176_ = lean_box(0);
v___x_4177_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4175_, v___x_4176_);
v___f_4178_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4179_ = lean_unsigned_to_nat(0u);
v___x_4180_ = 0;
v___x_4181_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4179_, v___x_4180_, v___x_4177_, v___f_4178_);
v___f_4182_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4182_, 0, v_eList_4174_);
lean_closure_set(v___f_4182_, 1, v___x_4176_);
lean_closure_set(v___f_4182_, 2, v___f_4178_);
v___x_4183_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4179_, v___x_4180_, v___x_4181_, v___f_4182_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4184_, v___y_4185_);
lean_dec(v___y_4185_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4188_, lean_object* v_x_4189_){
_start:
{
if (lean_obj_tag(v_x_4189_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4199_; 
v_a_4191_ = lean_ctor_get(v_x_4189_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v_x_4189_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4193_ = v_x_4189_;
v_isShared_4194_ = v_isSharedCheck_4199_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v_x_4189_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4199_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
lean_object* v___x_4197_; 
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v_producers_4201_; lean_object* v_consumers_4202_; lean_object* v_capacity_4203_; lean_object* v_buf_4204_; lean_object* v_bufCount_4205_; lean_object* v_sendIdx_4206_; lean_object* v_recvIdx_4207_; uint8_t v_closed_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___f_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; lean_object* v___x_4214_; 
v_a_4200_ = lean_ctor_get(v_x_4189_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v_x_4189_, 1);
v_producers_4201_ = lean_ctor_get(v_a_4200_, 0);
lean_inc_ref(v_producers_4201_);
v_consumers_4202_ = lean_ctor_get(v_a_4200_, 1);
lean_inc_ref(v_consumers_4202_);
v_capacity_4203_ = lean_ctor_get(v_a_4200_, 2);
lean_inc(v_capacity_4203_);
v_buf_4204_ = lean_ctor_get(v_a_4200_, 3);
lean_inc_ref(v_buf_4204_);
v_bufCount_4205_ = lean_ctor_get(v_a_4200_, 4);
lean_inc(v_bufCount_4205_);
v_sendIdx_4206_ = lean_ctor_get(v_a_4200_, 5);
lean_inc(v_sendIdx_4206_);
v_recvIdx_4207_ = lean_ctor_get(v_a_4200_, 6);
lean_inc(v_recvIdx_4207_);
v_closed_4208_ = lean_ctor_get_uint8(v_a_4200_, sizeof(void*)*7);
lean_dec(v_a_4200_);
v___x_4209_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4202_, v___y_4188_);
v___x_4210_ = lean_box(v_closed_4208_);
lean_inc(v___y_4188_);
v___f_4211_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4211_, 0, v_producers_4201_);
lean_closure_set(v___f_4211_, 1, v_capacity_4203_);
lean_closure_set(v___f_4211_, 2, v_buf_4204_);
lean_closure_set(v___f_4211_, 3, v_bufCount_4205_);
lean_closure_set(v___f_4211_, 4, v_sendIdx_4206_);
lean_closure_set(v___f_4211_, 5, v_recvIdx_4207_);
lean_closure_set(v___f_4211_, 6, v___x_4210_);
lean_closure_set(v___f_4211_, 7, v___y_4188_);
v___x_4212_ = lean_unsigned_to_nat(0u);
v___x_4213_ = 0;
v___x_4214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4212_, v___x_4213_, v___x_4209_, v___f_4211_);
return v___x_4214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4215_, lean_object* v_x_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4215_, v_x_4216_);
lean_dec(v___y_4215_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; lean_object* v___f_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; lean_object* v___x_4227_; 
v___x_4221_ = lean_st_ref_get(v___y_4219_);
lean_inc(v___y_4219_);
v___f_4222_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4222_, 0, v___y_4219_);
v___x_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4221_);
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
v___x_4225_ = lean_unsigned_to_nat(0u);
v___x_4226_ = 0;
v___x_4227_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4225_, v___x_4226_, v___x_4224_, v___f_4222_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4228_);
lean_dec(v___y_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4236_){
_start:
{
lean_object* v___f_4237_; lean_object* v___f_4238_; lean_object* v___f_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_inc_ref_n(v_ch_4236_, 2);
v___f_4237_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4237_, 0, v_ch_4236_);
v___f_4238_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___f_4239_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2));
v___x_4240_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4240_, 0, lean_box(0));
lean_closure_set(v___x_4240_, 1, lean_box(0));
lean_closure_set(v___x_4240_, 2, v_ch_4236_);
lean_closure_set(v___x_4240_, 3, v___f_4238_);
v___x_4241_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4241_, 0, lean_box(0));
lean_closure_set(v___x_4241_, 1, lean_box(0));
lean_closure_set(v___x_4241_, 2, v_ch_4236_);
lean_closure_set(v___x_4241_, 3, v___f_4239_);
v___x_4242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4240_);
lean_ctor_set(v___x_4242_, 1, v___f_4237_);
lean_ctor_set(v___x_4242_, 2, v___x_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4243_, lean_object* v_ch_4244_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4246_, lean_object* v_q_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4247_, v___y_4248_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4251_, lean_object* v_q_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4251_, v_q_4252_, v___y_4253_);
lean_dec(v___y_4253_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4256_, lean_object* v_x_4257_, lean_object* v_x_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4257_, v_x_4258_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4262_, lean_object* v_x_4263_, lean_object* v_x_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4262_, v_x_4263_, v_x_4264_, v___y_4265_);
lean_dec(v___y_4265_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object* v_x_4268_){
_start:
{
switch(lean_obj_tag(v_x_4268_))
{
case 0:
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_unsigned_to_nat(0u);
return v___x_4269_;
}
case 1:
{
lean_object* v___x_4270_; 
v___x_4270_ = lean_unsigned_to_nat(1u);
return v___x_4270_;
}
default: 
{
lean_object* v___x_4271_; 
v___x_4271_ = lean_unsigned_to_nat(2u);
return v___x_4271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object* v_x_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4272_);
lean_dec_ref(v_x_4272_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object* v_00_u03b1_4274_, lean_object* v_x_4275_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object* v_00_u03b1_4277_, lean_object* v_x_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_4277_, v_x_4278_);
lean_dec_ref(v_x_4278_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4280_, lean_object* v_k_4281_){
_start:
{
lean_object* v_ch_4282_; lean_object* v___x_4283_; 
v_ch_4282_ = lean_ctor_get(v_t_4280_, 0);
lean_inc_ref(v_ch_4282_);
lean_dec_ref(v_t_4280_);
v___x_4283_ = lean_apply_1(v_k_4281_, v_ch_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4284_, lean_object* v_motive_4285_, lean_object* v_ctorIdx_4286_, lean_object* v_t_4287_, lean_object* v_h_4288_, lean_object* v_k_4289_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4287_, v_k_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4291_, lean_object* v_motive_4292_, lean_object* v_ctorIdx_4293_, lean_object* v_t_4294_, lean_object* v_h_4295_, lean_object* v_k_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4291_, v_motive_4292_, v_ctorIdx_4293_, v_t_4294_, v_h_4295_, v_k_4296_);
lean_dec(v_ctorIdx_4293_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4298_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4299_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4298_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4301_, lean_object* v_motive_4302_, lean_object* v_t_4303_, lean_object* v_h_4304_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4305_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4303_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4307_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4308_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4307_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4308_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4310_, lean_object* v_motive_4311_, lean_object* v_t_4312_, lean_object* v_h_4313_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4314_){
_start:
{
lean_object* v___x_4315_; 
v___x_4315_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4312_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4314_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4316_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4317_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4316_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4317_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4319_, lean_object* v_motive_4320_, lean_object* v_t_4321_, lean_object* v_h_4322_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4321_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4325_){
_start:
{
if (lean_obj_tag(v_capacity_4325_) == 0)
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4328_, 0, v___x_4327_);
return v___x_4328_;
}
else
{
lean_object* v_val_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4346_; 
v_val_4329_ = lean_ctor_get(v_capacity_4325_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v_capacity_4325_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4331_ = v_capacity_4325_;
v_isShared_4332_ = v_isSharedCheck_4346_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_val_4329_);
lean_dec(v_capacity_4325_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4346_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v_zero_4333_; uint8_t v_isZero_4334_; 
v_zero_4333_ = lean_unsigned_to_nat(0u);
v_isZero_4334_ = lean_nat_dec_eq(v_val_4329_, v_zero_4333_);
if (v_isZero_4334_ == 1)
{
lean_object* v___x_4335_; lean_object* v___x_4337_; 
lean_dec(v_val_4329_);
v___x_4335_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4332_ == 0)
{
lean_ctor_set(v___x_4331_, 0, v___x_4335_);
v___x_4337_ = v___x_4331_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
else
{
lean_object* v_one_4339_; lean_object* v_n_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4344_; 
v_one_4339_ = lean_unsigned_to_nat(1u);
v_n_4340_ = lean_nat_sub(v_val_4329_, v_one_4339_);
lean_dec(v_val_4329_);
v___x_4341_ = lean_nat_add(v_n_4340_, v_one_4339_);
lean_dec(v_n_4340_);
v___x_4342_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4341_);
if (v_isShared_4332_ == 0)
{
lean_ctor_set_tag(v___x_4331_, 2);
lean_ctor_set(v___x_4331_, 0, v___x_4342_);
v___x_4344_ = v___x_4331_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Std_CloseableChannel_new___redArg(v_capacity_4347_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4350_, lean_object* v_capacity_4351_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Std_CloseableChannel_new___redArg(v_capacity_4351_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4354_, lean_object* v_capacity_4355_, lean_object* v_a_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l_Std_CloseableChannel_new(v_00_u03b1_4354_, v_capacity_4355_);
return v_res_4357_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4358_, lean_object* v_v_4359_){
_start:
{
switch(lean_obj_tag(v_ch_4358_))
{
case 0:
{
lean_object* v_ch_4361_; uint8_t v___x_4362_; 
v_ch_4361_ = lean_ctor_get(v_ch_4358_, 0);
lean_inc_ref(v_ch_4361_);
lean_dec_ref_known(v_ch_4358_, 1);
v___x_4362_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4361_, v_v_4359_);
return v___x_4362_;
}
case 1:
{
lean_object* v_ch_4363_; uint8_t v___x_4364_; 
v_ch_4363_ = lean_ctor_get(v_ch_4358_, 0);
lean_inc_ref(v_ch_4363_);
lean_dec_ref_known(v_ch_4358_, 1);
v___x_4364_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4363_, v_v_4359_);
return v___x_4364_;
}
default: 
{
lean_object* v_ch_4365_; uint8_t v___x_4366_; 
v_ch_4365_ = lean_ctor_get(v_ch_4358_, 0);
lean_inc_ref(v_ch_4365_);
lean_dec_ref_known(v_ch_4358_, 1);
v___x_4366_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4365_, v_v_4359_);
return v___x_4366_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4367_, lean_object* v_v_4368_, lean_object* v_a_4369_){
_start:
{
uint8_t v_res_4370_; lean_object* v_r_4371_; 
v_res_4370_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4367_, v_v_4368_);
v_r_4371_ = lean_box(v_res_4370_);
return v_r_4371_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4372_, lean_object* v_ch_4373_, lean_object* v_v_4374_){
_start:
{
uint8_t v___x_4376_; 
v___x_4376_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4373_, v_v_4374_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4377_, lean_object* v_ch_4378_, lean_object* v_v_4379_, lean_object* v_a_4380_){
_start:
{
uint8_t v_res_4381_; lean_object* v_r_4382_; 
v_res_4381_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4377_, v_ch_4378_, v_v_4379_);
v_r_4382_ = lean_box(v_res_4381_);
return v_r_4382_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4383_, lean_object* v_v_4384_){
_start:
{
switch(lean_obj_tag(v_ch_4383_))
{
case 0:
{
lean_object* v_ch_4386_; lean_object* v___x_4387_; 
v_ch_4386_ = lean_ctor_get(v_ch_4383_, 0);
lean_inc_ref(v_ch_4386_);
lean_dec_ref_known(v_ch_4383_, 1);
v___x_4387_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4386_, v_v_4384_);
return v___x_4387_;
}
case 1:
{
lean_object* v_ch_4388_; lean_object* v___x_4389_; 
v_ch_4388_ = lean_ctor_get(v_ch_4383_, 0);
lean_inc_ref(v_ch_4388_);
lean_dec_ref_known(v_ch_4383_, 1);
v___x_4389_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4388_, v_v_4384_);
return v___x_4389_;
}
default: 
{
lean_object* v_ch_4390_; lean_object* v___x_4391_; 
v_ch_4390_ = lean_ctor_get(v_ch_4383_, 0);
lean_inc_ref(v_ch_4390_);
lean_dec_ref_known(v_ch_4383_, 1);
v___x_4391_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4390_, v_v_4384_);
return v___x_4391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4392_, lean_object* v_v_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Std_CloseableChannel_send___redArg(v_ch_4392_, v_v_4393_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4396_, lean_object* v_ch_4397_, lean_object* v_v_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Std_CloseableChannel_send___redArg(v_ch_4397_, v_v_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4401_, lean_object* v_ch_4402_, lean_object* v_v_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Std_CloseableChannel_send(v_00_u03b1_4401_, v_ch_4402_, v_v_4403_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4406_){
_start:
{
switch(lean_obj_tag(v_ch_4406_))
{
case 0:
{
lean_object* v_ch_4408_; lean_object* v___x_4409_; 
v_ch_4408_ = lean_ctor_get(v_ch_4406_, 0);
lean_inc_ref(v_ch_4408_);
lean_dec_ref_known(v_ch_4406_, 1);
v___x_4409_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4408_);
return v___x_4409_;
}
case 1:
{
lean_object* v_ch_4410_; lean_object* v___x_4411_; 
v_ch_4410_ = lean_ctor_get(v_ch_4406_, 0);
lean_inc_ref(v_ch_4410_);
lean_dec_ref_known(v_ch_4406_, 1);
v___x_4411_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4410_);
return v___x_4411_;
}
default: 
{
lean_object* v_ch_4412_; lean_object* v___x_4413_; 
v_ch_4412_ = lean_ctor_get(v_ch_4406_, 0);
lean_inc_ref(v_ch_4412_);
lean_dec_ref_known(v_ch_4406_, 1);
v___x_4413_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4412_);
return v___x_4413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Std_CloseableChannel_close___redArg(v_ch_4414_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4417_, lean_object* v_ch_4418_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_Std_CloseableChannel_close___redArg(v_ch_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4421_, lean_object* v_ch_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l_Std_CloseableChannel_close(v_00_u03b1_4421_, v_ch_4422_);
return v_res_4424_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4425_){
_start:
{
switch(lean_obj_tag(v_ch_4425_))
{
case 0:
{
lean_object* v_ch_4427_; uint8_t v___x_4428_; 
v_ch_4427_ = lean_ctor_get(v_ch_4425_, 0);
lean_inc_ref(v_ch_4427_);
lean_dec_ref_known(v_ch_4425_, 1);
v___x_4428_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4427_);
return v___x_4428_;
}
case 1:
{
lean_object* v_ch_4429_; uint8_t v___x_4430_; 
v_ch_4429_ = lean_ctor_get(v_ch_4425_, 0);
lean_inc_ref(v_ch_4429_);
lean_dec_ref_known(v_ch_4425_, 1);
v___x_4430_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4429_);
return v___x_4430_;
}
default: 
{
lean_object* v_ch_4431_; uint8_t v___x_4432_; 
v_ch_4431_ = lean_ctor_get(v_ch_4425_, 0);
lean_inc_ref(v_ch_4431_);
lean_dec_ref_known(v_ch_4425_, 1);
v___x_4432_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4431_);
return v___x_4432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4433_, lean_object* v_a_4434_){
_start:
{
uint8_t v_res_4435_; lean_object* v_r_4436_; 
v_res_4435_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4433_);
v_r_4436_ = lean_box(v_res_4435_);
return v_r_4436_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4437_, lean_object* v_ch_4438_){
_start:
{
uint8_t v___x_4440_; 
v___x_4440_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4438_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4441_, lean_object* v_ch_4442_, lean_object* v_a_4443_){
_start:
{
uint8_t v_res_4444_; lean_object* v_r_4445_; 
v_res_4444_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4441_, v_ch_4442_);
v_r_4445_ = lean_box(v_res_4444_);
return v_r_4445_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4446_){
_start:
{
switch(lean_obj_tag(v_ch_4446_))
{
case 0:
{
lean_object* v_ch_4448_; lean_object* v___x_4449_; 
v_ch_4448_ = lean_ctor_get(v_ch_4446_, 0);
lean_inc_ref(v_ch_4448_);
lean_dec_ref_known(v_ch_4446_, 1);
v___x_4449_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4448_);
return v___x_4449_;
}
case 1:
{
lean_object* v_ch_4450_; lean_object* v___x_4451_; 
v_ch_4450_ = lean_ctor_get(v_ch_4446_, 0);
lean_inc_ref(v_ch_4450_);
lean_dec_ref_known(v_ch_4446_, 1);
v___x_4451_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4450_);
return v___x_4451_;
}
default: 
{
lean_object* v_ch_4452_; lean_object* v___x_4453_; 
v_ch_4452_ = lean_ctor_get(v_ch_4446_, 0);
lean_inc_ref(v_ch_4452_);
lean_dec_ref_known(v_ch_4446_, 1);
v___x_4453_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4452_);
return v___x_4453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4454_, lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4454_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4457_, lean_object* v_ch_4458_){
_start:
{
lean_object* v___x_4460_; 
v___x_4460_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4458_);
return v___x_4460_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4461_, lean_object* v_ch_4462_, lean_object* v_a_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4461_, v_ch_4462_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4465_){
_start:
{
switch(lean_obj_tag(v_ch_4465_))
{
case 0:
{
lean_object* v_ch_4467_; lean_object* v___x_4468_; 
v_ch_4467_ = lean_ctor_get(v_ch_4465_, 0);
lean_inc_ref(v_ch_4467_);
lean_dec_ref_known(v_ch_4465_, 1);
v___x_4468_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4467_);
return v___x_4468_;
}
case 1:
{
lean_object* v_ch_4469_; lean_object* v___x_4470_; 
v_ch_4469_ = lean_ctor_get(v_ch_4465_, 0);
lean_inc_ref(v_ch_4469_);
lean_dec_ref_known(v_ch_4465_, 1);
v___x_4470_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4469_);
return v___x_4470_;
}
default: 
{
lean_object* v_ch_4471_; lean_object* v___x_4472_; 
v_ch_4471_ = lean_ctor_get(v_ch_4465_, 0);
lean_inc_ref(v_ch_4471_);
lean_dec_ref_known(v_ch_4465_, 1);
v___x_4472_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4471_);
return v___x_4472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l_Std_CloseableChannel_recv___redArg(v_ch_4473_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4476_, lean_object* v_ch_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Std_CloseableChannel_recv___redArg(v_ch_4477_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4480_, lean_object* v_ch_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Std_CloseableChannel_recv(v_00_u03b1_4480_, v_ch_4481_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4484_){
_start:
{
switch(lean_obj_tag(v_ch_4484_))
{
case 0:
{
lean_object* v_ch_4485_; lean_object* v___x_4486_; 
v_ch_4485_ = lean_ctor_get(v_ch_4484_, 0);
lean_inc_ref(v_ch_4485_);
lean_dec_ref_known(v_ch_4484_, 1);
v___x_4486_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4485_);
return v___x_4486_;
}
case 1:
{
lean_object* v_ch_4487_; lean_object* v___x_4488_; 
v_ch_4487_ = lean_ctor_get(v_ch_4484_, 0);
lean_inc_ref(v_ch_4487_);
lean_dec_ref_known(v_ch_4484_, 1);
v___x_4488_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4487_);
return v___x_4488_;
}
default: 
{
lean_object* v_ch_4489_; lean_object* v___x_4490_; 
v_ch_4489_ = lean_ctor_get(v_ch_4484_, 0);
lean_inc_ref(v_ch_4489_);
lean_dec_ref_known(v_ch_4484_, 1);
v___x_4490_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4489_);
return v___x_4490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4491_, lean_object* v_ch_4492_){
_start:
{
lean_object* v___x_4493_; 
v___x_4493_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4492_);
return v___x_4493_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4494_ = lean_box(0);
v___x_4495_ = lean_task_pure(v___x_4494_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4496_, lean_object* v_ch_4497_, lean_object* v_prio_4498_, lean_object* v_x_4499_){
_start:
{
if (lean_obj_tag(v_x_4499_) == 0)
{
lean_object* v___x_4501_; 
lean_dec(v_prio_4498_);
lean_dec_ref(v_ch_4497_);
lean_dec_ref(v_f_4496_);
v___x_4501_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4501_;
}
else
{
lean_object* v_val_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v_val_4502_ = lean_ctor_get(v_x_4499_, 0);
lean_inc(v_val_4502_);
lean_dec_ref_known(v_x_4499_, 1);
lean_inc_ref(v_f_4496_);
v___x_4503_ = lean_apply_2(v_f_4496_, v_val_4502_, lean_box(0));
v___x_4504_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4496_, v_ch_4497_, v_prio_4498_);
return v___x_4504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4505_, lean_object* v_ch_4506_, lean_object* v_prio_4507_, lean_object* v_x_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4505_, v_ch_4506_, v_prio_4507_, v_x_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4511_, lean_object* v_ch_4512_, lean_object* v_prio_4513_){
_start:
{
lean_object* v___x_4515_; lean_object* v___f_4516_; uint8_t v___x_4517_; lean_object* v___x_4518_; 
lean_inc_ref(v_ch_4512_);
v___x_4515_ = l_Std_CloseableChannel_recv___redArg(v_ch_4512_);
lean_inc(v_prio_4513_);
v___f_4516_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4516_, 0, v_f_4511_);
lean_closure_set(v___f_4516_, 1, v_ch_4512_);
lean_closure_set(v___f_4516_, 2, v_prio_4513_);
v___x_4517_ = 0;
v___x_4518_ = lean_io_bind_task(v___x_4515_, v___f_4516_, v_prio_4513_, v___x_4517_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4519_, lean_object* v_ch_4520_, lean_object* v_prio_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4519_, v_ch_4520_, v_prio_4521_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4524_, lean_object* v_f_4525_, lean_object* v_ch_4526_, lean_object* v_prio_4527_){
_start:
{
lean_object* v___x_4529_; 
v___x_4529_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4525_, v_ch_4526_, v_prio_4527_);
return v___x_4529_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4530_, lean_object* v_f_4531_, lean_object* v_ch_4532_, lean_object* v_prio_4533_, lean_object* v_a_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4530_, v_f_4531_, v_ch_4532_, v_prio_4533_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(lean_object* v_x_4536_){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = lean_box(0);
v___x_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4538_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed(lean_object* v_x_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(v_x_4540_);
lean_dec_ref(v_x_4540_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4548_, lean_object* v_inst_4549_){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4551_, lean_object* v_inst_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4551_, v_inst_4552_);
lean_dec(v_inst_4552_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_4554_){
_start:
{
lean_object* v___x_4555_; 
v___x_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4555_, 0, v_a_4554_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_4556_, lean_object* v_x_4557_){
_start:
{
if (lean_obj_tag(v_x_4557_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4567_; 
lean_dec_ref(v___f_4556_);
v_a_4559_ = lean_ctor_get(v_x_4557_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v_x_4557_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4561_ = v_x_4557_;
v_isShared_4562_ = v_isSharedCheck_4567_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v_x_4557_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4567_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
lean_object* v___x_4565_; 
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
return v___x_4565_;
}
}
}
else
{
lean_object* v_a_4568_; 
v_a_4568_ = lean_ctor_get(v_x_4557_, 0);
lean_inc(v_a_4568_);
lean_dec_ref_known(v_x_4557_, 1);
if (lean_obj_tag(v_a_4568_) == 0)
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4577_; 
lean_dec_ref(v___f_4556_);
v_a_4569_ = lean_ctor_get(v_a_4568_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_a_4568_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4571_ = v_a_4568_;
v_isShared_4572_ = v_isSharedCheck_4577_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v_a_4568_);
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
lean_object* v_a_4578_; lean_object* v___x_4579_; uint8_t v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v_a_4578_ = lean_ctor_get(v_a_4568_, 0);
lean_inc(v_a_4578_);
lean_dec_ref_known(v_a_4568_, 1);
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = 0;
v___x_4581_ = lean_task_map(v___f_4556_, v_a_4578_, v___x_4579_, v___x_4580_);
v___x_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
return v___x_4582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_4583_, lean_object* v_x_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(v___f_4583_, v_x_4584_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_4587_, lean_object* v_receiver_4588_){
_start:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; uint8_t v___x_4595_; lean_object* v___x_4596_; 
v___x_4590_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4588_);
v___x_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
v___x_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
v___x_4594_ = lean_unsigned_to_nat(0u);
v___x_4595_ = 0;
v___x_4596_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4594_, v___x_4595_, v___x_4593_, v___f_4587_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_4597_, lean_object* v_receiver_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(v___f_4597_, v_receiver_4598_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4606_, lean_object* v_inst_4607_){
_start:
{
lean_object* v___f_4608_; 
v___f_4608_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2));
return v___f_4608_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4609_, lean_object* v_inst_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4609_, v_inst_4610_);
lean_dec(v_inst_4610_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_4613_, lean_object* v_x_4614_){
_start:
{
if (lean_obj_tag(v_x_4614_) == 0)
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4624_; 
lean_dec_ref(v___f_4613_);
v_a_4616_ = lean_ctor_get(v_x_4614_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v_x_4614_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4618_ = v_x_4614_;
v_isShared_4619_ = v_isSharedCheck_4624_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v_x_4614_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4624_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4621_; 
if (v_isShared_4619_ == 0)
{
v___x_4621_ = v___x_4618_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4616_);
v___x_4621_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
return v___x_4622_;
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; uint8_t v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; 
v_a_4625_ = lean_ctor_get(v_x_4614_, 0);
lean_inc(v_a_4625_);
lean_dec_ref_known(v_x_4614_, 1);
v___x_4626_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0));
v___x_4627_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4627_, 0, lean_box(0));
lean_closure_set(v___x_4627_, 1, lean_box(0));
lean_closure_set(v___x_4627_, 2, lean_box(0));
lean_closure_set(v___x_4627_, 3, v___x_4626_);
lean_closure_set(v___x_4627_, 4, v___f_4613_);
v___x_4628_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4628_, 0, lean_box(0));
lean_closure_set(v___x_4628_, 1, lean_box(0));
lean_closure_set(v___x_4628_, 2, lean_box(0));
lean_closure_set(v___x_4628_, 3, v___x_4627_);
v___x_4629_ = lean_unsigned_to_nat(0u);
v___x_4630_ = 0;
v___x_4631_ = lean_task_map(v___x_4628_, v_a_4625_, v___x_4629_, v___x_4630_);
v___x_4632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
return v___x_4632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_4633_, lean_object* v_x_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(v___f_4633_, v_x_4634_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_4637_, lean_object* v_receiver_4638_, lean_object* v_x_4639_){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; lean_object* v___x_4646_; 
v___x_4641_ = l_Std_CloseableChannel_send___redArg(v_receiver_4638_, v_x_4639_);
v___x_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
v___x_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
v___x_4644_ = lean_unsigned_to_nat(0u);
v___x_4645_ = 0;
v___x_4646_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4644_, v___x_4645_, v___x_4643_, v___f_4637_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_4647_, lean_object* v_receiver_4648_, lean_object* v_x_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(v___f_4647_, v_receiver_4648_, v_x_4649_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(lean_object* v_x_4652_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v_x_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(v_x_4655_);
lean_dec_ref(v_x_4655_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(lean_object* v___f_4658_, lean_object* v_socket_4659_, lean_object* v_x_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v___x_4663_; 
v___x_4663_ = lean_apply_3(v___f_4658_, v_socket_4659_, v___y_4661_, lean_box(0));
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v___f_4664_, lean_object* v_socket_4665_, lean_object* v_x_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(v___f_4664_, v_socket_4665_, v_x_4666_, v___y_4667_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_4670_, lean_object* v___x_4671_, lean_object* v_socket_4672_, lean_object* v_data_4673_){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v___x_4675_ = lean_unsigned_to_nat(0u);
v___x_4676_ = lean_array_get_size(v_data_4673_);
v___x_4677_ = lean_box(0);
v___x_4678_ = lean_nat_dec_lt(v___x_4675_, v___x_4676_);
if (v___x_4678_ == 0)
{
lean_object* v___x_4679_; 
lean_dec_ref(v_data_4673_);
lean_dec_ref(v_socket_4672_);
lean_dec_ref(v___x_4671_);
lean_dec_ref(v___f_4670_);
v___x_4679_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4679_;
}
else
{
lean_object* v___f_4680_; uint8_t v___x_4681_; 
v___f_4680_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4680_, 0, v___f_4670_);
lean_closure_set(v___f_4680_, 1, v_socket_4672_);
v___x_4681_ = lean_nat_dec_le(v___x_4676_, v___x_4676_);
if (v___x_4681_ == 0)
{
if (v___x_4678_ == 0)
{
lean_object* v___x_4682_; 
lean_dec_ref(v___f_4680_);
lean_dec_ref(v_data_4673_);
lean_dec_ref(v___x_4671_);
v___x_4682_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4682_;
}
else
{
size_t v___x_4683_; size_t v___x_4684_; lean_object* v___x_753__overap_4685_; lean_object* v___x_4686_; 
v___x_4683_ = ((size_t)0ULL);
v___x_4684_ = lean_usize_of_nat(v___x_4676_);
v___x_753__overap_4685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4671_, v___f_4680_, v_data_4673_, v___x_4683_, v___x_4684_, v___x_4677_);
v___x_4686_ = lean_apply_1(v___x_753__overap_4685_, lean_box(0));
return v___x_4686_;
}
}
else
{
size_t v___x_4687_; size_t v___x_4688_; lean_object* v___x_756__overap_4689_; lean_object* v___x_4690_; 
v___x_4687_ = ((size_t)0ULL);
v___x_4688_ = lean_usize_of_nat(v___x_4676_);
v___x_756__overap_4689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4671_, v___f_4680_, v_data_4673_, v___x_4687_, v___x_4688_, v___x_4677_);
v___x_4690_ = lean_apply_1(v___x_756__overap_4689_, lean_box(0));
return v___x_4690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_4691_, lean_object* v___x_4692_, lean_object* v_socket_4693_, lean_object* v_data_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(v___f_4691_, v___x_4692_, v_socket_4693_, v_data_4694_);
return v_res_4696_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_4702_; 
v___x_4702_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_4702_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_4703_; lean_object* v___f_4704_; lean_object* v___f_4705_; 
v___x_4703_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_4704_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___f_4705_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4705_, 0, v___f_4704_);
lean_closure_set(v___f_4705_, 1, v___x_4703_);
return v___f_4705_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___f_4706_; lean_object* v___f_4707_; lean_object* v___f_4708_; lean_object* v___x_4709_; 
v___f_4706_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_4707_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4);
v___f_4708_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___x_4709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4709_, 0, v___f_4708_);
lean_ctor_set(v___x_4709_, 1, v___f_4707_);
lean_ctor_set(v___x_4709_, 2, v___f_4706_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4710_, lean_object* v_inst_4711_){
_start:
{
lean_object* v___x_4712_; 
v___x_4712_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5);
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4713_, lean_object* v_inst_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4713_, v_inst_4714_);
lean_dec(v_inst_4714_);
return v_res_4715_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4716_){
_start:
{
lean_inc_ref(v_ch_4716_);
return v_ch_4716_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Std_CloseableChannel_sync___redArg(v_ch_4717_);
lean_dec_ref(v_ch_4717_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4719_, lean_object* v_ch_4720_){
_start:
{
lean_inc_ref(v_ch_4720_);
return v_ch_4720_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4721_, lean_object* v_ch_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l_Std_CloseableChannel_sync(v_00_u03b1_4721_, v_ch_4722_);
lean_dec_ref(v_ch_4722_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4724_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Std_CloseableChannel_new___redArg(v_capacity_4724_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4727_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4730_, lean_object* v_capacity_4731_){
_start:
{
lean_object* v___x_4733_; 
v___x_4733_ = l_Std_CloseableChannel_new___redArg(v_capacity_4731_);
return v___x_4733_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4734_, lean_object* v_capacity_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4734_, v_capacity_4735_);
return v_res_4737_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4738_, lean_object* v_v_4739_){
_start:
{
uint8_t v___x_4741_; 
v___x_4741_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4738_, v_v_4739_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4742_, lean_object* v_v_4743_, lean_object* v_a_4744_){
_start:
{
uint8_t v_res_4745_; lean_object* v_r_4746_; 
v_res_4745_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4742_, v_v_4743_);
v_r_4746_ = lean_box(v_res_4745_);
return v_r_4746_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4747_, lean_object* v_ch_4748_, lean_object* v_v_4749_){
_start:
{
uint8_t v___x_4751_; 
v___x_4751_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4748_, v_v_4749_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4752_, lean_object* v_ch_4753_, lean_object* v_v_4754_, lean_object* v_a_4755_){
_start:
{
uint8_t v_res_4756_; lean_object* v_r_4757_; 
v_res_4756_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4752_, v_ch_4753_, v_v_4754_);
v_r_4757_ = lean_box(v_res_4756_);
return v_r_4757_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4758_, lean_object* v_v_4759_){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = l_Std_CloseableChannel_send___redArg(v_ch_4758_, v_v_4759_);
v___x_4762_ = lean_io_wait(v___x_4761_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4762_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4762_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
lean_ctor_set_tag(v___x_4765_, 1);
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_4771_; lean_object* v___x_4773_; uint8_t v_isShared_4774_; uint8_t v_isSharedCheck_4778_; 
v_a_4771_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4773_ = v___x_4762_;
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
else
{
lean_inc(v_a_4771_);
lean_dec(v___x_4762_);
v___x_4773_ = lean_box(0);
v_isShared_4774_ = v_isSharedCheck_4778_;
goto v_resetjp_4772_;
}
v_resetjp_4772_:
{
lean_object* v___x_4776_; 
if (v_isShared_4774_ == 0)
{
lean_ctor_set_tag(v___x_4773_, 0);
v___x_4776_ = v___x_4773_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4771_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4779_, lean_object* v_v_4780_, lean_object* v_a_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4779_, v_v_4780_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4783_, lean_object* v_ch_4784_, lean_object* v_v_4785_){
_start:
{
lean_object* v___x_4787_; 
v___x_4787_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4784_, v_v_4785_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4788_, lean_object* v_ch_4789_, lean_object* v_v_4790_, lean_object* v_a_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4788_, v_ch_4789_, v_v_4790_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4793_){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Std_CloseableChannel_close___redArg(v_ch_4793_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4796_, lean_object* v_a_4797_){
_start:
{
lean_object* v_res_4798_; 
v_res_4798_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4796_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4799_, lean_object* v_ch_4800_){
_start:
{
lean_object* v___x_4802_; 
v___x_4802_ = l_Std_CloseableChannel_close___redArg(v_ch_4800_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4803_, lean_object* v_ch_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4803_, v_ch_4804_);
return v_res_4806_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4807_){
_start:
{
uint8_t v___x_4809_; 
v___x_4809_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4807_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4810_, lean_object* v_a_4811_){
_start:
{
uint8_t v_res_4812_; lean_object* v_r_4813_; 
v_res_4812_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4810_);
v_r_4813_ = lean_box(v_res_4812_);
return v_r_4813_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4814_, lean_object* v_ch_4815_){
_start:
{
uint8_t v___x_4817_; 
v___x_4817_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4815_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4818_, lean_object* v_ch_4819_, lean_object* v_a_4820_){
_start:
{
uint8_t v_res_4821_; lean_object* v_r_4822_; 
v_res_4821_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4818_, v_ch_4819_);
v_r_4822_ = lean_box(v_res_4821_);
return v_r_4822_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4823_){
_start:
{
lean_object* v___x_4825_; 
v___x_4825_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4823_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4826_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4829_, lean_object* v_ch_4830_){
_start:
{
lean_object* v___x_4832_; 
v___x_4832_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4830_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4833_, lean_object* v_ch_4834_, lean_object* v_a_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4833_, v_ch_4834_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4837_){
_start:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = l_Std_CloseableChannel_recv___redArg(v_ch_4837_);
v___x_4840_ = lean_io_wait(v___x_4839_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v_res_4843_; 
v_res_4843_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4841_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4844_, lean_object* v_ch_4845_){
_start:
{
lean_object* v___x_4847_; 
v___x_4847_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4845_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4848_, lean_object* v_ch_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4848_, v_ch_4849_);
return v_res_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4852_, lean_object* v_b_4853_, lean_object* v_f_4854_, lean_object* v_toBind_4855_, lean_object* v___f_4856_, lean_object* v_____do__lift_4857_){
_start:
{
if (lean_obj_tag(v_____do__lift_4857_) == 0)
{
lean_object* v___x_4858_; 
lean_dec(v___f_4856_);
lean_dec(v_toBind_4855_);
lean_dec(v_f_4854_);
v___x_4858_ = lean_apply_2(v_toPure_4852_, lean_box(0), v_b_4853_);
return v___x_4858_;
}
else
{
lean_object* v_val_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
lean_dec(v_toPure_4852_);
v_val_4859_ = lean_ctor_get(v_____do__lift_4857_, 0);
lean_inc(v_val_4859_);
lean_dec_ref_known(v_____do__lift_4857_, 1);
v___x_4860_ = lean_apply_2(v_f_4854_, v_val_4859_, v_b_4853_);
v___x_4861_ = lean_apply_4(v_toBind_4855_, lean_box(0), lean_box(0), v___x_4860_, v___f_4856_);
return v___x_4861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4862_, lean_object* v_inst_4863_, lean_object* v_ch_4864_, lean_object* v_f_4865_, lean_object* v_b_4866_){
_start:
{
lean_object* v_toApplicative_4867_; lean_object* v_toBind_4868_; lean_object* v_toPure_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___f_4872_; lean_object* v___f_4873_; lean_object* v___x_4874_; 
v_toApplicative_4867_ = lean_ctor_get(v_inst_4862_, 0);
v_toBind_4868_ = lean_ctor_get(v_inst_4862_, 1);
lean_inc_n(v_toBind_4868_, 2);
v_toPure_4869_ = lean_ctor_get(v_toApplicative_4867_, 1);
lean_inc_n(v_toPure_4869_, 2);
lean_inc_ref(v_ch_4864_);
v___x_4870_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4870_, 0, lean_box(0));
lean_closure_set(v___x_4870_, 1, v_ch_4864_);
lean_inc(v_inst_4863_);
v___x_4871_ = lean_apply_2(v_inst_4863_, lean_box(0), v___x_4870_);
lean_inc(v_f_4865_);
v___f_4872_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4872_, 0, v_toPure_4869_);
lean_closure_set(v___f_4872_, 1, v_inst_4862_);
lean_closure_set(v___f_4872_, 2, v_inst_4863_);
lean_closure_set(v___f_4872_, 3, v_ch_4864_);
lean_closure_set(v___f_4872_, 4, v_f_4865_);
v___f_4873_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4873_, 0, v_toPure_4869_);
lean_closure_set(v___f_4873_, 1, v_b_4866_);
lean_closure_set(v___f_4873_, 2, v_f_4865_);
lean_closure_set(v___f_4873_, 3, v_toBind_4868_);
lean_closure_set(v___f_4873_, 4, v___f_4872_);
v___x_4874_ = lean_apply_4(v_toBind_4868_, lean_box(0), lean_box(0), v___x_4871_, v___f_4873_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4875_, lean_object* v_inst_4876_, lean_object* v_inst_4877_, lean_object* v_ch_4878_, lean_object* v_f_4879_, lean_object* v_____do__lift_4880_){
_start:
{
if (lean_obj_tag(v_____do__lift_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4882_; 
lean_dec(v_f_4879_);
lean_dec_ref(v_ch_4878_);
lean_dec(v_inst_4877_);
lean_dec_ref(v_inst_4876_);
v_a_4881_ = lean_ctor_get(v_____do__lift_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref_known(v_____do__lift_4880_, 1);
v___x_4882_ = lean_apply_2(v_toPure_4875_, lean_box(0), v_a_4881_);
return v___x_4882_;
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4884_; 
lean_dec(v_toPure_4875_);
v_a_4883_ = lean_ctor_get(v_____do__lift_4880_, 0);
lean_inc(v_a_4883_);
lean_dec_ref_known(v_____do__lift_4880_, 1);
v___x_4884_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4876_, v_inst_4877_, v_ch_4878_, v_f_4879_, v_a_4883_);
return v___x_4884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4885_, lean_object* v_00_u03b1_4886_, lean_object* v_00_u03b2_4887_, lean_object* v_inst_4888_, lean_object* v_inst_4889_, lean_object* v_ch_4890_, lean_object* v_f_4891_, lean_object* v_b_4892_){
_start:
{
lean_object* v___x_4893_; 
v___x_4893_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4888_, v_inst_4889_, v_ch_4890_, v_f_4891_, v_b_4892_);
return v___x_4893_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4894_, lean_object* v_inst_4895_, lean_object* v_ch_4896_, lean_object* v_b_4897_, lean_object* v_f_4898_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4894_, v_inst_4895_, v_ch_4896_, v_f_4898_, v_b_4897_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4900_, lean_object* v_00_u03b1_4901_, lean_object* v_inst_4902_, lean_object* v_inst_4903_, lean_object* v_00_u03b2_4904_, lean_object* v_ch_4905_, lean_object* v_b_4906_, lean_object* v_f_4907_){
_start:
{
lean_object* v___x_4908_; 
v___x_4908_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4902_, v_inst_4903_, v_ch_4905_, v_f_4907_, v_b_4906_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4909_, lean_object* v_inst_4910_, lean_object* v_00_u03b2_4911_, lean_object* v_ch_4912_, lean_object* v_b_4913_, lean_object* v_f_4914_){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4909_, v_inst_4910_, v_ch_4912_, v_f_4914_, v_b_4913_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4916_, lean_object* v_inst_4917_){
_start:
{
lean_object* v___f_4918_; 
v___f_4918_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4918_, 0, v_inst_4916_);
lean_closure_set(v___f_4918_, 1, v_inst_4917_);
return v___f_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4919_, lean_object* v_00_u03b1_4920_, lean_object* v_inst_4921_, lean_object* v_inst_4922_){
_start:
{
lean_object* v___f_4923_; 
v___f_4923_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4923_, 0, v_inst_4921_);
lean_closure_set(v___f_4923_, 1, v_inst_4922_);
return v___f_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Std_CloseableChannel_new___redArg(v_capacity_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4927_, lean_object* v_a_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Std_Channel_new___redArg(v_capacity_4927_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4930_, lean_object* v_capacity_4931_){
_start:
{
lean_object* v___x_4933_; 
v___x_4933_ = l_Std_CloseableChannel_new___redArg(v_capacity_4931_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4934_, lean_object* v_capacity_4935_, lean_object* v_a_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Std_Channel_new(v_00_u03b1_4934_, v_capacity_4935_);
return v_res_4937_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4938_, lean_object* v_v_4939_){
_start:
{
uint8_t v___x_4941_; 
v___x_4941_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4938_, v_v_4939_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4942_, lean_object* v_v_4943_, lean_object* v_a_4944_){
_start:
{
uint8_t v_res_4945_; lean_object* v_r_4946_; 
v_res_4945_ = l_Std_Channel_trySend___redArg(v_ch_4942_, v_v_4943_);
v_r_4946_ = lean_box(v_res_4945_);
return v_r_4946_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4947_, lean_object* v_ch_4948_, lean_object* v_v_4949_){
_start:
{
uint8_t v___x_4951_; 
v___x_4951_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4948_, v_v_4949_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4952_, lean_object* v_ch_4953_, lean_object* v_v_4954_, lean_object* v_a_4955_){
_start:
{
uint8_t v_res_4956_; lean_object* v_r_4957_; 
v_res_4956_ = l_Std_Channel_trySend(v_00_u03b1_4952_, v_ch_4953_, v_v_4954_);
v_r_4957_ = lean_box(v_res_4956_);
return v_r_4957_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4958_; lean_object* v___x_4959_; 
v___x_4958_ = lean_box(0);
v___x_4959_ = lean_task_pure(v___x_4958_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4960_){
_start:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_142__overap_4965_; lean_object* v___x_4966_; 
v___x_4962_ = l_instMonadBaseIO;
v___x_4963_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4964_ = l_instInhabitedOfMonad___redArg(v___x_4962_, v___x_4963_);
v___x_142__overap_4965_ = lean_panic_fn_borrowed(v___x_4964_, v_msg_4960_);
lean_dec(v___x_4964_);
v___x_4966_ = lean_apply_1(v___x_142__overap_4965_, lean_box(0));
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4967_);
return v_res_4969_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4973_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4974_ = lean_unsigned_to_nat(21u);
v___x_4975_ = lean_unsigned_to_nat(869u);
v___x_4976_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4977_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4978_ = l_mkPanicMessageWithDecl(v___x_4977_, v___x_4976_, v___x_4975_, v___x_4974_, v___x_4973_);
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4979_){
_start:
{
if (lean_obj_tag(v_x_4979_) == 0)
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4981_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4982_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4981_);
return v___x_4982_;
}
else
{
lean_object* v___x_4983_; 
v___x_4983_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4983_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4984_, lean_object* v___y_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l_Std_Channel_send___redArg___lam__0(v_x_4984_);
lean_dec_ref(v_x_4984_);
return v_res_4986_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4988_, lean_object* v_v_4989_){
_start:
{
lean_object* v___x_4991_; lean_object* v___f_4992_; lean_object* v___x_4993_; uint8_t v___x_4994_; lean_object* v___x_4995_; 
v___x_4991_ = l_Std_CloseableChannel_send___redArg(v_ch_4988_, v_v_4989_);
v___f_4992_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4993_ = lean_unsigned_to_nat(0u);
v___x_4994_ = 1;
v___x_4995_ = lean_io_bind_task(v___x_4991_, v___f_4992_, v___x_4993_, v___x_4994_);
return v___x_4995_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4996_, lean_object* v_v_4997_, lean_object* v_a_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l_Std_Channel_send___redArg(v_ch_4996_, v_v_4997_);
return v_res_4999_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_5000_, lean_object* v_ch_5001_, lean_object* v_v_5002_){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = l_Std_Channel_send___redArg(v_ch_5001_, v_v_5002_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_5005_, lean_object* v_ch_5006_, lean_object* v_v_5007_, lean_object* v_a_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l_Std_Channel_send(v_00_u03b1_5005_, v_ch_5006_, v_v_5007_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_5010_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5010_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_5013_, lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l_Std_Channel_tryRecv___redArg(v_ch_5013_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_5016_, lean_object* v_ch_5017_){
_start:
{
lean_object* v___x_5019_; 
v___x_5019_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5017_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_5020_, lean_object* v_ch_5021_, lean_object* v_a_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Std_Channel_tryRecv(v_00_u03b1_5020_, v_ch_5021_);
return v_res_5023_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5025_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_5026_ = lean_unsigned_to_nat(16u);
v___x_5027_ = lean_unsigned_to_nat(880u);
v___x_5028_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_5029_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_5030_ = l_mkPanicMessageWithDecl(v___x_5029_, v___x_5028_, v___x_5027_, v___x_5026_, v___x_5025_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_5031_, lean_object* v_x_5032_){
_start:
{
if (lean_obj_tag(v_x_5032_) == 0)
{
lean_object* v___x_5034_; lean_object* v___x_140__overap_5035_; lean_object* v___x_5036_; 
v___x_5034_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_140__overap_5035_ = l_panic___redArg(v___x_5031_, v___x_5034_);
v___x_5036_ = lean_apply_1(v___x_140__overap_5035_, lean_box(0));
return v___x_5036_;
}
else
{
lean_object* v_val_5037_; lean_object* v___x_5038_; 
v_val_5037_ = lean_ctor_get(v_x_5032_, 0);
lean_inc(v_val_5037_);
lean_dec_ref_known(v_x_5032_, 1);
v___x_5038_ = lean_task_pure(v_val_5037_);
return v___x_5038_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_5039_, lean_object* v_x_5040_, lean_object* v___y_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_Std_Channel_recv___redArg___lam__0(v___x_5039_, v_x_5040_);
lean_dec_ref(v___x_5039_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_5043_, lean_object* v_ch_5044_){
_start:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___f_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; lean_object* v___x_5053_; 
v___x_5046_ = l_instMonadBaseIO;
v___x_5047_ = l_Std_CloseableChannel_recv___redArg(v_ch_5044_);
v___x_5048_ = lean_task_pure(v_inst_5043_);
v___x_5049_ = l_instInhabitedOfMonad___redArg(v___x_5046_, v___x_5048_);
v___f_5050_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5050_, 0, v___x_5049_);
v___x_5051_ = lean_unsigned_to_nat(0u);
v___x_5052_ = 1;
v___x_5053_ = lean_io_bind_task(v___x_5047_, v___f_5050_, v___x_5051_, v___x_5052_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_5054_, lean_object* v_ch_5055_, lean_object* v_a_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_Std_Channel_recv___redArg(v_inst_5054_, v_ch_5055_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5058_, lean_object* v_inst_5059_, lean_object* v_ch_5060_){
_start:
{
lean_object* v___x_5062_; 
v___x_5062_ = l_Std_Channel_recv___redArg(v_inst_5059_, v_ch_5060_);
return v___x_5062_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5063_, lean_object* v_inst_5064_, lean_object* v_ch_5065_, lean_object* v_a_5066_){
_start:
{
lean_object* v_res_5067_; 
v_res_5067_ = l_Std_Channel_recv(v_00_u03b1_5063_, v_inst_5064_, v_ch_5065_);
return v_res_5067_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5068_){
_start:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5070_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5068_);
v___x_5071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5070_);
v___x_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5072_, 0, v___x_5071_);
return v___x_5072_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5073_, lean_object* v___y_5074_){
_start:
{
lean_object* v_res_5075_; 
v_res_5075_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5073_);
return v_res_5075_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5079_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5080_ = lean_unsigned_to_nat(14u);
v___x_5081_ = lean_unsigned_to_nat(22u);
v___x_5082_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5083_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5084_ = l_mkPanicMessageWithDecl(v___x_5083_, v___x_5082_, v___x_5081_, v___x_5080_, v___x_5079_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5085_, lean_object* v_inst_5086_, lean_object* v_x_5087_){
_start:
{
lean_object* v___y_5090_; lean_object* v___y_5094_; 
if (lean_obj_tag(v_x_5087_) == 0)
{
lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5096_ = lean_box(0);
v___x_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5096_);
return v___x_5097_;
}
else
{
lean_object* v_val_5098_; 
v_val_5098_ = lean_ctor_get(v_x_5087_, 0);
lean_inc(v_val_5098_);
lean_dec_ref_known(v_x_5087_, 1);
if (lean_obj_tag(v_val_5098_) == 0)
{
lean_object* v_a_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5106_; 
v_a_5099_ = lean_ctor_get(v_val_5098_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v_val_5098_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5101_ = v_val_5098_;
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_a_5099_);
lean_dec(v_val_5098_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5104_; 
if (v_isShared_5102_ == 0)
{
v___x_5104_ = v___x_5101_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
v___y_5090_ = v___x_5104_;
goto v___jp_5089_;
}
}
}
else
{
lean_object* v_a_5107_; 
v_a_5107_ = lean_ctor_get(v_val_5098_, 0);
lean_inc(v_a_5107_);
lean_dec_ref_known(v_val_5098_, 1);
if (lean_obj_tag(v_a_5107_) == 0)
{
lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5108_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5109_ = l_panic___redArg(v_inst_5086_, v___x_5108_);
v___y_5094_ = v___x_5109_;
goto v___jp_5093_;
}
else
{
lean_object* v_val_5110_; 
v_val_5110_ = lean_ctor_get(v_a_5107_, 0);
lean_inc(v_val_5110_);
lean_dec_ref_known(v_a_5107_, 1);
v___y_5094_ = v_val_5110_;
goto v___jp_5093_;
}
}
}
v___jp_5089_:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; 
v___x_5091_ = lean_io_promise_resolve(v___y_5090_, v_promise_5085_);
v___x_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5092_, 0, v___x_5091_);
return v___x_5092_;
}
v___jp_5093_:
{
lean_object* v___x_5095_; 
v___x_5095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5095_, 0, v___y_5094_);
v___y_5090_ = v___x_5095_;
goto v___jp_5089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5111_, lean_object* v_inst_5112_, lean_object* v_x_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5111_, v_inst_5112_, v_x_5113_);
lean_dec(v_inst_5112_);
lean_dec(v_promise_5111_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5116_, lean_object* v___f_5117_, lean_object* v_x_5118_){
_start:
{
lean_object* v_val_5121_; 
if (lean_obj_tag(v_x_5118_) == 0)
{
lean_object* v___x_5123_; 
lean_dec_ref(v___f_5117_);
v___x_5123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5123_, 0, v_x_5118_);
return v___x_5123_;
}
else
{
lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5139_; 
v_isSharedCheck_5139_ = !lean_is_exclusive(v_x_5118_);
if (v_isSharedCheck_5139_ == 0)
{
lean_object* v_unused_5140_; 
v_unused_5140_ = lean_ctor_get(v_x_5118_, 0);
lean_dec(v_unused_5140_);
v___x_5125_ = v_x_5118_;
v_isShared_5126_ = v_isSharedCheck_5139_;
goto v_resetjp_5124_;
}
else
{
lean_dec(v_x_5118_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5139_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5127_; lean_object* v___x_5128_; uint8_t v___x_5129_; lean_object* v___x_5130_; 
v___x_5127_ = lean_io_promise_result_opt(v_a_5116_);
v___x_5128_ = lean_unsigned_to_nat(0u);
v___x_5129_ = 1;
v___x_5130_ = l_EIO_chainTask___redArg(v___x_5127_, v___f_5117_, v___x_5128_, v___x_5129_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v___x_5133_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5130_, 1);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 0, v_a_5131_);
v___x_5133_ = v___x_5125_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5131_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
v_val_5121_ = v___x_5133_;
goto v___jp_5120_;
}
}
else
{
lean_object* v_a_5135_; lean_object* v___x_5137_; 
v_a_5135_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5130_, 1);
if (v_isShared_5126_ == 0)
{
lean_ctor_set_tag(v___x_5125_, 0);
lean_ctor_set(v___x_5125_, 0, v_a_5135_);
v___x_5137_ = v___x_5125_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5138_; 
v_reuseFailAlloc_5138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5135_);
v___x_5137_ = v_reuseFailAlloc_5138_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
v_val_5121_ = v___x_5137_;
goto v___jp_5120_;
}
}
}
}
v___jp_5120_:
{
lean_object* v___x_5122_; 
v___x_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5122_, 0, v_val_5121_);
return v___x_5122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5141_, lean_object* v___f_5142_, lean_object* v_x_5143_, lean_object* v___y_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5141_, v___f_5142_, v_x_5143_);
lean_dec(v_a_5141_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5146_, lean_object* v_finished_5147_, lean_object* v___f_5148_, lean_object* v_x_5149_){
_start:
{
if (lean_obj_tag(v_x_5149_) == 0)
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5159_; 
lean_dec_ref(v___f_5148_);
lean_dec(v_finished_5147_);
lean_dec_ref(v_sel_5146_);
v_a_5151_ = lean_ctor_get(v_x_5149_, 0);
v_isSharedCheck_5159_ = !lean_is_exclusive(v_x_5149_);
if (v_isSharedCheck_5159_ == 0)
{
v___x_5153_ = v_x_5149_;
v_isShared_5154_ = v_isSharedCheck_5159_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v_x_5149_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5159_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5158_; 
v_reuseFailAlloc_5158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5158_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
lean_object* v___x_5157_; 
v___x_5157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5156_);
return v___x_5157_;
}
}
}
else
{
lean_object* v_a_5160_; lean_object* v_registerFn_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___f_5164_; lean_object* v___x_5165_; uint8_t v___x_5166_; lean_object* v___x_5167_; 
v_a_5160_ = lean_ctor_get(v_x_5149_, 0);
lean_inc_n(v_a_5160_, 2);
lean_dec_ref_known(v_x_5149_, 1);
v_registerFn_5161_ = lean_ctor_get(v_sel_5146_, 1);
lean_inc_ref(v_registerFn_5161_);
lean_dec_ref(v_sel_5146_);
v___x_5162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5162_, 0, v_finished_5147_);
lean_ctor_set(v___x_5162_, 1, v_a_5160_);
v___x_5163_ = lean_apply_2(v_registerFn_5161_, v___x_5162_, lean_box(0));
v___f_5164_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5164_, 0, v_a_5160_);
lean_closure_set(v___f_5164_, 1, v___f_5148_);
v___x_5165_ = lean_unsigned_to_nat(0u);
v___x_5166_ = 0;
v___x_5167_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5165_, v___x_5166_, v___x_5163_, v___f_5164_);
return v___x_5167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5168_, lean_object* v_finished_5169_, lean_object* v___f_5170_, lean_object* v_x_5171_, lean_object* v___y_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5168_, v_finished_5169_, v___f_5170_, v_x_5171_);
return v_res_5173_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5174_, lean_object* v_sel_5175_, lean_object* v_waiter_5176_){
_start:
{
lean_object* v___x_5178_; lean_object* v_finished_5179_; lean_object* v_promise_5180_; lean_object* v___f_5181_; lean_object* v___f_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; uint8_t v___x_5186_; lean_object* v___x_5187_; 
v___x_5178_ = lean_io_promise_new();
v_finished_5179_ = lean_ctor_get(v_waiter_5176_, 0);
lean_inc(v_finished_5179_);
v_promise_5180_ = lean_ctor_get(v_waiter_5176_, 1);
lean_inc(v_promise_5180_);
lean_dec_ref(v_waiter_5176_);
v___f_5181_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5181_, 0, v_promise_5180_);
lean_closure_set(v___f_5181_, 1, v_inst_5174_);
v___f_5182_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5182_, 0, v_sel_5175_);
lean_closure_set(v___f_5182_, 1, v_finished_5179_);
lean_closure_set(v___f_5182_, 2, v___f_5181_);
v___x_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5178_);
v___x_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5183_);
v___x_5185_ = lean_unsigned_to_nat(0u);
v___x_5186_ = 0;
v___x_5187_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5185_, v___x_5186_, v___x_5184_, v___f_5182_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5188_, lean_object* v_sel_5189_, lean_object* v_waiter_5190_, lean_object* v___y_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5188_, v_sel_5189_, v_waiter_5190_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5193_, lean_object* v_ch_5194_){
_start:
{
lean_object* v_sel_5195_; lean_object* v_unregisterFn_5196_; lean_object* v___f_5197_; lean_object* v___f_5198_; lean_object* v___x_5199_; 
lean_inc_ref(v_ch_5194_);
v_sel_5195_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5194_);
v_unregisterFn_5196_ = lean_ctor_get(v_sel_5195_, 2);
lean_inc_ref(v_unregisterFn_5196_);
v___f_5197_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5197_, 0, v_ch_5194_);
v___f_5198_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5198_, 0, v_inst_5193_);
lean_closure_set(v___f_5198_, 1, v_sel_5195_);
v___x_5199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5199_, 0, v___f_5197_);
lean_ctor_set(v___x_5199_, 1, v___f_5198_);
lean_ctor_set(v___x_5199_, 2, v_unregisterFn_5196_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5200_, lean_object* v_inst_5201_, lean_object* v_ch_5202_){
_start:
{
lean_object* v___x_5203_; 
v___x_5203_ = l_Std_Channel_recvSelector___redArg(v_inst_5201_, v_ch_5202_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5204_, lean_object* v_inst_5205_, lean_object* v_ch_5206_, lean_object* v_prio_5207_, lean_object* v_v_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5204_, v_inst_5205_, v_ch_5206_, v_prio_5207_, v_v_5208_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5211_, lean_object* v_f_5212_, lean_object* v_ch_5213_, lean_object* v_prio_5214_){
_start:
{
lean_object* v___x_5216_; lean_object* v___f_5217_; uint8_t v___x_5218_; lean_object* v___x_5219_; 
lean_inc_ref(v_ch_5213_);
lean_inc(v_inst_5211_);
v___x_5216_ = l_Std_Channel_recv___redArg(v_inst_5211_, v_ch_5213_);
lean_inc(v_prio_5214_);
v___f_5217_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5217_, 0, v_f_5212_);
lean_closure_set(v___f_5217_, 1, v_inst_5211_);
lean_closure_set(v___f_5217_, 2, v_ch_5213_);
lean_closure_set(v___f_5217_, 3, v_prio_5214_);
v___x_5218_ = 0;
v___x_5219_ = lean_io_bind_task(v___x_5216_, v___f_5217_, v_prio_5214_, v___x_5218_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5220_, lean_object* v_inst_5221_, lean_object* v_ch_5222_, lean_object* v_prio_5223_, lean_object* v_v_5224_){
_start:
{
lean_object* v___x_5226_; lean_object* v___x_5227_; 
lean_inc_ref(v_f_5220_);
v___x_5226_ = lean_apply_2(v_f_5220_, v_v_5224_, lean_box(0));
v___x_5227_ = l_Std_Channel_forAsync___redArg(v_inst_5221_, v_f_5220_, v_ch_5222_, v_prio_5223_);
return v___x_5227_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5228_, lean_object* v_f_5229_, lean_object* v_ch_5230_, lean_object* v_prio_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l_Std_Channel_forAsync___redArg(v_inst_5228_, v_f_5229_, v_ch_5230_, v_prio_5231_);
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5234_, lean_object* v_inst_5235_, lean_object* v_f_5236_, lean_object* v_ch_5237_, lean_object* v_prio_5238_){
_start:
{
lean_object* v___x_5240_; 
v___x_5240_ = l_Std_Channel_forAsync___redArg(v_inst_5235_, v_f_5236_, v_ch_5237_, v_prio_5238_);
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5241_, lean_object* v_inst_5242_, lean_object* v_f_5243_, lean_object* v_ch_5244_, lean_object* v_prio_5245_, lean_object* v_a_5246_){
_start:
{
lean_object* v_res_5247_; 
v_res_5247_ = l_Std_Channel_forAsync(v_00_u03b1_5241_, v_inst_5242_, v_f_5243_, v_ch_5244_, v_prio_5245_);
return v_res_5247_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5248_, lean_object* v_channel_5249_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Std_Channel_recvSelector___redArg(v_inst_5248_, v_channel_5249_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5251_){
_start:
{
lean_object* v___f_5252_; lean_object* v___f_5253_; lean_object* v___x_5254_; 
v___f_5252_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5252_, 0, v_inst_5251_);
v___f_5253_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1));
v___x_5254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5254_, 0, v___f_5252_);
lean_ctor_set(v___x_5254_, 1, v___f_5253_);
return v___x_5254_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5255_, lean_object* v_inst_5256_){
_start:
{
lean_object* v___x_5257_; 
v___x_5257_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5256_);
return v___x_5257_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5258_){
_start:
{
lean_object* v___x_5259_; 
v___x_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5259_, 0, v_a_5258_);
return v___x_5259_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5260_, lean_object* v_x_5261_){
_start:
{
if (lean_obj_tag(v_x_5261_) == 0)
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5271_; 
lean_dec_ref(v___f_5260_);
v_a_5263_ = lean_ctor_get(v_x_5261_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v_x_5261_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5265_ = v_x_5261_;
v_isShared_5266_ = v_isSharedCheck_5271_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v_x_5261_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5271_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5270_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
lean_object* v___x_5269_; 
v___x_5269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5269_, 0, v___x_5268_);
return v___x_5269_;
}
}
}
else
{
lean_object* v_a_5272_; 
v_a_5272_ = lean_ctor_get(v_x_5261_, 0);
lean_inc(v_a_5272_);
lean_dec_ref_known(v_x_5261_, 1);
if (lean_obj_tag(v_a_5272_) == 0)
{
lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5281_; 
lean_dec_ref(v___f_5260_);
v_a_5273_ = lean_ctor_get(v_a_5272_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v_a_5272_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5275_ = v_a_5272_;
v_isShared_5276_ = v_isSharedCheck_5281_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v_a_5272_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5281_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5276_ == 0)
{
v___x_5278_ = v___x_5275_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5273_);
v___x_5278_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
lean_object* v___x_5279_; 
v___x_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
return v___x_5279_;
}
}
}
else
{
lean_object* v_a_5282_; lean_object* v___x_5283_; uint8_t v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v_a_5282_ = lean_ctor_get(v_a_5272_, 0);
lean_inc(v_a_5282_);
lean_dec_ref_known(v_a_5272_, 1);
v___x_5283_ = lean_unsigned_to_nat(0u);
v___x_5284_ = 0;
v___x_5285_ = lean_task_map(v___f_5260_, v_a_5282_, v___x_5283_, v___x_5284_);
v___x_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5286_, 0, v___x_5285_);
return v___x_5286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5287_, lean_object* v_x_5288_, lean_object* v___y_5289_){
_start:
{
lean_object* v_res_5290_; 
v_res_5290_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5287_, v_x_5288_);
return v_res_5290_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5291_, lean_object* v___f_5292_, lean_object* v_receiver_5293_){
_start:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; uint8_t v___x_5300_; lean_object* v___x_5301_; 
v___x_5295_ = l_Std_Channel_recv___redArg(v_inst_5291_, v_receiver_5293_);
v___x_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5295_);
v___x_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5297_, 0, v___x_5296_);
v___x_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5297_);
v___x_5299_ = lean_unsigned_to_nat(0u);
v___x_5300_ = 0;
v___x_5301_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5299_, v___x_5300_, v___x_5298_, v___f_5292_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5302_, lean_object* v___f_5303_, lean_object* v_receiver_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_res_5306_; 
v_res_5306_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5302_, v___f_5303_, v_receiver_5304_);
return v_res_5306_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5310_){
_start:
{
lean_object* v___f_5311_; lean_object* v___f_5312_; 
v___f_5311_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5312_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5312_, 0, v_inst_5310_);
lean_closure_set(v___f_5312_, 1, v___f_5311_);
return v___f_5312_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5313_, lean_object* v_inst_5314_){
_start:
{
lean_object* v___x_5315_; 
v___x_5315_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5314_);
return v___x_5315_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__0(lean_object* v_a_5316_){
_start:
{
lean_object* v___x_5317_; 
v___x_5317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5317_, 0, v_a_5316_);
return v___x_5317_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_5318_, lean_object* v_x_5319_){
_start:
{
if (lean_obj_tag(v_x_5319_) == 0)
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5329_; 
lean_dec_ref(v___f_5318_);
v_a_5321_ = lean_ctor_get(v_x_5319_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v_x_5319_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5323_ = v_x_5319_;
v_isShared_5324_ = v_isSharedCheck_5329_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v_x_5319_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5329_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
lean_object* v___x_5327_; 
v___x_5327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5326_);
return v___x_5327_;
}
}
}
else
{
lean_object* v_a_5330_; lean_object* v___x_5331_; uint8_t v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v_a_5330_ = lean_ctor_get(v_x_5319_, 0);
lean_inc(v_a_5330_);
lean_dec_ref_known(v_x_5319_, 1);
v___x_5331_ = lean_unsigned_to_nat(0u);
v___x_5332_ = 0;
v___x_5333_ = lean_task_map(v___f_5318_, v_a_5330_, v___x_5331_, v___x_5332_);
v___x_5334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5334_, 0, v___x_5333_);
return v___x_5334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_5335_, lean_object* v_x_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v_res_5338_; 
v_res_5338_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__1(v___f_5335_, v_x_5336_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5339_, lean_object* v_receiver_5340_, lean_object* v_x_5341_){
_start:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; uint8_t v___x_5347_; lean_object* v___x_5348_; 
v___x_5343_ = l_Std_Channel_send___redArg(v_receiver_5340_, v_x_5341_);
v___x_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5344_, 0, v___x_5343_);
v___x_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5345_, 0, v___x_5344_);
v___x_5346_ = lean_unsigned_to_nat(0u);
v___x_5347_ = 0;
v___x_5348_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5346_, v___x_5347_, v___x_5345_, v___f_5339_);
return v___x_5348_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5349_, lean_object* v_receiver_5350_, lean_object* v_x_5351_, lean_object* v___y_5352_){
_start:
{
lean_object* v_res_5353_; 
v_res_5353_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__2(v___f_5349_, v_receiver_5350_, v_x_5351_);
return v_res_5353_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_5359_; lean_object* v___f_5360_; lean_object* v___f_5361_; 
v___x_5359_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_5360_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___f_5361_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5361_, 0, v___f_5360_);
lean_closure_set(v___f_5361_, 1, v___x_5359_);
return v___f_5361_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___f_5362_; lean_object* v___f_5363_; lean_object* v___f_5364_; lean_object* v___x_5365_; 
v___f_5362_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_5363_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3);
v___f_5364_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___x_5365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5365_, 0, v___f_5364_);
lean_ctor_set(v___x_5365_, 1, v___f_5363_);
lean_ctor_set(v___x_5365_, 2, v___f_5362_);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5366_, lean_object* v_inst_5367_){
_start:
{
lean_object* v___x_5368_; 
v___x_5368_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4);
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

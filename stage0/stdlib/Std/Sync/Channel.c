// Lean compiler output
// Module: Std.Sync.Channel
// Imports: public import Init.Data.Queue public import Std.Sync.Mutex public import Std.Internal.Async.IO import Init.Data.Vector.Basic import Init.Data.Option.BasicAux import Init.Omega
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
lean_object* l_instMonadST(lean_object*);
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
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonad(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00Std_Channel_send_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_Channel_send_spec__0___closed__1;
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
lean_dec_ref(v_t_178_);
v___x_181_ = lean_apply_1(v_k_179_, v_promise_180_);
return v___x_181_;
}
else
{
lean_object* v_finished_182_; lean_object* v___x_183_; 
v_finished_182_ = lean_ctor_get(v_t_178_, 0);
lean_inc_ref(v_finished_182_);
lean_dec_ref(v_t_178_);
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
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(lean_object* v_x_216_, lean_object* v_w_217_, lean_object* v_lose_218_){
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg___boxed(lean_object* v_x_235_, lean_object* v_w_236_, lean_object* v_lose_237_, lean_object* v___y_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_235_, v_w_236_, v_lose_237_);
lean_dec_ref(v_w_236_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(lean_object* v_00_u03b1_241_, lean_object* v_x_242_, lean_object* v_w_243_, lean_object* v_lose_244_){
_start:
{
uint8_t v___x_246_; 
v___x_246_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_242_, v_w_243_, v_lose_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___boxed(lean_object* v_00_u03b1_247_, lean_object* v_x_248_, lean_object* v_w_249_, lean_object* v_lose_250_, lean_object* v___y_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(v_00_u03b1_247_, v_x_248_, v_w_249_, v_lose_250_);
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
uint8_t v___x_673__boxed_258_; uint8_t v_res_259_; lean_object* v_r_260_; 
v___x_673__boxed_258_ = lean_unbox(v___x_256_);
v_res_259_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(v___x_673__boxed_258_);
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
v___x_272_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_265_, v_finished_270_, v_lose_271_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(lean_object* v_v_328_, lean_object* v___y_329_){
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg___boxed(lean_object* v_v_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_362_, v___y_363_);
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
v___x_371_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_366_, v___y_367_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(lean_object* v_00_u03b1_401_, lean_object* v_v_402_, lean_object* v_b_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_402_, v___y_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_407_, lean_object* v_v_408_, lean_object* v_b_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(v_00_u03b1_407_, v_v_408_, v_b_409_, v___y_410_);
lean_dec(v___y_410_);
return v_res_412_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
v___x_417_ = lean_task_pure(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
v___x_421_ = lean_task_pure(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(lean_object* v_ch_422_, lean_object* v_v_423_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_422_, v_v_423_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___boxed(lean_object* v_ch_428_, lean_object* v_v_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_428_, v_v_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(lean_object* v_00_u03b1_432_, lean_object* v_ch_433_, lean_object* v_v_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_433_, v_v_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___boxed(lean_object* v_00_u03b1_437_, lean_object* v_ch_438_, lean_object* v_v_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(v_00_u03b1_437_, v_ch_438_, v_v_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(lean_object* v_mutex_442_, lean_object* v_k_443_){
_start:
{
lean_object* v_ref_445_; lean_object* v_mutex_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_ref_445_ = lean_ctor_get(v_mutex_442_, 0);
lean_inc(v_ref_445_);
v_mutex_446_ = lean_ctor_get(v_mutex_442_, 1);
lean_inc(v_mutex_446_);
lean_dec_ref(v_mutex_442_);
v___x_447_ = lean_io_basemutex_lock(v_mutex_446_);
v___x_448_ = lean_apply_2(v_k_443_, v_ref_445_, lean_box(0));
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_457_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_io_basemutex_unlock(v_mutex_446_);
lean_dec(v_mutex_446_);
if (v_isShared_452_ == 0)
{
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_449_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_a_458_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v___x_448_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_448_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_io_basemutex_unlock(v_mutex_446_);
lean_dec(v_mutex_446_);
if (v_isShared_461_ == 0)
{
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_458_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg___boxed(lean_object* v_mutex_467_, lean_object* v_k_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_467_, v_k_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(lean_object* v_00_u03b1_471_, lean_object* v_00_u03b2_472_, lean_object* v_mutex_473_, lean_object* v_k_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_473_, v_k_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___boxed(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_mutex_479_, lean_object* v_k_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(v_00_u03b1_477_, v_00_u03b2_478_, v_mutex_479_, v_k_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(lean_object* v_as_483_, size_t v_sz_484_, size_t v_i_485_, lean_object* v_b_486_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_lt(v_i_485_, v_sz_484_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_b_486_);
return v___x_489_;
}
else
{
lean_object* v_a_490_; lean_object* v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; size_t v___x_494_; size_t v___x_495_; 
v_a_490_ = lean_array_uget_borrowed(v_as_483_, v_i_485_);
v___x_491_ = lean_box(0);
v___x_492_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_490_, v___x_491_);
v___x_493_ = lean_box(0);
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_i_485_, v___x_494_);
v_i_485_ = v___x_495_;
v_b_486_ = v___x_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg___boxed(lean_object* v_as_497_, lean_object* v_sz_498_, lean_object* v_i_499_, lean_object* v_b_500_, lean_object* v___y_501_){
_start:
{
size_t v_sz_boxed_502_; size_t v_i_boxed_503_; lean_object* v_res_504_; 
v_sz_boxed_502_ = lean_unbox_usize(v_sz_498_);
lean_dec(v_sz_498_);
v_i_boxed_503_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_497_, v_sz_boxed_502_, v_i_boxed_503_, v_b_500_);
lean_dec_ref(v_as_497_);
return v_res_504_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_Queue_empty(lean_box(0));
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; uint8_t v_closed_509_; 
v___x_508_ = lean_st_ref_get(v___y_506_);
v_closed_509_ = lean_ctor_get_uint8(v___x_508_, sizeof(void*)*2);
if (v_closed_509_ == 0)
{
lean_object* v_values_510_; lean_object* v_consumers_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_534_; 
v_values_510_ = lean_ctor_get(v___x_508_, 0);
v_consumers_511_ = lean_ctor_get(v___x_508_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_534_ == 0)
{
v___x_513_ = v___x_508_;
v_isShared_514_ = v_isSharedCheck_534_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_consumers_511_);
lean_inc(v_values_510_);
lean_dec(v___x_508_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_534_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; size_t v_sz_517_; size_t v___x_518_; lean_object* v___x_519_; 
v___x_515_ = l_Std_Queue_toArray___redArg(v_consumers_511_);
v___x_516_ = lean_box(0);
v_sz_517_ = lean_array_size(v___x_515_);
v___x_518_ = ((size_t)0ULL);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v___x_515_, v_sz_517_, v___x_518_, v___x_516_);
lean_dec_ref(v___x_515_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_532_; 
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v___x_519_, 0);
lean_dec(v_unused_533_);
v___x_521_ = v___x_519_;
v_isShared_522_ = v_isSharedCheck_532_;
goto v_resetjp_520_;
}
else
{
lean_dec(v___x_519_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_532_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_526_; 
v___x_523_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
v___x_524_ = 1;
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_523_);
v___x_526_ = v___x_513_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_values_510_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_523_);
v___x_526_ = v_reuseFailAlloc_531_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*2, v___x_524_);
v___x_527_ = lean_st_ref_set(v___y_506_, v___x_526_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_516_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_516_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_del_object(v___x_513_);
lean_dec_ref(v_values_510_);
return v___x_519_;
}
}
}
else
{
uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v___x_508_);
v___x_535_ = 1;
v___x_536_ = lean_box(v___x_535_);
v___x_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed(lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(v___y_538_);
lean_dec(v___y_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(lean_object* v_ch_542_){
_start:
{
lean_object* v___f_544_; lean_object* v___x_545_; 
v___f_544_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0));
v___x_545_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_542_, v___f_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___boxed(lean_object* v_ch_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(lean_object* v_00_u03b1_549_, lean_object* v_ch_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___boxed(lean_object* v_00_u03b1_553_, lean_object* v_ch_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(v_00_u03b1_553_, v_ch_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(lean_object* v_00_u03b1_557_, lean_object* v_as_558_, size_t v_sz_559_, size_t v_i_560_, lean_object* v_b_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_558_, v_sz_559_, v_i_560_, v_b_561_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___boxed(lean_object* v_00_u03b1_565_, lean_object* v_as_566_, lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_sz_boxed_572_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_573_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(v_00_u03b1_565_, v_as_566_, v_sz_boxed_572_, v_i_boxed_573_, v_b_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v_as_566_);
return v_res_574_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; uint8_t v_closed_578_; 
v___x_577_ = lean_st_ref_get(v___y_575_);
v_closed_578_ = lean_ctor_get_uint8(v___x_577_, sizeof(void*)*2);
lean_dec(v___x_577_);
return v_closed_578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v_res_581_; lean_object* v_r_582_; 
v_res_581_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(v___y_579_);
lean_dec(v___y_579_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(lean_object* v_ch_584_){
_start:
{
lean_object* v___f_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___f_586_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0));
v___x_587_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_584_, v___f_586_);
v___x_588_ = lean_unbox(v___x_587_);
lean_dec(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___boxed(lean_object* v_ch_589_, lean_object* v_a_590_){
_start:
{
uint8_t v_res_591_; lean_object* v_r_592_; 
v_res_591_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_589_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(lean_object* v_00_u03b1_593_, lean_object* v_ch_594_){
_start:
{
uint8_t v___x_596_; 
v___x_596_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_594_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___boxed(lean_object* v_00_u03b1_597_, lean_object* v_ch_598_, lean_object* v_a_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(v_00_u03b1_597_, v_ch_598_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_602_, lean_object* v_fst_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_toPure_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_toPure_605_ = lean_ctor_get(v_toApplicative_602_, 1);
lean_inc(v_toPure_605_);
lean_dec_ref(v_toApplicative_602_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_fst_603_);
v___x_607_ = lean_apply_2(v_toPure_605_, lean_box(0), v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_608_, lean_object* v_a_609_, lean_object* v_inst_610_, lean_object* v_toBind_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_values_613_; lean_object* v_consumers_614_; uint8_t v_closed_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_633_; 
v_values_613_ = lean_ctor_get(v_a_612_, 0);
v_consumers_614_ = lean_ctor_get(v_a_612_, 1);
v_closed_615_ = lean_ctor_get_uint8(v_a_612_, sizeof(void*)*2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_612_);
if (v_isSharedCheck_633_ == 0)
{
v___x_617_ = v_a_612_;
v_isShared_618_ = v_isSharedCheck_633_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_consumers_614_);
lean_inc(v_values_613_);
lean_dec(v_a_612_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_633_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_Queue_dequeue_x3f___redArg(v_values_613_);
if (lean_obj_tag(v___x_619_) == 1)
{
lean_object* v_val_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___f_623_; lean_object* v___x_625_; 
v_val_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_val_620_);
lean_dec_ref(v___x_619_);
v_fst_621_ = lean_ctor_get(v_val_620_, 0);
lean_inc(v_fst_621_);
v_snd_622_ = lean_ctor_get(v_val_620_, 1);
lean_inc(v_snd_622_);
lean_dec(v_val_620_);
v___f_623_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_623_, 0, v_toApplicative_608_);
lean_closure_set(v___f_623_, 1, v_fst_621_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_snd_622_);
v___x_625_ = v___x_617_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_snd_622_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_consumers_614_);
lean_ctor_set_uint8(v_reuseFailAlloc_629_, sizeof(void*)*2, v_closed_615_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_626_, 0, lean_box(0));
lean_closure_set(v___x_626_, 1, lean_box(0));
lean_closure_set(v___x_626_, 2, v_a_609_);
lean_closure_set(v___x_626_, 3, v___x_625_);
v___x_627_ = lean_apply_2(v_inst_610_, lean_box(0), v___x_626_);
v___x_628_ = lean_apply_4(v_toBind_611_, lean_box(0), lean_box(0), v___x_627_, v___f_623_);
return v___x_628_;
}
}
else
{
lean_object* v_toPure_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v___x_619_);
lean_del_object(v___x_617_);
lean_dec_ref(v_consumers_614_);
lean_dec(v_toBind_611_);
lean_dec(v_inst_610_);
lean_dec(v_a_609_);
v_toPure_630_ = lean_ctor_get(v_toApplicative_608_, 1);
lean_inc(v_toPure_630_);
lean_dec_ref(v_toApplicative_608_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_apply_2(v_toPure_630_, lean_box(0), v___x_631_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_toApplicative_637_; lean_object* v_toBind_638_; lean_object* v___f_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_toApplicative_637_ = lean_ctor_get(v_inst_634_, 0);
lean_inc_ref(v_toApplicative_637_);
v_toBind_638_ = lean_ctor_get(v_inst_634_, 1);
lean_inc(v_toBind_638_);
lean_dec_ref(v_inst_634_);
lean_inc(v_toBind_638_);
lean_inc(v_inst_635_);
lean_inc(v_a_636_);
v___f_639_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_639_, 0, v_toApplicative_637_);
lean_closure_set(v___f_639_, 1, v_a_636_);
lean_closure_set(v___f_639_, 2, v_inst_635_);
lean_closure_set(v___f_639_, 3, v_toBind_638_);
v___x_640_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_640_, 0, lean_box(0));
lean_closure_set(v___x_640_, 1, lean_box(0));
lean_closure_set(v___x_640_, 2, v_a_636_);
v___x_641_ = lean_apply_2(v_inst_635_, lean_box(0), v___x_640_);
v___x_642_ = lean_apply_4(v_toBind_638_, lean_box(0), lean_box(0), v___x_641_, v___f_639_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object* v_m_643_, lean_object* v_00_u03b1_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_645_, v_inst_646_, v_a_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(lean_object* v_a_649_){
_start:
{
lean_object* v___x_651_; lean_object* v_values_652_; lean_object* v_consumers_653_; uint8_t v_closed_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_674_; 
v___x_651_ = lean_st_ref_get(v_a_649_);
v_values_652_ = lean_ctor_get(v___x_651_, 0);
v_consumers_653_ = lean_ctor_get(v___x_651_, 1);
v_closed_654_ = lean_ctor_get_uint8(v___x_651_, sizeof(void*)*2);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_674_ == 0)
{
v___x_656_ = v___x_651_;
v_isShared_657_ = v_isSharedCheck_674_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_consumers_653_);
lean_inc(v_values_652_);
lean_dec(v___x_651_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_674_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_Queue_dequeue_x3f___redArg(v_values_652_);
if (lean_obj_tag(v___x_658_) == 1)
{
lean_object* v_val_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_672_; 
v_val_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_672_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_672_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_val_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_672_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_666_; 
v_fst_663_ = lean_ctor_get(v_val_659_, 0);
lean_inc(v_fst_663_);
v_snd_664_ = lean_ctor_get(v_val_659_, 1);
lean_inc(v_snd_664_);
lean_dec(v_val_659_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v_snd_664_);
v___x_666_ = v___x_656_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_snd_664_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_consumers_653_);
lean_ctor_set_uint8(v_reuseFailAlloc_671_, sizeof(void*)*2, v_closed_654_);
v___x_666_ = v_reuseFailAlloc_671_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_st_ref_set(v_a_649_, v___x_666_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v_fst_663_);
v___x_669_ = v___x_661_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_fst_663_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v___x_673_; 
lean_dec(v___x_658_);
lean_del_object(v___x_656_);
lean_dec_ref(v_consumers_653_);
v___x_673_ = lean_box(0);
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_675_);
lean_dec(v_a_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_object* v_00_u03b1_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_682_, lean_object* v_a_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(v_00_u03b1_682_, v_a_683_);
lean_dec(v_a_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(lean_object* v_ch_687_){
_start:
{
lean_object* v___f_689_; lean_object* v___x_690_; 
v___f_689_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0));
v___x_690_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_687_, v___f_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(lean_object* v_ch_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_object* v_00_u03b1_694_, lean_object* v_ch_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(lean_object* v_00_u03b1_698_, lean_object* v_ch_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(v_00_u03b1_698_, v_ch_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(lean_object* v_x_702_){
_start:
{
if (lean_obj_tag(v_x_702_) == 0)
{
lean_object* v___x_703_; 
v___x_703_ = lean_box(0);
return v___x_703_;
}
else
{
lean_object* v_val_704_; 
v_val_704_ = lean_ctor_get(v_x_702_, 0);
lean_inc(v_val_704_);
return v_val_704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(lean_object* v_x_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(v_x_705_);
lean_dec(v_x_705_);
return v_res_706_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_box(0);
v___x_708_ = lean_task_pure(v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(lean_object* v___f_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v___y_710_);
if (lean_obj_tag(v___x_712_) == 1)
{
lean_object* v___x_713_; 
lean_dec_ref(v___f_709_);
v___x_713_ = lean_task_pure(v___x_712_);
return v___x_713_;
}
else
{
lean_object* v___x_714_; uint8_t v_closed_715_; 
lean_dec(v___x_712_);
v___x_714_ = lean_st_ref_get(v___y_710_);
v_closed_715_ = lean_ctor_get_uint8(v___x_714_, sizeof(void*)*2);
lean_dec(v___x_714_);
if (v_closed_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_values_718_; lean_object* v_consumers_719_; uint8_t v_closed_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_734_; 
v___x_716_ = lean_io_promise_new();
v___x_717_ = lean_st_ref_take(v___y_710_);
v_values_718_ = lean_ctor_get(v___x_717_, 0);
v_consumers_719_ = lean_ctor_get(v___x_717_, 1);
v_closed_720_ = lean_ctor_get_uint8(v___x_717_, sizeof(void*)*2);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_734_ == 0)
{
v___x_722_ = v___x_717_;
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_consumers_719_);
lean_inc(v_values_718_);
lean_dec(v___x_717_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
lean_inc(v___x_716_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_716_);
v___x_725_ = l_Std_Queue_enqueue___redArg(v___x_724_, v_consumers_719_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___x_725_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_values_718_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_725_);
lean_ctor_set_uint8(v_reuseFailAlloc_733_, sizeof(void*)*2, v_closed_720_);
v___x_727_ = v_reuseFailAlloc_733_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_728_ = lean_st_ref_set(v___y_710_, v___x_727_);
v___x_729_ = 1;
v___x_730_ = lean_io_promise_result_opt(v___x_716_);
lean_dec(v___x_716_);
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = lean_task_map(v___f_709_, v___x_730_, v___x_731_, v___x_729_);
return v___x_732_;
}
}
}
else
{
lean_object* v___x_735_; 
lean_dec_ref(v___f_709_);
v___x_735_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(lean_object* v___f_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(v___f_736_, v___y_737_);
lean_dec(v___y_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(lean_object* v_ch_743_){
_start:
{
lean_object* v___f_745_; lean_object* v___x_746_; 
v___f_745_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1));
v___x_746_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_743_, v___f_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(lean_object* v_ch_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_747_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_object* v_00_u03b1_750_, lean_object* v_ch_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(lean_object* v_00_u03b1_754_, lean_object* v_ch_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(v_00_u03b1_754_, v_ch_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_758_, lean_object* v_a_759_){
_start:
{
uint8_t v___y_761_; lean_object* v_values_765_; uint8_t v_closed_766_; uint8_t v___x_767_; 
v_values_765_ = lean_ctor_get(v_a_759_, 0);
v_closed_766_ = lean_ctor_get_uint8(v_a_759_, sizeof(void*)*2);
v___x_767_ = l_Std_Queue_isEmpty___redArg(v_values_765_);
if (v___x_767_ == 0)
{
uint8_t v___x_768_; 
v___x_768_ = 1;
v___y_761_ = v___x_768_;
goto v___jp_760_;
}
else
{
v___y_761_ = v_closed_766_;
goto v___jp_760_;
}
v___jp_760_:
{
lean_object* v_toPure_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_toPure_762_ = lean_ctor_get(v_toApplicative_758_, 1);
lean_inc(v_toPure_762_);
lean_dec_ref(v_toApplicative_758_);
v___x_763_ = lean_box(v___y_761_);
v___x_764_ = lean_apply_2(v_toPure_762_, lean_box(0), v___x_763_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(v_toApplicative_769_, v_a_770_);
lean_dec_ref(v_a_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_toApplicative_775_; lean_object* v_toBind_776_; lean_object* v___f_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_toApplicative_775_ = lean_ctor_get(v_inst_772_, 0);
lean_inc_ref(v_toApplicative_775_);
v_toBind_776_ = lean_ctor_get(v_inst_772_, 1);
lean_inc(v_toBind_776_);
lean_dec_ref(v_inst_772_);
v___f_777_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_777_, 0, v_toApplicative_775_);
v___x_778_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_778_, 0, lean_box(0));
lean_closure_set(v___x_778_, 1, lean_box(0));
lean_closure_set(v___x_778_, 2, v_a_774_);
v___x_779_ = lean_apply_2(v_inst_773_, lean_box(0), v___x_778_);
v___x_780_ = lean_apply_4(v_toBind_776_, lean_box(0), lean_box(0), v___x_779_, v___f_777_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object* v_m_781_, lean_object* v_00_u03b1_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_a_785_){
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
v___x_789_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_789_, 0, lean_box(0));
lean_closure_set(v___x_789_, 1, lean_box(0));
lean_closure_set(v___x_789_, 2, v_a_785_);
v___x_790_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_789_);
v___x_791_ = lean_apply_4(v_toBind_787_, lean_box(0), lean_box(0), v___x_790_, v___f_788_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_fst_792_, lean_object* v_x_793_){
_start:
{
if (lean_obj_tag(v_x_793_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
lean_dec(v_fst_792_);
v_a_795_ = lean_ctor_get(v_x_793_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_803_ == 0)
{
v___x_797_ = v_x_793_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v_x_793_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
else
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_812_; 
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_x_793_, 0);
lean_dec(v_unused_813_);
v___x_805_ = v_x_793_;
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_x_793_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_812_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v_fst_792_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_811_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; 
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_814_, lean_object* v_x_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_814_, v_x_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_833_; 
v_a_825_ = lean_ctor_get(v_x_823_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_823_);
if (v_isSharedCheck_833_ == 0)
{
v___x_827_ = v_x_823_;
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v_x_823_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_825_);
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
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_868_; 
v_a_834_ = lean_ctor_get(v_x_823_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x_823_);
if (v_isSharedCheck_868_ == 0)
{
v___x_836_ = v_x_823_;
v_isShared_837_ = v_isSharedCheck_868_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v_x_823_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_868_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_values_838_; lean_object* v_consumers_839_; uint8_t v_closed_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_867_; 
v_values_838_ = lean_ctor_get(v_a_834_, 0);
v_consumers_839_ = lean_ctor_get(v_a_834_, 1);
v_closed_840_ = lean_ctor_get_uint8(v_a_834_, sizeof(void*)*2);
v_isSharedCheck_867_ = !lean_is_exclusive(v_a_834_);
if (v_isSharedCheck_867_ == 0)
{
v___x_842_ = v_a_834_;
v_isShared_843_ = v_isSharedCheck_867_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_consumers_839_);
lean_inc(v_values_838_);
lean_dec(v_a_834_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_867_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_Queue_dequeue_x3f___redArg(v_values_838_);
if (lean_obj_tag(v___x_844_) == 1)
{
lean_object* v_val_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_865_; 
v_val_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_865_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_865_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_val_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_865_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_852_; 
v_fst_849_ = lean_ctor_get(v_val_845_, 0);
lean_inc(v_fst_849_);
v_snd_850_ = lean_ctor_get(v_val_845_, 1);
lean_inc(v_snd_850_);
lean_dec(v_val_845_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v_snd_850_);
v___x_852_ = v___x_842_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_snd_850_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_consumers_839_);
lean_ctor_set_uint8(v_reuseFailAlloc_864_, sizeof(void*)*2, v_closed_840_);
v___x_852_ = v_reuseFailAlloc_864_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___f_854_; lean_object* v___x_856_; 
v___x_853_ = lean_st_ref_set(v_a_822_, v___x_852_);
v___f_854_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_854_, 0, v_fst_849_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_853_);
v___x_856_ = v___x_836_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_853_);
v___x_856_ = v_reuseFailAlloc_863_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_858_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 0);
lean_ctor_set(v___x_847_, 0, v___x_856_);
v___x_858_ = v___x_847_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = 0;
v___x_861_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_859_, v___x_860_, v___x_858_, v___f_854_);
return v___x_861_;
}
}
}
}
}
else
{
lean_object* v___x_866_; 
lean_dec(v___x_844_);
lean_del_object(v___x_842_);
lean_dec_ref(v_consumers_839_);
lean_del_object(v___x_836_);
v___x_866_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_869_, lean_object* v_x_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_869_, v_x_870_);
lean_dec(v_a_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object* v_a_873_){
_start:
{
lean_object* v___x_875_; lean_object* v___f_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; 
v___x_875_ = lean_st_ref_get(v_a_873_);
v___f_876_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_876_, 0, v_a_873_);
v___x_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = 0;
v___x_881_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_879_, v___x_880_, v___x_878_, v___f_876_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object* v_00_u03b1_885_, lean_object* v_a_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_889_, lean_object* v_a_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_889_, v_a_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_promise_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_894_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_904_; 
v_a_896_ = lean_ctor_get(v_x_894_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_894_);
if (v_isSharedCheck_904_ == 0)
{
v___x_898_ = v_x_894_;
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v_x_894_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_904_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_903_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; 
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_io_promise_resolve(v_x_894_, v_promise_893_);
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_promise_908_, lean_object* v_x_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_908_, v_x_909_);
lean_dec(v_promise_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_912_, lean_object* v___y_913_, lean_object* v___f_914_, lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v___f_914_);
lean_dec(v___y_913_);
lean_dec_ref(v_lose_912_);
v_a_917_ = lean_ctor_get(v_x_915_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_925_ == 0)
{
v___x_919_ = v_x_915_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v_x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_924_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
}
else
{
lean_object* v_a_926_; uint8_t v___x_927_; 
v_a_926_ = lean_ctor_get(v_x_915_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v_x_915_);
v___x_927_ = lean_unbox(v_a_926_);
lean_dec(v_a_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec_ref(v___f_914_);
v___x_928_ = lean_apply_2(v_lose_912_, v___y_913_, lean_box(0));
return v___x_928_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___x_932_; 
lean_dec_ref(v_lose_912_);
v___x_929_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_913_);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = 0;
v___x_932_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_930_, v___x_931_, v___x_929_, v___f_914_);
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_933_, lean_object* v___y_934_, lean_object* v___f_935_, lean_object* v_x_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_933_, v___y_934_, v___f_935_, v_x_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object* v_w_939_, lean_object* v_lose_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_finished_943_; lean_object* v_promise_944_; lean_object* v___x_945_; lean_object* v___f_946_; lean_object* v___f_947_; uint8_t v___y_949_; uint8_t v___x_959_; 
v_finished_943_ = lean_ctor_get(v_w_939_, 0);
lean_inc(v_finished_943_);
v_promise_944_ = lean_ctor_get(v_w_939_, 1);
lean_inc(v_promise_944_);
lean_dec_ref(v_w_939_);
v___x_945_ = lean_st_ref_take(v_finished_943_);
v___f_946_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_946_, 0, v_promise_944_);
v___f_947_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_947_, 0, v_lose_940_);
lean_closure_set(v___f_947_, 1, v___y_941_);
lean_closure_set(v___f_947_, 2, v___f_946_);
v___x_959_ = lean_unbox(v___x_945_);
lean_dec(v___x_945_);
if (v___x_959_ == 0)
{
uint8_t v___x_960_; 
v___x_960_ = 1;
v___y_949_ = v___x_960_;
goto v___jp_948_;
}
else
{
uint8_t v___x_961_; 
v___x_961_ = 0;
v___y_949_ = v___x_961_;
goto v___jp_948_;
}
v___jp_948_:
{
uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; 
v___x_950_ = 1;
v___x_951_ = lean_box(v___x_950_);
v___x_952_ = lean_st_ref_set(v_finished_943_, v___x_951_);
lean_dec(v_finished_943_);
v___x_953_ = lean_box(v___y_949_);
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = 0;
v___x_958_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_956_, v___x_957_, v___x_955_, v___f_947_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object* v_w_962_, lean_object* v_lose_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_962_, v_lose_963_, v___y_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object* v_00_u03b1_967_, lean_object* v_w_968_, lean_object* v_lose_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_968_, v_lose_969_, v___y_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_973_, lean_object* v_w_974_, lean_object* v_lose_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_973_, v_w_974_, v_lose_975_, v___y_976_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_979_, lean_object* v_x_980_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_io_basemutex_unlock(v_mutex_979_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_985_, lean_object* v_x_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(v_mutex_985_, v_x_986_);
lean_dec(v_x_986_);
lean_dec(v_mutex_985_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_989_, lean_object* v_ref_990_, lean_object* v_x_991_){
_start:
{
if (lean_obj_tag(v_x_991_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_ref_990_);
lean_dec_ref(v_k_989_);
v_a_993_ = lean_ctor_get(v_x_991_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_x_991_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_995_ = v_x_991_;
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v_x_991_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_1000_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; 
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
}
else
{
lean_object* v___x_1002_; 
lean_dec_ref(v_x_991_);
v___x_1002_ = lean_apply_2(v_k_989_, v_ref_990_, lean_box(0));
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_1003_, lean_object* v_ref_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_k_1003_, v_ref_1004_, v_x_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_1008_, lean_object* v___f_1009_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; 
v___x_1011_ = lean_io_basemutex_lock(v_mutex_1008_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = 0;
v___x_1016_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1014_, v___x_1015_, v___x_1013_, v___f_1009_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_1017_, lean_object* v___f_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_mutex_1017_, v___f_1018_);
lean_dec(v_mutex_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_1021_){
_start:
{
if (lean_obj_tag(v___y_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___y_1021_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___y_1021_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___y_1021_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___y_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
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
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_a_1030_ = lean_ctor_get(v___y_1021_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___y_1021_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v___y_1021_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___y_1021_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_fst_1034_; lean_object* v___x_1036_; 
v_fst_1034_ = lean_ctor_get(v_a_1030_, 0);
lean_inc(v_fst_1034_);
lean_dec(v_a_1030_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v_fst_1034_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_fst_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object* v_mutex_1040_, lean_object* v_k_1041_){
_start:
{
lean_object* v_ref_1043_; lean_object* v_mutex_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___y_1052_; 
v_ref_1043_ = lean_ctor_get(v_mutex_1040_, 0);
lean_inc(v_ref_1043_);
v_mutex_1044_ = lean_ctor_get(v_mutex_1040_, 1);
lean_inc(v_mutex_1044_);
lean_dec_ref(v_mutex_1040_);
lean_inc(v_mutex_1044_);
v___f_1045_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1045_, 0, v_mutex_1044_);
v___f_1046_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1046_, 0, v_k_1041_);
lean_closure_set(v___f_1046_, 1, v_ref_1043_);
v___f_1047_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1047_, 0, v_mutex_1044_);
lean_closure_set(v___f_1047_, 1, v___f_1046_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = 0;
v___x_1050_ = l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(v___f_1047_, v___f_1045_, v___x_1048_, v___x_1049_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1054_; 
v_a_1054_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1054_);
lean_dec_ref(v___x_1050_);
if (lean_obj_tag(v_a_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v_a_1054_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_a_1054_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v_a_1054_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v_a_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
v___y_1052_ = v___x_1060_;
goto v___jp_1051_;
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_a_1063_ = lean_ctor_get(v_a_1054_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_a_1054_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1065_ = v_a_1054_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v_a_1054_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_fst_1067_; lean_object* v___x_1069_; 
v_fst_1067_ = lean_ctor_get(v_a_1063_, 0);
lean_inc(v_fst_1067_);
lean_dec(v_a_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_fst_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_fst_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
v___y_1052_ = v___x_1069_;
goto v___jp_1051_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1081_; 
v_a_1072_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1074_ = v___x_1050_;
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1050_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___f_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___f_1076_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0));
v___x_1077_ = lean_task_map(v___f_1076_, v_a_1072_, v___x_1048_, v___x_1049_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1077_);
v___x_1079_ = v___x_1074_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
v___jp_1051_:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___y_1052_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_1082_, lean_object* v_k_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1082_, v_k_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_mutex_1088_, lean_object* v_k_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1088_, v_k_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_mutex_1094_, lean_object* v_k_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_1092_, v_00_u03b2_1093_, v_mutex_1094_, v_k_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object* v_x_1098_){
_start:
{
if (lean_obj_tag(v_x_1098_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1108_; 
v_a_1100_ = lean_ctor_get(v_x_1098_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_x_1098_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1102_ = v_x_1098_;
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v_x_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1118_; 
v_a_1109_ = lean_ctor_get(v_x_1098_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_x_1098_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1111_ = v_x_1098_;
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v_x_1098_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_a_1109_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object* v_x_1122_){
_start:
{
uint8_t v___y_1125_; 
if (lean_obj_tag(v_x_1122_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_a_1129_ = lean_ctor_get(v_x_1122_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_x_1122_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v_x_1122_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v_x_1122_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v_values_1139_; uint8_t v_closed_1140_; uint8_t v___x_1141_; 
v_a_1138_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_a_1138_);
lean_dec_ref(v_x_1122_);
v_values_1139_ = lean_ctor_get(v_a_1138_, 0);
lean_inc_ref(v_values_1139_);
v_closed_1140_ = lean_ctor_get_uint8(v_a_1138_, sizeof(void*)*2);
lean_dec(v_a_1138_);
v___x_1141_ = l_Std_Queue_isEmpty___redArg(v_values_1139_);
lean_dec_ref(v_values_1139_);
if (v___x_1141_ == 0)
{
uint8_t v___x_1142_; 
v___x_1142_ = 1;
v___y_1125_ = v___x_1142_;
goto v___jp_1124_;
}
else
{
v___y_1125_ = v_closed_1140_;
goto v___jp_1124_;
}
}
v___jp_1124_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_box(v___y_1125_);
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object* v_x_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object* v___x_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1146_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1151_, v___y_1152_);
lean_dec(v___y_1152_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object* v___y_1161_, lean_object* v_waiter_1162_, lean_object* v_x_1163_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_waiter_1162_);
lean_dec(v___y_1161_);
v_a_1165_ = lean_ctor_get(v_x_1163_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_x_1163_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1167_ = v_x_1163_;
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v_x_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1174_; uint8_t v___x_1175_; 
v_a_1174_ = lean_ctor_get(v_x_1163_, 0);
lean_inc(v_a_1174_);
lean_dec_ref(v_x_1163_);
v___x_1175_ = lean_unbox(v_a_1174_);
lean_dec(v_a_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v_values_1177_; lean_object* v_consumers_1178_; uint8_t v_closed_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1190_; 
v___x_1176_ = lean_st_ref_take(v___y_1161_);
v_values_1177_ = lean_ctor_get(v___x_1176_, 0);
v_consumers_1178_ = lean_ctor_get(v___x_1176_, 1);
v_closed_1179_ = lean_ctor_get_uint8(v___x_1176_, sizeof(void*)*2);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1181_ = v___x_1176_;
v_isShared_1182_ = v_isSharedCheck_1190_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_consumers_1178_);
lean_inc(v_values_1177_);
lean_dec(v___x_1176_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1190_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_waiter_1162_);
v___x_1184_ = l_Std_Queue_enqueue___redArg(v___x_1183_, v_consumers_1178_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1184_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_values_1177_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, sizeof(void*)*2, v_closed_1179_);
v___x_1186_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_st_ref_set(v___y_1161_, v___x_1186_);
lean_dec(v___y_1161_);
v___x_1188_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_1188_;
}
}
}
else
{
lean_object* v_lose_1191_; lean_object* v___x_1192_; 
v_lose_1191_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_1192_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_1162_, v_lose_1191_, v___y_1161_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object* v___y_1193_, lean_object* v_waiter_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1193_, v_waiter_1194_, v_x_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object* v___f_1198_, lean_object* v_waiter_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; 
v___x_1202_ = lean_st_ref_get(v___y_1200_);
v___x_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
v___x_1205_ = lean_unsigned_to_nat(0u);
v___x_1206_ = 0;
v___x_1207_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1205_, v___x_1206_, v___x_1204_, v___f_1198_);
v___f_1208_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1208_, 0, v___y_1200_);
lean_closure_set(v___f_1208_, 1, v_waiter_1199_);
v___x_1209_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1205_, v___x_1206_, v___x_1207_, v___f_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object* v___f_1210_, lean_object* v_waiter_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v___f_1210_, v_waiter_1211_, v___y_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object* v___f_1215_, lean_object* v_ch_1216_, lean_object* v_waiter_1217_){
_start:
{
lean_object* v___f_1219_; lean_object* v___x_1220_; 
v___f_1219_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1219_, 0, v___f_1215_);
lean_closure_set(v___f_1219_, 1, v_waiter_1217_);
v___x_1220_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_1216_, v___f_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object* v___f_1221_, lean_object* v_ch_1222_, lean_object* v_waiter_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1221_, v_ch_1222_, v_waiter_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object* v___y_1230_, lean_object* v___f_1231_, lean_object* v_x_1232_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___f_1231_);
lean_dec(v___y_1230_);
v_a_1234_ = lean_ctor_get(v_x_1232_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_x_1232_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1236_ = v_x_1232_;
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v_x_1232_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1242_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
else
{
lean_object* v_a_1243_; uint8_t v___x_1244_; 
v_a_1243_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v_x_1232_);
v___x_1244_ = lean_unbox(v_a_1243_);
lean_dec(v_a_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_dec_ref(v___f_1231_);
lean_dec(v___y_1230_);
v___x_1245_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1246_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_1230_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = 0;
v___x_1249_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1247_, v___x_1248_, v___x_1246_, v___f_1231_);
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object* v___y_1250_, lean_object* v___f_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1250_, v___f_1251_, v_x_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object* v___f_1255_, lean_object* v___f_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; 
v___x_1259_ = lean_st_ref_get(v___y_1257_);
v___x_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = 0;
v___x_1264_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1262_, v___x_1263_, v___x_1261_, v___f_1255_);
v___f_1265_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1265_, 0, v___y_1257_);
lean_closure_set(v___f_1265_, 1, v___f_1256_);
v___x_1266_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1262_, v___x_1263_, v___x_1264_, v___f_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object* v___f_1267_, lean_object* v___f_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1267_, v___f_1268_, v___y_1269_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object* v_values_1272_, uint8_t v_closed_1273_, lean_object* v___y_1274_, lean_object* v_x_1275_){
_start:
{
if (lean_obj_tag(v_x_1275_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_values_1272_);
v_a_1277_ = lean_ctor_get(v_x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1279_ = v_x_1275_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v_x_1275_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
return v___x_1283_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1296_; 
v_a_1286_ = lean_ctor_get(v_x_1275_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_x_1275_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1288_ = v_x_1275_;
v_isShared_1289_ = v_isSharedCheck_1296_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v_x_1275_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1296_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1290_, 0, v_values_1272_);
lean_ctor_set(v___x_1290_, 1, v_a_1286_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*2, v_closed_1273_);
v___x_1291_ = lean_st_ref_set(v___y_1274_, v___x_1290_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1291_);
v___x_1293_ = v___x_1288_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
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
lean_dec_ref(v_x_1355_);
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
lean_object* v_head_1387_; lean_object* v_tail_1388_; lean_object* v___f_1389_; lean_object* v_val_1391_; 
v_head_1387_ = lean_ctor_get(v_x_1382_, 0);
lean_inc(v_head_1387_);
v_tail_1388_ = lean_ctor_get(v_x_1382_, 1);
lean_inc(v_tail_1388_);
lean_dec_ref(v_x_1382_);
lean_inc(v_head_1387_);
v___f_1389_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1389_, 0, v_tail_1388_);
lean_closure_set(v___f_1389_, 1, v_x_1383_);
lean_closure_set(v___f_1389_, 2, v_head_1387_);
if (lean_obj_tag(v_head_1387_) == 0)
{
lean_object* v___x_1395_; 
lean_dec_ref(v_head_1387_);
v___x_1395_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_1391_ = v___x_1395_;
goto v___jp_1390_;
}
else
{
lean_object* v_finished_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1410_; 
v_finished_1396_ = lean_ctor_get(v_head_1387_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_head_1387_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1398_ = v_head_1387_;
v_isShared_1399_ = v_isSharedCheck_1410_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_finished_1396_);
lean_dec(v_head_1387_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1410_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_finished_1400_; lean_object* v___x_1401_; lean_object* v___f_1402_; lean_object* v___x_1404_; 
v_finished_1400_ = lean_ctor_get(v_finished_1396_, 0);
lean_inc(v_finished_1400_);
lean_dec_ref(v_finished_1396_);
v___x_1401_ = lean_st_ref_get(v_finished_1400_);
lean_dec(v_finished_1400_);
v___f_1402_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1401_);
v___x_1404_ = v___x_1398_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1401_);
v___x_1404_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = 0;
v___x_1408_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1406_, v___x_1407_, v___x_1405_, v___f_1402_);
v_val_1391_ = v___x_1408_;
goto v___jp_1390_;
}
}
}
v___jp_1390_:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = 0;
v___x_1394_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1392_, v___x_1393_, v_val_1391_, v___f_1389_);
return v___x_1394_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1411_, lean_object* v_x_1412_, lean_object* v_head_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_head_1413_);
lean_dec(v_x_1412_);
lean_dec(v_tail_1411_);
v_a_1416_ = lean_ctor_get(v_x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v_x_1414_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v_x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; uint8_t v___x_1426_; 
v_a_1425_ = lean_ctor_get(v_x_1414_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v_x_1414_);
v___x_1426_ = lean_unbox(v_a_1425_);
lean_dec(v_a_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
lean_dec_ref(v_head_1413_);
v___x_1427_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1411_, v_x_1412_);
return v___x_1427_;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_head_1413_);
lean_ctor_set(v___x_1428_, 1, v_x_1412_);
v___x_1429_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1411_, v___x_1428_);
return v___x_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1430_, v_x_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_1434_, lean_object* v___x_1435_, lean_object* v___f_1436_, lean_object* v_x_1437_){
_start:
{
if (lean_obj_tag(v_x_1437_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v___f_1436_);
lean_dec(v___x_1435_);
lean_dec(v_eList_1434_);
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
lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___f_1453_; lean_object* v___x_1454_; 
v_a_1448_ = lean_ctor_get(v_x_1437_, 0);
lean_inc(v_a_1448_);
lean_dec_ref(v_x_1437_);
lean_inc(v___x_1435_);
v___x_1449_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1434_, v___x_1435_);
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = 0;
v___x_1452_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1450_, v___x_1451_, v___x_1449_, v___f_1436_);
v___f_1453_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1453_, 0, v_a_1448_);
lean_closure_set(v___f_1453_, 1, v___x_1435_);
v___x_1454_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1450_, v___x_1451_, v___x_1452_, v___f_1453_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_1455_, lean_object* v___x_1456_, lean_object* v___f_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v_eList_1455_, v___x_1456_, v___f_1457_, v_x_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_eList_1465_; lean_object* v_dList_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; lean_object* v___f_1473_; lean_object* v___x_1474_; 
v_eList_1465_ = lean_ctor_get(v_q_1462_, 0);
lean_inc(v_eList_1465_);
v_dList_1466_ = lean_ctor_get(v_q_1462_, 1);
lean_inc(v_dList_1466_);
lean_dec_ref(v_q_1462_);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1466_, v___x_1467_);
v___f_1469_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = 0;
v___x_1472_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1470_, v___x_1471_, v___x_1468_, v___f_1469_);
v___f_1473_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1473_, 0, v_eList_1465_);
lean_closure_set(v___f_1473_, 1, v___x_1467_);
lean_closure_set(v___f_1473_, 2, v___f_1469_);
v___x_1474_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1470_, v___x_1471_, v___x_1472_, v___f_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1475_, v___y_1476_);
lean_dec(v___y_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1479_, lean_object* v_x_1480_){
_start:
{
if (lean_obj_tag(v_x_1480_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v___y_1479_);
v_a_1482_ = lean_ctor_get(v_x_1480_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_x_1480_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1484_ = v_x_1480_;
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v_x_1480_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v_values_1492_; lean_object* v_consumers_1493_; uint8_t v_closed_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; 
v_a_1491_ = lean_ctor_get(v_x_1480_, 0);
lean_inc(v_a_1491_);
lean_dec_ref(v_x_1480_);
v_values_1492_ = lean_ctor_get(v_a_1491_, 0);
lean_inc_ref(v_values_1492_);
v_consumers_1493_ = lean_ctor_get(v_a_1491_, 1);
lean_inc_ref(v_consumers_1493_);
v_closed_1494_ = lean_ctor_get_uint8(v_a_1491_, sizeof(void*)*2);
lean_dec(v_a_1491_);
v___x_1495_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1493_, v___y_1479_);
v___x_1496_ = lean_box(v_closed_1494_);
v___f_1497_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1497_, 0, v_values_1492_);
lean_closure_set(v___f_1497_, 1, v___x_1496_);
lean_closure_set(v___f_1497_, 2, v___y_1479_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = 0;
v___x_1500_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1498_, v___x_1499_, v___x_1495_, v___f_1497_);
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1501_, lean_object* v_x_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1501_, v_x_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v___f_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1507_ = lean_st_ref_get(v___y_1505_);
v___f_1508_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1508_, 0, v___y_1505_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
v___x_1511_ = lean_unsigned_to_nat(0u);
v___x_1512_ = 0;
v___x_1513_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1511_, v___x_1512_, v___x_1510_, v___f_1508_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1523_){
_start:
{
lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___f_1524_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref(v_ch_1523_);
v___f_1525_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1525_, 0, v___f_1524_);
lean_closure_set(v___f_1525_, 1, v_ch_1523_);
v___f_1526_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1527_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
lean_inc_ref(v_ch_1523_);
v___x_1528_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1528_, 0, lean_box(0));
lean_closure_set(v___x_1528_, 1, lean_box(0));
lean_closure_set(v___x_1528_, 2, v_ch_1523_);
lean_closure_set(v___x_1528_, 3, v___f_1526_);
v___x_1529_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1529_, 0, lean_box(0));
lean_closure_set(v___x_1529_, 1, lean_box(0));
lean_closure_set(v___x_1529_, 2, v_ch_1523_);
lean_closure_set(v___x_1529_, 3, v___f_1527_);
v___x_1530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___f_1525_);
lean_ctor_set(v___x_1530_, 2, v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1531_, lean_object* v_ch_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1534_, lean_object* v_q_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1535_, v___y_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1539_, lean_object* v_q_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1539_, v_q_1540_, v___y_1541_);
lean_dec(v___y_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1545_, v_x_1546_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1550_, lean_object* v_x_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1550_, v_x_1551_, v_x_1552_, v___y_1553_);
lean_dec(v___y_1553_);
return v_res_1555_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Std_Queue_empty(lean_box(0));
return v___x_1556_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = 0;
v___x_1558_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1559_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*2, v___x_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1);
v___x_1562_ = l_Std_Mutex_new___redArg(v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1568_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v_producers_1584_; lean_object* v_consumers_1585_; uint8_t v_closed_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1609_; 
v___x_1583_ = lean_st_ref_get(v___y_1581_);
v_producers_1584_ = lean_ctor_get(v___x_1583_, 0);
v_consumers_1585_ = lean_ctor_get(v___x_1583_, 1);
v_closed_1586_ = lean_ctor_get_uint8(v___x_1583_, sizeof(void*)*2);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1588_ = v___x_1583_;
v_isShared_1589_ = v_isSharedCheck_1609_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_consumers_1585_);
lean_inc(v_producers_1584_);
lean_dec(v___x_1583_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1609_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1585_);
if (lean_obj_tag(v___x_1590_) == 1)
{
lean_object* v_val_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1607_; 
v_val_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1607_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_val_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1607_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_fst_1595_; lean_object* v_snd_1596_; lean_object* v___x_1598_; 
v_fst_1595_ = lean_ctor_get(v_val_1591_, 0);
lean_inc(v_fst_1595_);
v_snd_1596_ = lean_ctor_get(v_val_1591_, 1);
lean_inc(v_snd_1596_);
lean_dec(v_val_1591_);
lean_inc(v_v_1580_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v_v_1580_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_v_1580_);
v___x_1598_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
uint8_t v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1595_, v___x_1598_);
lean_dec(v_fst_1595_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v_snd_1596_);
v___x_1601_ = v___x_1588_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_producers_1584_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_snd_1596_);
lean_ctor_set_uint8(v_reuseFailAlloc_1605_, sizeof(void*)*2, v_closed_1586_);
v___x_1601_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_st_ref_set(v___y_1581_, v___x_1601_);
if (v___x_1599_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_1604_; 
lean_dec(v_v_1580_);
v___x_1604_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
return v___x_1604_;
}
}
}
}
}
else
{
lean_object* v___x_1608_; 
lean_dec(v___x_1590_);
lean_del_object(v___x_1588_);
lean_dec_ref(v_producers_1584_);
lean_dec(v_v_1580_);
v___x_1608_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1610_, v___y_1611_);
lean_dec(v___y_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1617_; lean_object* v_fst_1618_; 
v___x_1617_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1614_, v_a_1615_);
v_fst_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_fst_1618_);
lean_dec_ref(v___x_1617_);
if (lean_obj_tag(v_fst_1618_) == 0)
{
uint8_t v___x_1619_; 
v___x_1619_ = 1;
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; uint8_t v___x_1621_; 
v_val_1620_ = lean_ctor_get(v_fst_1618_, 0);
lean_inc(v_val_1620_);
lean_dec_ref(v_fst_1618_);
v___x_1621_ = lean_unbox(v_val_1620_);
lean_dec(v_val_1620_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
uint8_t v_res_1625_; lean_object* v_r_1626_; 
v_res_1625_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1622_, v_a_1623_);
lean_dec(v_a_1623_);
v_r_1626_ = lean_box(v_res_1625_);
return v_r_1626_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1627_, lean_object* v_v_1628_, lean_object* v_a_1629_){
_start:
{
uint8_t v___x_1631_; 
v___x_1631_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1628_, v_a_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1632_, lean_object* v_v_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
uint8_t v_res_1636_; lean_object* v_r_1637_; 
v_res_1636_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1632_, v_v_1633_, v_a_1634_);
lean_dec(v_a_1634_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1638_, lean_object* v_v_1639_, lean_object* v_b_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1639_, v___y_1641_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1644_, lean_object* v_v_1645_, lean_object* v_b_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1644_, v_v_1645_, v_b_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v_b_1646_);
return v_res_1649_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; uint8_t v_closed_1654_; 
v___x_1653_ = lean_st_ref_get(v___y_1651_);
v_closed_1654_ = lean_ctor_get_uint8(v___x_1653_, sizeof(void*)*2);
lean_dec(v___x_1653_);
if (v_closed_1654_ == 0)
{
uint8_t v___x_1655_; 
v___x_1655_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1650_, v___y_1651_);
return v___x_1655_;
}
else
{
uint8_t v___x_1656_; 
lean_dec(v_v_1650_);
v___x_1656_ = 0;
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v_res_1660_; lean_object* v_r_1661_; 
v_res_1660_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1657_, v___y_1658_);
lean_dec(v___y_1658_);
v_r_1661_ = lean_box(v_res_1660_);
return v_r_1661_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1662_, lean_object* v_v_1663_){
_start:
{
lean_object* v___f_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___f_1665_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1665_, 0, v_v_1663_);
v___x_1666_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1662_, v___f_1665_);
v___x_1667_ = lean_unbox(v___x_1666_);
lean_dec(v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1668_, lean_object* v_v_1669_, lean_object* v_a_1670_){
_start:
{
uint8_t v_res_1671_; lean_object* v_r_1672_; 
v_res_1671_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1668_, v_v_1669_);
v_r_1672_ = lean_box(v_res_1671_);
return v_r_1672_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1673_, lean_object* v_ch_1674_, lean_object* v_v_1675_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1674_, v_v_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1678_, lean_object* v_ch_1679_, lean_object* v_v_1680_, lean_object* v_a_1681_){
_start:
{
uint8_t v_res_1682_; lean_object* v_r_1683_; 
v_res_1682_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1678_, v_ch_1679_, v_v_1680_);
v_r_1683_ = lean_box(v_res_1682_);
return v_r_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1684_){
_start:
{
if (lean_obj_tag(v_x_1684_) == 0)
{
goto v___jp_1685_;
}
else
{
lean_object* v_val_1687_; uint8_t v___x_1688_; 
v_val_1687_ = lean_ctor_get(v_x_1684_, 0);
v___x_1688_ = lean_unbox(v_val_1687_);
if (v___x_1688_ == 0)
{
goto v___jp_1685_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1689_;
}
}
v___jp_1685_:
{
lean_object* v___x_1686_; 
v___x_1686_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1690_);
lean_dec(v_x_1690_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1692_, lean_object* v___f_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; uint8_t v_closed_1697_; 
v___x_1696_ = lean_st_ref_get(v___y_1694_);
v_closed_1697_ = lean_ctor_get_uint8(v___x_1696_, sizeof(void*)*2);
lean_dec(v___x_1696_);
if (v_closed_1697_ == 0)
{
uint8_t v___x_1698_; 
lean_inc(v_v_1692_);
v___x_1698_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1692_, v___y_1694_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_producers_1701_; lean_object* v_consumers_1702_; uint8_t v_closed_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1717_; 
v___x_1699_ = lean_io_promise_new();
v___x_1700_ = lean_st_ref_take(v___y_1694_);
v_producers_1701_ = lean_ctor_get(v___x_1700_, 0);
v_consumers_1702_ = lean_ctor_get(v___x_1700_, 1);
v_closed_1703_ = lean_ctor_get_uint8(v___x_1700_, sizeof(void*)*2);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1705_ = v___x_1700_;
v_isShared_1706_ = v_isSharedCheck_1717_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_consumers_1702_);
lean_inc(v_producers_1701_);
lean_dec(v___x_1700_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1717_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
lean_inc(v___x_1699_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v_v_1692_);
lean_ctor_set(v___x_1707_, 1, v___x_1699_);
v___x_1708_ = l_Std_Queue_enqueue___redArg(v___x_1707_, v_producers_1701_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1708_);
v___x_1710_ = v___x_1705_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_consumers_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1716_, sizeof(void*)*2, v_closed_1703_);
v___x_1710_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1711_ = lean_st_ref_set(v___y_1694_, v___x_1710_);
v___x_1712_ = 1;
v___x_1713_ = lean_io_promise_result_opt(v___x_1699_);
lean_dec(v___x_1699_);
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = lean_task_map(v___f_1693_, v___x_1713_, v___x_1714_, v___x_1712_);
return v___x_1715_;
}
}
}
else
{
lean_object* v___x_1718_; 
lean_dec_ref(v___f_1693_);
lean_dec(v_v_1692_);
v___x_1718_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1718_;
}
}
else
{
lean_object* v___x_1719_; 
lean_dec_ref(v___f_1693_);
lean_dec(v_v_1692_);
v___x_1719_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1720_, lean_object* v___f_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1720_, v___f_1721_, v___y_1722_);
lean_dec(v___y_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1726_, lean_object* v_v_1727_){
_start:
{
lean_object* v___f_1729_; lean_object* v___f_1730_; lean_object* v___x_1731_; 
v___f_1729_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1730_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1730_, 0, v_v_1727_);
lean_closure_set(v___f_1730_, 1, v___f_1729_);
v___x_1731_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1726_, v___f_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1732_, lean_object* v_v_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1732_, v_v_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1736_, lean_object* v_ch_1737_, lean_object* v_v_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1737_, v_v_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_ch_1742_, lean_object* v_v_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1741_, v_ch_1742_, v_v_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1746_, size_t v_sz_1747_, size_t v_i_1748_, lean_object* v_b_1749_){
_start:
{
uint8_t v___x_1751_; 
v___x_1751_ = lean_usize_dec_lt(v_i_1748_, v_sz_1747_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_b_1749_);
return v___x_1752_;
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; size_t v___x_1757_; size_t v___x_1758_; 
v_a_1753_ = lean_array_uget_borrowed(v_as_1746_, v_i_1748_);
v___x_1754_ = lean_box(0);
v___x_1755_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1753_, v___x_1754_);
v___x_1756_ = lean_box(0);
v___x_1757_ = ((size_t)1ULL);
v___x_1758_ = lean_usize_add(v_i_1748_, v___x_1757_);
v_i_1748_ = v___x_1758_;
v_b_1749_ = v___x_1756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1760_, lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_){
_start:
{
size_t v_sz_boxed_1765_; size_t v_i_boxed_1766_; lean_object* v_res_1767_; 
v_sz_boxed_1765_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1766_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1760_, v_sz_boxed_1765_, v_i_boxed_1766_, v_b_1763_);
lean_dec_ref(v_as_1760_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; uint8_t v_closed_1771_; 
v___x_1770_ = lean_st_ref_get(v___y_1768_);
v_closed_1771_ = lean_ctor_get_uint8(v___x_1770_, sizeof(void*)*2);
if (v_closed_1771_ == 0)
{
lean_object* v_producers_1772_; lean_object* v_consumers_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1796_; 
v_producers_1772_ = lean_ctor_get(v___x_1770_, 0);
v_consumers_1773_ = lean_ctor_get(v___x_1770_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1775_ = v___x_1770_;
v_isShared_1776_ = v_isSharedCheck_1796_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_consumers_1773_);
lean_inc(v_producers_1772_);
lean_dec(v___x_1770_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1796_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; size_t v_sz_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
v___x_1777_ = l_Std_Queue_toArray___redArg(v_consumers_1773_);
v___x_1778_ = lean_box(0);
v_sz_1779_ = lean_array_size(v___x_1777_);
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1777_, v_sz_1779_, v___x_1780_, v___x_1778_);
lean_dec_ref(v___x_1777_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1794_; 
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v___x_1781_, 0);
lean_dec(v_unused_1795_);
v___x_1783_ = v___x_1781_;
v_isShared_1784_ = v_isSharedCheck_1794_;
goto v_resetjp_1782_;
}
else
{
lean_dec(v___x_1781_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1794_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; uint8_t v___x_1786_; lean_object* v___x_1788_; 
v___x_1785_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
v___x_1786_ = 1;
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 1, v___x_1785_);
v___x_1788_ = v___x_1775_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_producers_1772_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1785_);
v___x_1788_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
lean_ctor_set_uint8(v___x_1788_, sizeof(void*)*2, v___x_1786_);
v___x_1789_ = lean_st_ref_set(v___y_1768_, v___x_1788_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1778_);
v___x_1791_ = v___x_1783_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1778_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_del_object(v___x_1775_);
lean_dec_ref(v_producers_1772_);
return v___x_1781_;
}
}
}
else
{
uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v___x_1770_);
v___x_1797_ = 1;
v___x_1798_ = lean_box(v___x_1797_);
v___x_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1800_);
lean_dec(v___y_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1804_){
_start:
{
lean_object* v___f_1806_; lean_object* v___x_1807_; 
v___f_1806_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1807_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1804_, v___f_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1811_, lean_object* v_ch_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1815_, lean_object* v_ch_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1815_, v_ch_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1819_, lean_object* v_as_1820_, size_t v_sz_1821_, size_t v_i_1822_, lean_object* v_b_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1820_, v_sz_1821_, v_i_1822_, v_b_1823_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1827_, lean_object* v_as_1828_, lean_object* v_sz_1829_, lean_object* v_i_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
size_t v_sz_boxed_1834_; size_t v_i_boxed_1835_; lean_object* v_res_1836_; 
v_sz_boxed_1834_ = lean_unbox_usize(v_sz_1829_);
lean_dec(v_sz_1829_);
v_i_boxed_1835_ = lean_unbox_usize(v_i_1830_);
lean_dec(v_i_1830_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1827_, v_as_1828_, v_sz_boxed_1834_, v_i_boxed_1835_, v_b_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v_as_1828_);
return v_res_1836_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; uint8_t v_closed_1840_; 
v___x_1839_ = lean_st_ref_get(v___y_1837_);
v_closed_1840_ = lean_ctor_get_uint8(v___x_1839_, sizeof(void*)*2);
lean_dec(v___x_1839_);
return v_closed_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v_res_1843_; lean_object* v_r_1844_; 
v_res_1843_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1841_);
lean_dec(v___y_1841_);
v_r_1844_ = lean_box(v_res_1843_);
return v_r_1844_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1846_){
_start:
{
lean_object* v___f_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___f_1848_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1849_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1846_, v___f_1848_);
v___x_1850_ = lean_unbox(v___x_1849_);
lean_dec(v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1851_, lean_object* v_a_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1851_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1855_, lean_object* v_ch_1856_){
_start:
{
uint8_t v___x_1858_; 
v___x_1858_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1859_, lean_object* v_ch_1860_, lean_object* v_a_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1859_, v_ch_1860_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1864_, lean_object* v_inst_1865_, lean_object* v_toBind_1866_, lean_object* v___f_1867_, lean_object* v_a_1868_){
_start:
{
uint8_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1869_ = 1;
v___x_1870_ = lean_box(v___x_1869_);
v___x_1871_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1871_, 0, lean_box(0));
lean_closure_set(v___x_1871_, 1, v___x_1870_);
lean_closure_set(v___x_1871_, 2, v_snd_1864_);
v___x_1872_ = lean_apply_2(v_inst_1865_, lean_box(0), v___x_1871_);
v___x_1873_ = lean_apply_4(v_toBind_1866_, lean_box(0), lean_box(0), v___x_1872_, v___f_1867_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1874_, lean_object* v_inst_1875_, lean_object* v_toBind_1876_, lean_object* v_a_1877_, lean_object* v_inst_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_producers_1880_; lean_object* v_consumers_1881_; uint8_t v_closed_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1903_; 
v_producers_1880_ = lean_ctor_get(v_a_1879_, 0);
v_consumers_1881_ = lean_ctor_get(v_a_1879_, 1);
v_closed_1882_ = lean_ctor_get_uint8(v_a_1879_, sizeof(void*)*2);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_a_1879_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1884_ = v_a_1879_;
v_isShared_1885_ = v_isSharedCheck_1903_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_consumers_1881_);
lean_inc(v_producers_1880_);
lean_dec(v_a_1879_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1903_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1880_);
if (lean_obj_tag(v___x_1886_) == 1)
{
lean_object* v_val_1887_; lean_object* v_fst_1888_; lean_object* v_snd_1889_; lean_object* v_fst_1890_; lean_object* v_snd_1891_; lean_object* v___f_1892_; lean_object* v___f_1893_; lean_object* v___x_1895_; 
v_val_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_val_1887_);
lean_dec_ref(v___x_1886_);
v_fst_1888_ = lean_ctor_get(v_val_1887_, 0);
lean_inc(v_fst_1888_);
v_snd_1889_ = lean_ctor_get(v_val_1887_, 1);
lean_inc(v_snd_1889_);
lean_dec(v_val_1887_);
v_fst_1890_ = lean_ctor_get(v_fst_1888_, 0);
lean_inc(v_fst_1890_);
v_snd_1891_ = lean_ctor_get(v_fst_1888_, 1);
lean_inc(v_snd_1891_);
lean_dec(v_fst_1888_);
v___f_1892_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1892_, 0, v_toApplicative_1874_);
lean_closure_set(v___f_1892_, 1, v_fst_1890_);
lean_inc(v_toBind_1876_);
v___f_1893_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1893_, 0, v_snd_1891_);
lean_closure_set(v___f_1893_, 1, v_inst_1875_);
lean_closure_set(v___f_1893_, 2, v_toBind_1876_);
lean_closure_set(v___f_1893_, 3, v___f_1892_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v_snd_1889_);
v___x_1895_ = v___x_1884_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_snd_1889_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_consumers_1881_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*2, v_closed_1882_);
v___x_1895_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1896_, 0, lean_box(0));
lean_closure_set(v___x_1896_, 1, lean_box(0));
lean_closure_set(v___x_1896_, 2, v_a_1877_);
lean_closure_set(v___x_1896_, 3, v___x_1895_);
v___x_1897_ = lean_apply_2(v_inst_1878_, lean_box(0), v___x_1896_);
v___x_1898_ = lean_apply_4(v_toBind_1876_, lean_box(0), lean_box(0), v___x_1897_, v___f_1893_);
return v___x_1898_;
}
}
else
{
lean_object* v_toPure_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v___x_1886_);
lean_del_object(v___x_1884_);
lean_dec_ref(v_consumers_1881_);
lean_dec(v_inst_1878_);
lean_dec(v_a_1877_);
lean_dec(v_toBind_1876_);
lean_dec(v_inst_1875_);
v_toPure_1900_ = lean_ctor_get(v_toApplicative_1874_, 1);
lean_inc(v_toPure_1900_);
lean_dec_ref(v_toApplicative_1874_);
v___x_1901_ = lean_box(0);
v___x_1902_ = lean_apply_2(v_toPure_1900_, lean_box(0), v___x_1901_);
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_toApplicative_1908_; lean_object* v_toBind_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_toApplicative_1908_ = lean_ctor_get(v_inst_1904_, 0);
lean_inc_ref(v_toApplicative_1908_);
v_toBind_1909_ = lean_ctor_get(v_inst_1904_, 1);
lean_inc(v_toBind_1909_);
lean_dec_ref(v_inst_1904_);
lean_inc(v_inst_1905_);
lean_inc(v_a_1907_);
lean_inc(v_toBind_1909_);
v___f_1910_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0), 6, 5);
lean_closure_set(v___f_1910_, 0, v_toApplicative_1908_);
lean_closure_set(v___f_1910_, 1, v_inst_1906_);
lean_closure_set(v___f_1910_, 2, v_toBind_1909_);
lean_closure_set(v___f_1910_, 3, v_a_1907_);
lean_closure_set(v___f_1910_, 4, v_inst_1905_);
v___x_1911_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1911_, 0, lean_box(0));
lean_closure_set(v___x_1911_, 1, lean_box(0));
lean_closure_set(v___x_1911_, 2, v_a_1907_);
v___x_1912_ = lean_apply_2(v_inst_1905_, lean_box(0), v___x_1911_);
v___x_1913_ = lean_apply_4(v_toBind_1909_, lean_box(0), lean_box(0), v___x_1912_, v___f_1910_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_1914_, lean_object* v_00_u03b1_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1916_, v_inst_1917_, v_inst_1918_, v_a_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v_producers_1924_; lean_object* v_consumers_1925_; uint8_t v_closed_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1951_; 
v___x_1923_ = lean_st_ref_get(v_a_1921_);
v_producers_1924_ = lean_ctor_get(v___x_1923_, 0);
v_consumers_1925_ = lean_ctor_get(v___x_1923_, 1);
v_closed_1926_ = lean_ctor_get_uint8(v___x_1923_, sizeof(void*)*2);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1928_ = v___x_1923_;
v_isShared_1929_ = v_isSharedCheck_1951_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_consumers_1925_);
lean_inc(v_producers_1924_);
lean_dec(v___x_1923_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1951_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1924_);
if (lean_obj_tag(v___x_1930_) == 1)
{
lean_object* v_val_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1949_; 
v_val_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1949_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_val_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1949_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_fst_1935_; lean_object* v_snd_1936_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1940_; 
v_fst_1935_ = lean_ctor_get(v_val_1931_, 0);
lean_inc(v_fst_1935_);
v_snd_1936_ = lean_ctor_get(v_val_1931_, 1);
lean_inc(v_snd_1936_);
lean_dec(v_val_1931_);
v_fst_1937_ = lean_ctor_get(v_fst_1935_, 0);
lean_inc(v_fst_1937_);
v_snd_1938_ = lean_ctor_get(v_fst_1935_, 1);
lean_inc(v_snd_1938_);
lean_dec(v_fst_1935_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v_snd_1936_);
v___x_1940_ = v___x_1928_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_snd_1936_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_consumers_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1948_, sizeof(void*)*2, v_closed_1926_);
v___x_1940_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1941_ = lean_st_ref_set(v_a_1921_, v___x_1940_);
v___x_1942_ = 1;
v___x_1943_ = lean_box(v___x_1942_);
v___x_1944_ = lean_io_promise_resolve(v___x_1943_, v_snd_1938_);
lean_dec(v_snd_1938_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v_fst_1937_);
v___x_1946_ = v___x_1933_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_fst_1937_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v___x_1950_; 
lean_dec(v___x_1930_);
lean_del_object(v___x_1928_);
lean_dec_ref(v_consumers_1925_);
v___x_1950_ = lean_box(0);
return v___x_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1952_);
lean_dec(v_a_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_1959_, lean_object* v_a_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_1959_, v_a_1960_);
lean_dec(v_a_1960_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_1964_){
_start:
{
lean_object* v___f_1966_; lean_object* v___x_1967_; 
v___f_1966_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_1967_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1964_, v___f_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_1971_, lean_object* v_ch_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_ch_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_1975_, v_ch_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_st_ref_get(v___y_1980_);
v___x_1983_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_1980_);
if (lean_obj_tag(v___x_1983_) == 1)
{
lean_object* v___x_1984_; 
lean_dec(v___x_1982_);
lean_dec_ref(v___f_1979_);
v___x_1984_ = lean_task_pure(v___x_1983_);
return v___x_1984_;
}
else
{
uint8_t v_closed_1985_; 
lean_dec(v___x_1983_);
v_closed_1985_ = lean_ctor_get_uint8(v___x_1982_, sizeof(void*)*2);
if (v_closed_1985_ == 0)
{
lean_object* v_producers_1986_; lean_object* v_consumers_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2002_; 
v_producers_1986_ = lean_ctor_get(v___x_1982_, 0);
v_consumers_1987_ = lean_ctor_get(v___x_1982_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1989_ = v___x_1982_;
v_isShared_1990_ = v_isSharedCheck_2002_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_consumers_1987_);
lean_inc(v_producers_1986_);
lean_dec(v___x_1982_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2002_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1991_ = lean_io_promise_new();
lean_inc(v___x_1991_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
v___x_1993_ = l_Std_Queue_enqueue___redArg(v___x_1992_, v_consumers_1987_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 1, v___x_1993_);
v___x_1995_ = v___x_1989_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_producers_1986_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2001_, sizeof(void*)*2, v_closed_1985_);
v___x_1995_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1996_ = lean_st_ref_set(v___y_1980_, v___x_1995_);
v___x_1997_ = 1;
v___x_1998_ = lean_io_promise_result_opt(v___x_1991_);
lean_dec(v___x_1991_);
v___x_1999_ = lean_unsigned_to_nat(0u);
v___x_2000_ = lean_task_map(v___f_1979_, v___x_1998_, v___x_1999_, v___x_1997_);
return v___x_2000_;
}
}
}
else
{
lean_object* v___x_2003_; 
lean_dec(v___x_1982_);
lean_dec_ref(v___f_1979_);
v___x_2003_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2004_, v___y_2005_);
lean_dec(v___y_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2010_){
_start:
{
lean_object* v___f_2012_; lean_object* v___x_2013_; 
v___f_2012_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2013_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2010_, v___f_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2017_, lean_object* v_ch_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2021_, lean_object* v_ch_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2021_, v_ch_2022_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2025_, lean_object* v_a_2026_){
_start:
{
uint8_t v___y_2028_; lean_object* v_producers_2032_; uint8_t v_closed_2033_; uint8_t v___x_2034_; 
v_producers_2032_ = lean_ctor_get(v_a_2026_, 0);
v_closed_2033_ = lean_ctor_get_uint8(v_a_2026_, sizeof(void*)*2);
v___x_2034_ = l_Std_Queue_isEmpty___redArg(v_producers_2032_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; 
v___x_2035_ = 1;
v___y_2028_ = v___x_2035_;
goto v___jp_2027_;
}
else
{
v___y_2028_ = v_closed_2033_;
goto v___jp_2027_;
}
v___jp_2027_:
{
lean_object* v_toPure_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_toPure_2029_ = lean_ctor_get(v_toApplicative_2025_, 1);
lean_inc(v_toPure_2029_);
lean_dec_ref(v_toApplicative_2025_);
v___x_2030_ = lean_box(v___y_2028_);
v___x_2031_ = lean_apply_2(v_toPure_2029_, lean_box(0), v___x_2030_);
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2036_, v_a_2037_);
lean_dec_ref(v_a_2037_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_toApplicative_2042_; lean_object* v_toBind_2043_; lean_object* v___f_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_toApplicative_2042_ = lean_ctor_get(v_inst_2039_, 0);
lean_inc_ref(v_toApplicative_2042_);
v_toBind_2043_ = lean_ctor_get(v_inst_2039_, 1);
lean_inc(v_toBind_2043_);
lean_dec_ref(v_inst_2039_);
v___f_2044_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2044_, 0, v_toApplicative_2042_);
v___x_2045_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2045_, 0, lean_box(0));
lean_closure_set(v___x_2045_, 1, lean_box(0));
lean_closure_set(v___x_2045_, 2, v_a_2041_);
v___x_2046_ = lean_apply_2(v_inst_2040_, lean_box(0), v___x_2045_);
v___x_2047_ = lean_apply_4(v_toBind_2043_, lean_box(0), lean_box(0), v___x_2046_, v___f_2044_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2048_, lean_object* v_00_u03b1_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_toApplicative_2053_; lean_object* v_toBind_2054_; lean_object* v___f_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_toApplicative_2053_ = lean_ctor_get(v_inst_2050_, 0);
lean_inc_ref(v_toApplicative_2053_);
v_toBind_2054_ = lean_ctor_get(v_inst_2050_, 1);
lean_inc(v_toBind_2054_);
lean_dec_ref(v_inst_2050_);
v___f_2055_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2055_, 0, v_toApplicative_2053_);
v___x_2056_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2056_, 0, lean_box(0));
lean_closure_set(v___x_2056_, 1, lean_box(0));
lean_closure_set(v___x_2056_, 2, v_a_2052_);
v___x_2057_ = lean_apply_2(v_inst_2051_, lean_box(0), v___x_2056_);
v___x_2058_ = lean_apply_4(v_toBind_2054_, lean_box(0), lean_box(0), v___x_2057_, v___f_2055_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2059_, lean_object* v___f_2060_, lean_object* v_x_2061_){
_start:
{
if (lean_obj_tag(v_x_2061_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v___f_2060_);
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
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2085_; 
v_isSharedCheck_2085_ = !lean_is_exclusive(v_x_2061_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v_x_2061_, 0);
lean_dec(v_unused_2086_);
v___x_2073_ = v_x_2061_;
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v_x_2061_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2075_ = 1;
v___x_2076_ = lean_box(v___x_2075_);
v___x_2077_ = lean_io_promise_resolve(v___x_2076_, v_snd_2059_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2077_);
v___x_2079_ = v___x_2073_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = 0;
v___x_2083_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2081_, v___x_2082_, v___x_2080_, v___f_2060_);
return v___x_2083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2087_, lean_object* v___f_2088_, lean_object* v_x_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2087_, v___f_2088_, v_x_2089_);
lean_dec(v_snd_2087_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2092_, lean_object* v_x_2093_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
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
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2141_; 
v_a_2104_ = lean_ctor_get(v_x_2093_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_x_2093_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2106_ = v_x_2093_;
v_isShared_2107_ = v_isSharedCheck_2141_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v_x_2093_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2141_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v_producers_2108_; lean_object* v_consumers_2109_; uint8_t v_closed_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2140_; 
v_producers_2108_ = lean_ctor_get(v_a_2104_, 0);
v_consumers_2109_ = lean_ctor_get(v_a_2104_, 1);
v_closed_2110_ = lean_ctor_get_uint8(v_a_2104_, sizeof(void*)*2);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2104_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2112_ = v_a_2104_;
v_isShared_2113_ = v_isSharedCheck_2140_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_consumers_2109_);
lean_inc(v_producers_2108_);
lean_dec(v_a_2104_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2140_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2108_);
if (lean_obj_tag(v___x_2114_) == 1)
{
lean_object* v_val_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2138_; 
v_val_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2138_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_val_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2138_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v_fst_2119_; lean_object* v_snd_2120_; lean_object* v_fst_2121_; lean_object* v_snd_2122_; lean_object* v___x_2124_; 
v_fst_2119_ = lean_ctor_get(v_val_2115_, 0);
lean_inc(v_fst_2119_);
v_snd_2120_ = lean_ctor_get(v_val_2115_, 1);
lean_inc(v_snd_2120_);
lean_dec(v_val_2115_);
v_fst_2121_ = lean_ctor_get(v_fst_2119_, 0);
lean_inc(v_fst_2121_);
v_snd_2122_ = lean_ctor_get(v_fst_2119_, 1);
lean_inc(v_snd_2122_);
lean_dec(v_fst_2119_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_snd_2120_);
v___x_2124_ = v___x_2112_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_snd_2120_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_consumers_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2137_, sizeof(void*)*2, v_closed_2110_);
v___x_2124_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v___f_2126_; lean_object* v___f_2127_; lean_object* v___x_2129_; 
v___x_2125_ = lean_st_ref_set(v_a_2092_, v___x_2124_);
v___f_2126_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2126_, 0, v_fst_2121_);
v___f_2127_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2127_, 0, v_snd_2122_);
lean_closure_set(v___f_2127_, 1, v___f_2126_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2125_);
v___x_2129_ = v___x_2106_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2125_);
v___x_2129_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set_tag(v___x_2117_, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2129_);
v___x_2131_ = v___x_2117_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = 0;
v___x_2134_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2132_, v___x_2133_, v___x_2131_, v___f_2127_);
return v___x_2134_;
}
}
}
}
}
else
{
lean_object* v___x_2139_; 
lean_dec(v___x_2114_);
lean_del_object(v___x_2112_);
lean_dec_ref(v_consumers_2109_);
lean_del_object(v___x_2106_);
v___x_2139_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2142_, lean_object* v_x_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2142_, v_x_2143_);
lean_dec(v_a_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v___f_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2148_ = lean_st_ref_get(v_a_2146_);
v___f_2149_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2149_, 0, v_a_2146_);
v___x_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
v___x_2152_ = lean_unsigned_to_nat(0u);
v___x_2153_ = 0;
v___x_2154_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2152_, v___x_2153_, v___x_2151_, v___f_2149_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2159_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_a_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2162_, v_a_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2166_, lean_object* v___y_2167_, lean_object* v___f_2168_, lean_object* v_x_2169_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___f_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v_lose_2166_);
v_a_2171_ = lean_ctor_get(v_x_2169_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_x_2169_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2173_ = v_x_2169_;
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v_x_2169_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2179_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
}
}
else
{
lean_object* v_a_2180_; uint8_t v___x_2181_; 
v_a_2180_ = lean_ctor_get(v_x_2169_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v_x_2169_);
v___x_2181_ = lean_unbox(v_a_2180_);
lean_dec(v_a_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
lean_dec_ref(v___f_2168_);
v___x_2182_ = lean_apply_2(v_lose_2166_, v___y_2167_, lean_box(0));
return v___x_2182_;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; 
lean_dec_ref(v_lose_2166_);
v___x_2183_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2167_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___x_2185_ = 0;
v___x_2186_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2184_, v___x_2185_, v___x_2183_, v___f_2168_);
return v___x_2186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2187_, lean_object* v___y_2188_, lean_object* v___f_2189_, lean_object* v_x_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2187_, v___y_2188_, v___f_2189_, v_x_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2193_, lean_object* v_lose_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_finished_2197_; lean_object* v_promise_2198_; lean_object* v___x_2199_; lean_object* v___f_2200_; lean_object* v___f_2201_; uint8_t v___y_2203_; uint8_t v___x_2213_; 
v_finished_2197_ = lean_ctor_get(v_w_2193_, 0);
lean_inc(v_finished_2197_);
v_promise_2198_ = lean_ctor_get(v_w_2193_, 1);
lean_inc(v_promise_2198_);
lean_dec_ref(v_w_2193_);
v___x_2199_ = lean_st_ref_take(v_finished_2197_);
v___f_2200_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2200_, 0, v_promise_2198_);
v___f_2201_ = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2201_, 0, v_lose_2194_);
lean_closure_set(v___f_2201_, 1, v___y_2195_);
lean_closure_set(v___f_2201_, 2, v___f_2200_);
v___x_2213_ = lean_unbox(v___x_2199_);
lean_dec(v___x_2199_);
if (v___x_2213_ == 0)
{
uint8_t v___x_2214_; 
v___x_2214_ = 1;
v___y_2203_ = v___x_2214_;
goto v___jp_2202_;
}
else
{
uint8_t v___x_2215_; 
v___x_2215_ = 0;
v___y_2203_ = v___x_2215_;
goto v___jp_2202_;
}
v___jp_2202_:
{
uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2204_ = 1;
v___x_2205_ = lean_box(v___x_2204_);
v___x_2206_ = lean_st_ref_set(v_finished_2197_, v___x_2205_);
lean_dec(v_finished_2197_);
v___x_2207_ = lean_box(v___y_2203_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = 0;
v___x_2212_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2210_, v___x_2211_, v___x_2209_, v___f_2201_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2216_, lean_object* v_lose_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2216_, v_lose_2217_, v___y_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2221_, lean_object* v_w_2222_, lean_object* v_lose_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2222_, v_lose_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_w_2228_, lean_object* v_lose_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2227_, v_w_2228_, v_lose_2229_, v___y_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2233_){
_start:
{
uint8_t v___y_2236_; 
if (lean_obj_tag(v_x_2233_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2248_; 
v_a_2240_ = lean_ctor_get(v_x_2233_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_x_2233_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2242_ = v_x_2233_;
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v_x_2233_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v_producers_2250_; uint8_t v_closed_2251_; uint8_t v___x_2252_; 
v_a_2249_ = lean_ctor_get(v_x_2233_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v_x_2233_);
v_producers_2250_ = lean_ctor_get(v_a_2249_, 0);
lean_inc_ref(v_producers_2250_);
v_closed_2251_ = lean_ctor_get_uint8(v_a_2249_, sizeof(void*)*2);
lean_dec(v_a_2249_);
v___x_2252_ = l_Std_Queue_isEmpty___redArg(v_producers_2250_);
lean_dec_ref(v_producers_2250_);
if (v___x_2252_ == 0)
{
uint8_t v___x_2253_; 
v___x_2253_ = 1;
v___y_2236_ = v___x_2253_;
goto v___jp_2235_;
}
else
{
v___y_2236_ = v_closed_2251_;
goto v___jp_2235_;
}
}
v___jp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = lean_box(v___y_2236_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2254_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2257_, lean_object* v_waiter_2258_, lean_object* v_x_2259_){
_start:
{
if (lean_obj_tag(v_x_2259_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v_waiter_2258_);
lean_dec(v___y_2257_);
v_a_2261_ = lean_ctor_get(v_x_2259_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_x_2259_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2263_ = v_x_2259_;
v_isShared_2264_ = v_isSharedCheck_2269_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v_x_2259_);
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
lean_object* v_a_2270_; uint8_t v___x_2271_; 
v_a_2270_ = lean_ctor_get(v_x_2259_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v_x_2259_);
v___x_2271_ = lean_unbox(v_a_2270_);
lean_dec(v_a_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v_producers_2273_; lean_object* v_consumers_2274_; uint8_t v_closed_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2286_; 
v___x_2272_ = lean_st_ref_take(v___y_2257_);
v_producers_2273_ = lean_ctor_get(v___x_2272_, 0);
v_consumers_2274_ = lean_ctor_get(v___x_2272_, 1);
v_closed_2275_ = lean_ctor_get_uint8(v___x_2272_, sizeof(void*)*2);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2277_ = v___x_2272_;
v_isShared_2278_ = v_isSharedCheck_2286_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_consumers_2274_);
lean_inc(v_producers_2273_);
lean_dec(v___x_2272_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2286_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2279_, 0, v_waiter_2258_);
v___x_2280_ = l_Std_Queue_enqueue___redArg(v___x_2279_, v_consumers_2274_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 1, v___x_2280_);
v___x_2282_ = v___x_2277_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_producers_2273_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2280_);
lean_ctor_set_uint8(v_reuseFailAlloc_2285_, sizeof(void*)*2, v_closed_2275_);
v___x_2282_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_st_ref_set(v___y_2257_, v___x_2282_);
lean_dec(v___y_2257_);
v___x_2284_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_2284_;
}
}
}
else
{
lean_object* v_lose_2287_; lean_object* v___x_2288_; 
v_lose_2287_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_2288_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2258_, v_lose_2287_, v___y_2257_);
return v___x_2288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2289_, lean_object* v_waiter_2290_, lean_object* v_x_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2289_, v_waiter_2290_, v_x_2291_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v___f_2294_, lean_object* v_waiter_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; 
v___x_2298_ = lean_st_ref_get(v___y_2296_);
v___x_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = 0;
v___x_2303_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2301_, v___x_2302_, v___x_2300_, v___f_2294_);
v___f_2304_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2304_, 0, v___y_2296_);
lean_closure_set(v___f_2304_, 1, v_waiter_2295_);
v___x_2305_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2301_, v___x_2302_, v___x_2303_, v___f_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v___f_2306_, lean_object* v_waiter_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v___f_2306_, v_waiter_2307_, v___y_2308_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2311_, lean_object* v_ch_2312_, lean_object* v_waiter_2313_){
_start:
{
lean_object* v___f_2315_; lean_object* v___x_2316_; 
v___f_2315_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2315_, 0, v___f_2311_);
lean_closure_set(v___f_2315_, 1, v_waiter_2313_);
v___x_2316_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2312_, v___f_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2317_, lean_object* v_ch_2318_, lean_object* v_waiter_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2317_, v_ch_2318_, v_waiter_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2322_, lean_object* v___f_2323_, lean_object* v_x_2324_){
_start:
{
if (lean_obj_tag(v_x_2324_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v___f_2323_);
lean_dec(v___y_2322_);
v_a_2326_ = lean_ctor_get(v_x_2324_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_x_2324_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v_x_2324_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v_x_2324_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2326_);
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
else
{
lean_object* v_a_2335_; uint8_t v___x_2336_; 
v_a_2335_ = lean_ctor_get(v_x_2324_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v_x_2324_);
v___x_2336_ = lean_unbox(v_a_2335_);
lean_dec(v_a_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2337_; 
lean_dec_ref(v___f_2323_);
lean_dec(v___y_2322_);
v___x_2337_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; 
v___x_2338_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2322_);
v___x_2339_ = lean_unsigned_to_nat(0u);
v___x_2340_ = 0;
v___x_2341_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2339_, v___x_2340_, v___x_2338_, v___f_2323_);
return v___x_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2342_, lean_object* v___f_2343_, lean_object* v_x_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2342_, v___f_2343_, v_x_2344_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2347_, lean_object* v___f_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___f_2357_; lean_object* v___x_2358_; 
v___x_2351_ = lean_st_ref_get(v___y_2349_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = 0;
v___x_2356_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2354_, v___x_2355_, v___x_2353_, v___f_2347_);
v___f_2357_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2357_, 0, v___y_2349_);
lean_closure_set(v___f_2357_, 1, v___f_2348_);
v___x_2358_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2354_, v___x_2355_, v___x_2356_, v___f_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2359_, lean_object* v___f_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2359_, v___f_2360_, v___y_2361_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2364_, uint8_t v_closed_2365_, lean_object* v___y_2366_, lean_object* v_x_2367_){
_start:
{
if (lean_obj_tag(v_x_2367_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v_producers_2364_);
v_a_2369_ = lean_ctor_get(v_x_2367_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_x_2367_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2371_ = v_x_2367_;
v_isShared_2372_ = v_isSharedCheck_2377_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v_x_2367_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2377_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
return v___x_2375_;
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2388_; 
v_a_2378_ = lean_ctor_get(v_x_2367_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_x_2367_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2380_ = v_x_2367_;
v_isShared_2381_ = v_isSharedCheck_2388_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v_x_2367_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2388_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2382_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2382_, 0, v_producers_2364_);
lean_ctor_set(v___x_2382_, 1, v_a_2378_);
lean_ctor_set_uint8(v___x_2382_, sizeof(void*)*2, v_closed_2365_);
v___x_2383_ = lean_st_ref_set(v___y_2366_, v___x_2382_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 0, v___x_2383_);
v___x_2385_ = v___x_2380_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2383_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2389_, lean_object* v_closed_2390_, lean_object* v___y_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_){
_start:
{
uint8_t v_closed_boxed_2394_; lean_object* v_res_2395_; 
v_closed_boxed_2394_ = lean_unbox(v_closed_2390_);
v_res_2395_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2389_, v_closed_boxed_2394_, v___y_2391_, v_x_2392_);
lean_dec(v___y_2391_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2396_, lean_object* v_x_2397_, lean_object* v_head_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2396_, v_x_2397_, v_head_2398_, v_x_2399_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
if (lean_obj_tag(v_x_2402_) == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v_x_2403_);
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
else
{
lean_object* v_head_2407_; lean_object* v_tail_2408_; lean_object* v___f_2409_; lean_object* v_val_2411_; 
v_head_2407_ = lean_ctor_get(v_x_2402_, 0);
lean_inc(v_head_2407_);
v_tail_2408_ = lean_ctor_get(v_x_2402_, 1);
lean_inc(v_tail_2408_);
lean_dec_ref(v_x_2402_);
lean_inc(v_head_2407_);
v___f_2409_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2409_, 0, v_tail_2408_);
lean_closure_set(v___f_2409_, 1, v_x_2403_);
lean_closure_set(v___f_2409_, 2, v_head_2407_);
if (lean_obj_tag(v_head_2407_) == 0)
{
lean_object* v___x_2415_; 
lean_dec_ref(v_head_2407_);
v___x_2415_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_2411_ = v___x_2415_;
goto v___jp_2410_;
}
else
{
lean_object* v_finished_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2430_; 
v_finished_2416_ = lean_ctor_get(v_head_2407_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_head_2407_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2418_ = v_head_2407_;
v_isShared_2419_ = v_isSharedCheck_2430_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_finished_2416_);
lean_dec(v_head_2407_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2430_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_finished_2420_; lean_object* v___x_2421_; lean_object* v___f_2422_; lean_object* v___x_2424_; 
v_finished_2420_ = lean_ctor_get(v_finished_2416_, 0);
lean_inc(v_finished_2420_);
lean_dec_ref(v_finished_2416_);
v___x_2421_ = lean_st_ref_get(v_finished_2420_);
lean_dec(v_finished_2420_);
v___f_2422_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2421_);
v___x_2424_ = v___x_2418_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2421_);
v___x_2424_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = 0;
v___x_2428_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2426_, v___x_2427_, v___x_2425_, v___f_2422_);
v_val_2411_ = v___x_2428_;
goto v___jp_2410_;
}
}
}
v___jp_2410_:
{
lean_object* v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_unsigned_to_nat(0u);
v___x_2413_ = 0;
v___x_2414_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2412_, v___x_2413_, v_val_2411_, v___f_2409_);
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2431_, lean_object* v_x_2432_, lean_object* v_head_2433_, lean_object* v_x_2434_){
_start:
{
if (lean_obj_tag(v_x_2434_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v_head_2433_);
lean_dec(v_x_2432_);
lean_dec(v_tail_2431_);
v_a_2436_ = lean_ctor_get(v_x_2434_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_x_2434_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2438_ = v_x_2434_;
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v_x_2434_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
}
}
else
{
lean_object* v_a_2445_; uint8_t v___x_2446_; 
v_a_2445_ = lean_ctor_get(v_x_2434_, 0);
lean_inc(v_a_2445_);
lean_dec_ref(v_x_2434_);
v___x_2446_ = lean_unbox(v_a_2445_);
lean_dec(v_a_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; 
lean_dec_ref(v_head_2433_);
v___x_2447_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2431_, v_x_2432_);
return v___x_2447_;
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_head_2433_);
lean_ctor_set(v___x_2448_, 1, v_x_2432_);
v___x_2449_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2431_, v___x_2448_);
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2450_, lean_object* v_x_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2450_, v_x_2451_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v_eList_2454_, lean_object* v___x_2455_, lean_object* v___f_2456_, lean_object* v_x_2457_){
_start:
{
if (lean_obj_tag(v_x_2457_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v___f_2456_);
lean_dec(v___x_2455_);
lean_dec(v_eList_2454_);
v_a_2459_ = lean_ctor_get(v_x_2457_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_x_2457_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2461_ = v_x_2457_;
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v_x_2457_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2464_);
return v___x_2465_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; 
v_a_2468_ = lean_ctor_get(v_x_2457_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v_x_2457_);
lean_inc(v___x_2455_);
v___x_2469_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2454_, v___x_2455_);
v___x_2470_ = lean_unsigned_to_nat(0u);
v___x_2471_ = 0;
v___x_2472_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2470_, v___x_2471_, v___x_2469_, v___f_2456_);
v___f_2473_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2473_, 0, v_a_2468_);
lean_closure_set(v___f_2473_, 1, v___x_2455_);
v___x_2474_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2470_, v___x_2471_, v___x_2472_, v___f_2473_);
return v___x_2474_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_eList_2475_, lean_object* v___x_2476_, lean_object* v___f_2477_, lean_object* v_x_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v_eList_2475_, v___x_2476_, v___f_2477_, v_x_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_eList_2484_; lean_object* v_dList_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___f_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; 
v_eList_2484_ = lean_ctor_get(v_q_2481_, 0);
lean_inc(v_eList_2484_);
v_dList_2485_ = lean_ctor_get(v_q_2481_, 1);
lean_inc(v_dList_2485_);
lean_dec_ref(v_q_2481_);
v___x_2486_ = lean_box(0);
v___x_2487_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2485_, v___x_2486_);
v___f_2488_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2489_ = lean_unsigned_to_nat(0u);
v___x_2490_ = 0;
v___x_2491_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2489_, v___x_2490_, v___x_2487_, v___f_2488_);
v___f_2492_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2492_, 0, v_eList_2484_);
lean_closure_set(v___f_2492_, 1, v___x_2486_);
lean_closure_set(v___f_2492_, 2, v___f_2488_);
v___x_2493_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2489_, v___x_2490_, v___x_2491_, v___f_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2494_, v___y_2495_);
lean_dec(v___y_2495_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2498_, lean_object* v_x_2499_){
_start:
{
if (lean_obj_tag(v_x_2499_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2509_; 
lean_dec(v___y_2498_);
v_a_2501_ = lean_ctor_get(v_x_2499_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_x_2499_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2503_ = v_x_2499_;
v_isShared_2504_ = v_isSharedCheck_2509_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v_x_2499_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2509_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v_producers_2511_; lean_object* v_consumers_2512_; uint8_t v_closed_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___f_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; 
v_a_2510_ = lean_ctor_get(v_x_2499_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v_x_2499_);
v_producers_2511_ = lean_ctor_get(v_a_2510_, 0);
lean_inc_ref(v_producers_2511_);
v_consumers_2512_ = lean_ctor_get(v_a_2510_, 1);
lean_inc_ref(v_consumers_2512_);
v_closed_2513_ = lean_ctor_get_uint8(v_a_2510_, sizeof(void*)*2);
lean_dec(v_a_2510_);
v___x_2514_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2512_, v___y_2498_);
v___x_2515_ = lean_box(v_closed_2513_);
v___f_2516_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2516_, 0, v_producers_2511_);
lean_closure_set(v___f_2516_, 1, v___x_2515_);
lean_closure_set(v___f_2516_, 2, v___y_2498_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = 0;
v___x_2519_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2517_, v___x_2518_, v___x_2514_, v___f_2516_);
return v___x_2519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2520_, lean_object* v_x_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2520_, v_x_2521_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2526_ = lean_st_ref_get(v___y_2524_);
v___f_2527_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2527_, 0, v___y_2524_);
v___x_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
v___x_2530_ = lean_unsigned_to_nat(0u);
v___x_2531_ = 0;
v___x_2532_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2530_, v___x_2531_, v___x_2529_, v___f_2527_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2533_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2541_){
_start:
{
lean_object* v___f_2542_; lean_object* v___f_2543_; lean_object* v___f_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___f_2542_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref(v_ch_2541_);
v___f_2543_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2543_, 0, v___f_2542_);
lean_closure_set(v___f_2543_, 1, v_ch_2541_);
v___f_2544_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2545_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
lean_inc_ref(v_ch_2541_);
v___x_2546_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2546_, 0, lean_box(0));
lean_closure_set(v___x_2546_, 1, lean_box(0));
lean_closure_set(v___x_2546_, 2, v_ch_2541_);
lean_closure_set(v___x_2546_, 3, v___f_2544_);
v___x_2547_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2547_, 0, lean_box(0));
lean_closure_set(v___x_2547_, 1, lean_box(0));
lean_closure_set(v___x_2547_, 2, v_ch_2541_);
lean_closure_set(v___x_2547_, 3, v___f_2545_);
v___x_2548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___f_2543_);
lean_ctor_set(v___x_2548_, 2, v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2549_, lean_object* v_ch_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2552_, lean_object* v_q_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2553_, v___y_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2557_, lean_object* v_q_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2557_, v_q_2558_, v___y_2559_);
lean_dec(v___y_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2563_, v_x_2564_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2568_, v_x_2569_, v_x_2570_, v___y_2571_);
lean_dec(v___y_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2574_, uint8_t v_b_2575_){
_start:
{
lean_object* v_promise_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_promise_2577_ = lean_ctor_get(v_c_2574_, 0);
v___x_2578_ = lean_box(v_b_2575_);
v___x_2579_ = lean_io_promise_resolve(v___x_2578_, v_promise_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2580_, lean_object* v_b_2581_, lean_object* v_a_2582_){
_start:
{
uint8_t v_b_boxed_2583_; lean_object* v_res_2584_; 
v_b_boxed_2583_ = lean_unbox(v_b_2581_);
v_res_2584_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2580_, v_b_boxed_2583_);
lean_dec_ref(v_c_2580_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2585_, lean_object* v_c_2586_, uint8_t v_b_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2586_, v_b_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2590_, lean_object* v_c_2591_, lean_object* v_b_2592_, lean_object* v_a_2593_){
_start:
{
uint8_t v_b_boxed_2594_; lean_object* v_res_2595_; 
v_b_boxed_2594_ = lean_unbox(v_b_2592_);
v_res_2595_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2590_, v_c_2591_, v_b_boxed_2594_);
lean_dec_ref(v_c_2591_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_st_mk_ref(v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2600_);
lean_dec(v_x_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2603_, lean_object* v_f_2604_, lean_object* v_xs_2605_, lean_object* v_k_2606_, lean_object* v_acc_2607_){
_start:
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_nat_dec_lt(v_k_2606_, v_n_2603_);
if (v___x_2609_ == 0)
{
lean_dec(v_k_2606_);
lean_dec_ref(v_f_2604_);
return v_acc_2607_;
}
else
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2610_ = lean_array_fget_borrowed(v_xs_2605_, v_k_2606_);
lean_inc_ref(v_f_2604_);
lean_inc(v___x_2610_);
v___x_2611_ = lean_apply_2(v_f_2604_, v___x_2610_, lean_box(0));
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_add(v_k_2606_, v___x_2612_);
lean_dec(v_k_2606_);
v___x_2614_ = lean_array_push(v_acc_2607_, v___x_2611_);
v_k_2606_ = v___x_2613_;
v_acc_2607_ = v___x_2614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2616_, lean_object* v_f_2617_, lean_object* v_xs_2618_, lean_object* v_k_2619_, lean_object* v_acc_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2616_, v_f_2617_, v_xs_2618_, v_k_2619_, v_acc_2620_);
lean_dec_ref(v_xs_2618_);
lean_dec(v_n_2616_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2626_){
_start:
{
lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___f_2628_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2626_);
v___x_2629_ = l_Array_range(v_capacity_2626_);
v___x_2630_ = lean_unsigned_to_nat(0u);
v___x_2631_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2632_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2626_, v___f_2628_, v___x_2629_, v___x_2630_, v___x_2631_);
lean_dec_ref(v___x_2629_);
v___x_2633_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2634_ = 0;
v___x_2635_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2635_, 0, v___x_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2633_);
lean_ctor_set(v___x_2635_, 2, v_capacity_2626_);
lean_ctor_set(v___x_2635_, 3, v___x_2632_);
lean_ctor_set(v___x_2635_, 4, v___x_2630_);
lean_ctor_set(v___x_2635_, 5, v___x_2630_);
lean_ctor_set(v___x_2635_, 6, v___x_2630_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*7, v___x_2634_);
v___x_2636_ = l_Std_Mutex_new___redArg(v___x_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2637_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2640_, lean_object* v_capacity_2641_, lean_object* v_hcap_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2641_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2645_, lean_object* v_capacity_2646_, lean_object* v_hcap_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2645_, v_capacity_2646_, v_hcap_2647_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2650_, lean_object* v_00_u03b2_2651_, lean_object* v_n_2652_, lean_object* v_f_2653_, lean_object* v_xs_2654_, lean_object* v_k_2655_, lean_object* v_h_2656_, lean_object* v_acc_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2652_, v_f_2653_, v_xs_2654_, v_k_2655_, v_acc_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_00_u03b2_2661_, lean_object* v_n_2662_, lean_object* v_f_2663_, lean_object* v_xs_2664_, lean_object* v_k_2665_, lean_object* v_h_2666_, lean_object* v_acc_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2660_, v_00_u03b2_2661_, v_n_2662_, v_f_2663_, v_xs_2664_, v_k_2665_, v_h_2666_, v_acc_2667_);
lean_dec_ref(v_xs_2664_);
lean_dec(v_n_2662_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2670_, lean_object* v_cap_2671_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_nat_add(v_idx_2670_, v___x_2672_);
v___x_2674_ = lean_nat_dec_eq(v___x_2673_, v_cap_2671_);
if (v___x_2674_ == 0)
{
return v___x_2673_;
}
else
{
lean_object* v___x_2675_; 
lean_dec(v___x_2673_);
v___x_2675_ = lean_unsigned_to_nat(0u);
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2676_, lean_object* v_cap_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2676_, v_cap_2677_);
lean_dec(v_cap_2677_);
lean_dec(v_idx_2676_);
return v_res_2678_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_st_2683_; lean_object* v___y_2684_; lean_object* v___x_2687_; lean_object* v_producers_2688_; lean_object* v_consumers_2689_; lean_object* v_capacity_2690_; lean_object* v_buf_2691_; lean_object* v_bufCount_2692_; lean_object* v_sendIdx_2693_; lean_object* v_recvIdx_2694_; uint8_t v_closed_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2721_; 
v___x_2687_ = lean_st_ref_get(v_a_2680_);
v_producers_2688_ = lean_ctor_get(v___x_2687_, 0);
v_consumers_2689_ = lean_ctor_get(v___x_2687_, 1);
v_capacity_2690_ = lean_ctor_get(v___x_2687_, 2);
v_buf_2691_ = lean_ctor_get(v___x_2687_, 3);
v_bufCount_2692_ = lean_ctor_get(v___x_2687_, 4);
v_sendIdx_2693_ = lean_ctor_get(v___x_2687_, 5);
v_recvIdx_2694_ = lean_ctor_get(v___x_2687_, 6);
v_closed_2695_ = lean_ctor_get_uint8(v___x_2687_, sizeof(void*)*7);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2697_ = v___x_2687_;
v_isShared_2698_ = v_isSharedCheck_2721_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_recvIdx_2694_);
lean_inc(v_sendIdx_2693_);
lean_inc(v_bufCount_2692_);
lean_inc(v_buf_2691_);
lean_inc(v_capacity_2690_);
lean_inc(v_consumers_2689_);
lean_inc(v_producers_2688_);
lean_dec(v___x_2687_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2721_;
goto v_resetjp_2696_;
}
v___jp_2682_:
{
lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = lean_st_ref_set(v___y_2684_, v_st_2683_);
v___x_2686_ = 1;
return v___x_2686_;
}
v_resetjp_2696_:
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_nat_dec_eq(v_bufCount_2692_, v_capacity_2690_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___y_2706_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2700_ = lean_array_fget_borrowed(v_buf_2691_, v_sendIdx_2693_);
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_v_2679_);
v___x_2702_ = lean_st_ref_set(v___x_2700_, v___x_2701_);
v___x_2703_ = lean_unsigned_to_nat(1u);
v___x_2704_ = lean_nat_add(v_bufCount_2692_, v___x_2703_);
lean_dec(v_bufCount_2692_);
v___x_2717_ = lean_nat_add(v_sendIdx_2693_, v___x_2703_);
lean_dec(v_sendIdx_2693_);
v___x_2718_ = lean_nat_dec_eq(v___x_2717_, v_capacity_2690_);
if (v___x_2718_ == 0)
{
v___y_2706_ = v___x_2717_;
goto v___jp_2705_;
}
else
{
lean_object* v___x_2719_; 
lean_dec(v___x_2717_);
v___x_2719_ = lean_unsigned_to_nat(0u);
v___y_2706_ = v___x_2719_;
goto v___jp_2705_;
}
v___jp_2705_:
{
lean_object* v___x_2708_; 
lean_inc(v_recvIdx_2694_);
lean_inc(v___y_2706_);
lean_inc(v___x_2704_);
lean_inc_ref(v_buf_2691_);
lean_inc(v_capacity_2690_);
lean_inc_ref(v_consumers_2689_);
lean_inc_ref(v_producers_2688_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 5, v___y_2706_);
lean_ctor_set(v___x_2697_, 4, v___x_2704_);
v___x_2708_ = v___x_2697_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_producers_2688_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_consumers_2689_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v_capacity_2690_);
lean_ctor_set(v_reuseFailAlloc_2716_, 3, v_buf_2691_);
lean_ctor_set(v_reuseFailAlloc_2716_, 4, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2716_, 5, v___y_2706_);
lean_ctor_set(v_reuseFailAlloc_2716_, 6, v_recvIdx_2694_);
lean_ctor_set_uint8(v_reuseFailAlloc_2716_, sizeof(void*)*7, v_closed_2695_);
v___x_2708_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2689_);
if (lean_obj_tag(v___x_2709_) == 1)
{
lean_object* v_val_2710_; lean_object* v_fst_2711_; lean_object* v_snd_2712_; uint8_t v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
lean_dec_ref(v___x_2708_);
v_val_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_val_2710_);
lean_dec_ref(v___x_2709_);
v_fst_2711_ = lean_ctor_get(v_val_2710_, 0);
lean_inc(v_fst_2711_);
v_snd_2712_ = lean_ctor_get(v_val_2710_, 1);
lean_inc(v_snd_2712_);
lean_dec(v_val_2710_);
v___x_2713_ = 1;
v___x_2714_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2711_, v___x_2713_);
lean_dec(v_fst_2711_);
v___x_2715_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2715_, 0, v_producers_2688_);
lean_ctor_set(v___x_2715_, 1, v_snd_2712_);
lean_ctor_set(v___x_2715_, 2, v_capacity_2690_);
lean_ctor_set(v___x_2715_, 3, v_buf_2691_);
lean_ctor_set(v___x_2715_, 4, v___x_2704_);
lean_ctor_set(v___x_2715_, 5, v___y_2706_);
lean_ctor_set(v___x_2715_, 6, v_recvIdx_2694_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*7, v_closed_2695_);
v_st_2683_ = v___x_2715_;
v___y_2684_ = v_a_2680_;
goto v___jp_2682_;
}
else
{
lean_dec(v___x_2709_);
lean_dec(v___y_2706_);
lean_dec(v___x_2704_);
lean_dec(v_recvIdx_2694_);
lean_dec_ref(v_buf_2691_);
lean_dec(v_capacity_2690_);
lean_dec_ref(v_producers_2688_);
v_st_2683_ = v___x_2708_;
v___y_2684_ = v_a_2680_;
goto v___jp_2682_;
}
}
}
}
else
{
uint8_t v___x_2720_; 
lean_del_object(v___x_2697_);
lean_dec(v_recvIdx_2694_);
lean_dec(v_sendIdx_2693_);
lean_dec(v_bufCount_2692_);
lean_dec_ref(v_buf_2691_);
lean_dec(v_capacity_2690_);
lean_dec_ref(v_consumers_2689_);
lean_dec_ref(v_producers_2688_);
lean_dec(v_v_2679_);
v___x_2720_ = 0;
return v___x_2720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
uint8_t v_res_2725_; lean_object* v_r_2726_; 
v_res_2725_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2722_, v_a_2723_);
lean_dec(v_a_2723_);
v_r_2726_ = lean_box(v_res_2725_);
return v_r_2726_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2727_, lean_object* v_v_2728_, lean_object* v_a_2729_){
_start:
{
uint8_t v___x_2731_; 
v___x_2731_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2728_, v_a_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_v_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
uint8_t v_res_2736_; lean_object* v_r_2737_; 
v_res_2736_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2732_, v_v_2733_, v_a_2734_);
lean_dec(v_a_2734_);
v_r_2737_ = lean_box(v_res_2736_);
return v_r_2737_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; uint8_t v_closed_2742_; 
v___x_2741_ = lean_st_ref_get(v___y_2739_);
v_closed_2742_ = lean_ctor_get_uint8(v___x_2741_, sizeof(void*)*7);
lean_dec(v___x_2741_);
if (v_closed_2742_ == 0)
{
uint8_t v___x_2743_; 
v___x_2743_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2738_, v___y_2739_);
return v___x_2743_;
}
else
{
uint8_t v___x_2744_; 
lean_dec(v_v_2738_);
v___x_2744_ = 0;
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
uint8_t v_res_2748_; lean_object* v_r_2749_; 
v_res_2748_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2745_, v___y_2746_);
lean_dec(v___y_2746_);
v_r_2749_ = lean_box(v_res_2748_);
return v_r_2749_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2750_, lean_object* v_v_2751_){
_start:
{
lean_object* v___f_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___f_2753_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2753_, 0, v_v_2751_);
v___x_2754_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2750_, v___f_2753_);
v___x_2755_ = lean_unbox(v___x_2754_);
lean_dec(v___x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2756_, lean_object* v_v_2757_, lean_object* v_a_2758_){
_start:
{
uint8_t v_res_2759_; lean_object* v_r_2760_; 
v_res_2759_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2756_, v_v_2757_);
v_r_2760_ = lean_box(v_res_2759_);
return v_r_2760_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2761_, lean_object* v_ch_2762_, lean_object* v_v_2763_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2762_, v_v_2763_);
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
v___x_2795_ = lean_st_ref_set(v___y_2774_, v___x_2794_);
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
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; size_t v___x_2853_; size_t v___x_2854_; 
v_a_2850_ = lean_array_uget_borrowed(v_as_2843_, v_i_2845_);
v___x_2851_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2850_, v___x_2842_);
v___x_2852_ = lean_box(0);
v___x_2853_ = ((size_t)1ULL);
v___x_2854_ = lean_usize_add(v_i_2845_, v___x_2853_);
v_i_2845_ = v___x_2854_;
v_b_2846_ = v___x_2852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2856_, lean_object* v_as_2857_, lean_object* v_sz_2858_, lean_object* v_i_2859_, lean_object* v_b_2860_, lean_object* v___y_2861_){
_start:
{
uint8_t v___x_1988__boxed_2862_; size_t v_sz_boxed_2863_; size_t v_i_boxed_2864_; lean_object* v_res_2865_; 
v___x_1988__boxed_2862_ = lean_unbox(v___x_2856_);
v_sz_boxed_2863_ = lean_unbox_usize(v_sz_2858_);
lean_dec(v_sz_2858_);
v_i_boxed_2864_ = lean_unbox_usize(v_i_2859_);
lean_dec(v_i_2859_);
v_res_2865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1988__boxed_2862_, v_as_2857_, v_sz_boxed_2863_, v_i_boxed_2864_, v_b_2860_);
lean_dec_ref(v_as_2857_);
return v_res_2865_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Std_Queue_empty(lean_box(0));
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; uint8_t v_closed_2870_; 
v___x_2869_ = lean_st_ref_get(v___y_2867_);
v_closed_2870_ = lean_ctor_get_uint8(v___x_2869_, sizeof(void*)*7);
if (v_closed_2870_ == 0)
{
lean_object* v_producers_2871_; lean_object* v_consumers_2872_; lean_object* v_capacity_2873_; lean_object* v_buf_2874_; lean_object* v_bufCount_2875_; lean_object* v_sendIdx_2876_; lean_object* v_recvIdx_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2900_; 
v_producers_2871_ = lean_ctor_get(v___x_2869_, 0);
v_consumers_2872_ = lean_ctor_get(v___x_2869_, 1);
v_capacity_2873_ = lean_ctor_get(v___x_2869_, 2);
v_buf_2874_ = lean_ctor_get(v___x_2869_, 3);
v_bufCount_2875_ = lean_ctor_get(v___x_2869_, 4);
v_sendIdx_2876_ = lean_ctor_get(v___x_2869_, 5);
v_recvIdx_2877_ = lean_ctor_get(v___x_2869_, 6);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2879_ = v___x_2869_;
v_isShared_2880_ = v_isSharedCheck_2900_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_recvIdx_2877_);
lean_inc(v_sendIdx_2876_);
lean_inc(v_bufCount_2875_);
lean_inc(v_buf_2874_);
lean_inc(v_capacity_2873_);
lean_inc(v_consumers_2872_);
lean_inc(v_producers_2871_);
lean_dec(v___x_2869_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2900_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; size_t v_sz_2883_; size_t v___x_2884_; lean_object* v___x_2885_; 
v___x_2881_ = l_Std_Queue_toArray___redArg(v_consumers_2872_);
v___x_2882_ = lean_box(0);
v_sz_2883_ = lean_array_size(v___x_2881_);
v___x_2884_ = ((size_t)0ULL);
v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2870_, v___x_2881_, v_sz_2883_, v___x_2884_, v___x_2882_);
lean_dec_ref(v___x_2881_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2898_; 
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; 
v_unused_2899_ = lean_ctor_get(v___x_2885_, 0);
lean_dec(v_unused_2899_);
v___x_2887_ = v___x_2885_;
v_isShared_2888_ = v_isSharedCheck_2898_;
goto v_resetjp_2886_;
}
else
{
lean_dec(v___x_2885_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2898_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; uint8_t v___x_2890_; lean_object* v___x_2892_; 
v___x_2889_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0);
v___x_2890_ = 1;
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 1, v___x_2889_);
v___x_2892_ = v___x_2879_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_producers_2871_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_capacity_2873_);
lean_ctor_set(v_reuseFailAlloc_2897_, 3, v_buf_2874_);
lean_ctor_set(v_reuseFailAlloc_2897_, 4, v_bufCount_2875_);
lean_ctor_set(v_reuseFailAlloc_2897_, 5, v_sendIdx_2876_);
lean_ctor_set(v_reuseFailAlloc_2897_, 6, v_recvIdx_2877_);
v___x_2892_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_ctor_set_uint8(v___x_2892_, sizeof(void*)*7, v___x_2890_);
v___x_2893_ = lean_st_ref_set(v___y_2867_, v___x_2892_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2882_);
v___x_2895_ = v___x_2887_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2882_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_del_object(v___x_2879_);
lean_dec(v_recvIdx_2877_);
lean_dec(v_sendIdx_2876_);
lean_dec(v_bufCount_2875_);
lean_dec_ref(v_buf_2874_);
lean_dec(v_capacity_2873_);
lean_dec_ref(v_producers_2871_);
return v___x_2885_;
}
}
}
else
{
uint8_t v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
lean_dec(v___x_2869_);
v___x_2901_ = 1;
v___x_2902_ = lean_box(v___x_2901_);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
return v___x_2903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2904_);
lean_dec(v___y_2904_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2908_){
_start:
{
lean_object* v___f_2910_; lean_object* v___x_2911_; 
v___f_2910_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2911_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2908_, v___f_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2912_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2915_, lean_object* v_ch_2916_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2919_, lean_object* v_ch_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2919_, v_ch_2920_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2923_, uint8_t v___x_2924_, lean_object* v_as_2925_, size_t v_sz_2926_, size_t v_i_2927_, lean_object* v_b_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2924_, v_as_2925_, v_sz_2926_, v_i_2927_, v_b_2928_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2932_, lean_object* v___x_2933_, lean_object* v_as_2934_, lean_object* v_sz_2935_, lean_object* v_i_2936_, lean_object* v_b_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v___x_2086__boxed_2940_; size_t v_sz_boxed_2941_; size_t v_i_boxed_2942_; lean_object* v_res_2943_; 
v___x_2086__boxed_2940_ = lean_unbox(v___x_2933_);
v_sz_boxed_2941_ = lean_unbox_usize(v_sz_2935_);
lean_dec(v_sz_2935_);
v_i_boxed_2942_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_res_2943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2932_, v___x_2086__boxed_2940_, v_as_2934_, v_sz_boxed_2941_, v_i_boxed_2942_, v_b_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v_as_2934_);
return v_res_2943_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; uint8_t v_closed_2947_; 
v___x_2946_ = lean_st_ref_get(v___y_2944_);
v_closed_2947_ = lean_ctor_get_uint8(v___x_2946_, sizeof(void*)*7);
lean_dec(v___x_2946_);
return v_closed_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
uint8_t v_res_2950_; lean_object* v_r_2951_; 
v_res_2950_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_2948_);
lean_dec(v___y_2948_);
v_r_2951_ = lean_box(v_res_2950_);
return v_r_2951_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_2953_){
_start:
{
lean_object* v___f_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___f_2955_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_2956_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2953_, v___f_2955_);
v___x_2957_ = lean_unbox(v___x_2956_);
lean_dec(v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_2958_, lean_object* v_a_2959_){
_start:
{
uint8_t v_res_2960_; lean_object* v_r_2961_; 
v_res_2960_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_2958_);
v_r_2961_ = lean_box(v_res_2960_);
return v_r_2961_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_2962_, lean_object* v_ch_2963_){
_start:
{
uint8_t v___x_2965_; 
v___x_2965_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_2963_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_2966_, lean_object* v_ch_2967_, lean_object* v_a_2968_){
_start:
{
uint8_t v_res_2969_; lean_object* v_r_2970_; 
v_res_2969_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_2966_, v_ch_2967_);
v_r_2970_ = lean_box(v_res_2969_);
return v_r_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_toPure_2974_; lean_object* v___x_2975_; 
v_toPure_2974_ = lean_ctor_get(v_toApplicative_2971_, 1);
lean_inc(v_toPure_2974_);
lean_dec_ref(v_toApplicative_2971_);
v___x_2975_ = lean_apply_2(v_toPure_2974_, lean_box(0), v_a_2972_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_2976_, lean_object* v_toBind_2977_, lean_object* v___f_2978_, lean_object* v_____r_2979_, lean_object* v_st_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2982_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_2982_, 0, lean_box(0));
lean_closure_set(v___x_2982_, 1, lean_box(0));
lean_closure_set(v___x_2982_, 2, v___y_2981_);
lean_closure_set(v___x_2982_, 3, v_st_2980_);
v___x_2983_ = lean_apply_2(v_inst_2976_, lean_box(0), v___x_2982_);
v___x_2984_ = lean_apply_4(v_toBind_2977_, lean_box(0), lean_box(0), v___x_2983_, v___f_2978_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_2985_, lean_object* v_consumers_2986_, lean_object* v_capacity_2987_, lean_object* v_buf_2988_, lean_object* v___x_2989_, lean_object* v_sendIdx_2990_, lean_object* v___y_2991_, uint8_t v_closed_2992_, lean_object* v___f_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2996_, 0, v_snd_2985_);
lean_ctor_set(v___x_2996_, 1, v_consumers_2986_);
lean_ctor_set(v___x_2996_, 2, v_capacity_2987_);
lean_ctor_set(v___x_2996_, 3, v_buf_2988_);
lean_ctor_set(v___x_2996_, 4, v___x_2989_);
lean_ctor_set(v___x_2996_, 5, v_sendIdx_2990_);
lean_ctor_set(v___x_2996_, 6, v___y_2991_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*7, v_closed_2992_);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_apply_3(v___f_2993_, v___x_2997_, v___x_2996_, v_a_2994_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_2999_, lean_object* v_consumers_3000_, lean_object* v_capacity_3001_, lean_object* v_buf_3002_, lean_object* v___x_3003_, lean_object* v_sendIdx_3004_, lean_object* v___y_3005_, lean_object* v_closed_3006_, lean_object* v___f_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
uint8_t v_closed_boxed_3010_; lean_object* v_res_3011_; 
v_closed_boxed_3010_ = lean_unbox(v_closed_3006_);
v_res_3011_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_2999_, v_consumers_3000_, v_capacity_3001_, v_buf_3002_, v___x_3003_, v_sendIdx_3004_, v___y_3005_, v_closed_boxed_3010_, v___f_3007_, v_a_3008_, v_a_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3012_, lean_object* v_inst_3013_, lean_object* v_toBind_3014_, lean_object* v_bufCount_3015_, lean_object* v_producers_3016_, lean_object* v_consumers_3017_, lean_object* v_capacity_3018_, lean_object* v_buf_3019_, lean_object* v_sendIdx_3020_, uint8_t v_closed_3021_, lean_object* v_a_3022_, uint8_t v___x_3023_, lean_object* v_inst_3024_, lean_object* v_recvIdx_3025_, lean_object* v___x_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v___f_3028_; lean_object* v___f_3029_; lean_object* v___y_3031_; lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___f_3028_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3028_, 0, v_toApplicative_3012_);
lean_closure_set(v___f_3028_, 1, v_a_3027_);
lean_inc_ref(v___f_3028_);
lean_inc(v_toBind_3014_);
lean_inc(v_inst_3013_);
v___f_3029_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1), 6, 3);
lean_closure_set(v___f_3029_, 0, v_inst_3013_);
lean_closure_set(v___f_3029_, 1, v_toBind_3014_);
lean_closure_set(v___f_3029_, 2, v___f_3028_);
v___x_3047_ = lean_unsigned_to_nat(1u);
v___x_3048_ = lean_nat_add(v_recvIdx_3025_, v___x_3047_);
v___x_3049_ = lean_nat_dec_eq(v___x_3048_, v_capacity_3018_);
if (v___x_3049_ == 0)
{
lean_dec(v___x_3026_);
v___y_3031_ = v___x_3048_;
goto v___jp_3030_;
}
else
{
lean_dec(v___x_3048_);
v___y_3031_ = v___x_3026_;
goto v___jp_3030_;
}
v___jp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3032_ = lean_unsigned_to_nat(1u);
v___x_3033_ = lean_nat_sub(v_bufCount_3015_, v___x_3032_);
lean_inc(v___y_3031_);
lean_inc(v_sendIdx_3020_);
lean_inc(v___x_3033_);
lean_inc_ref(v_buf_3019_);
lean_inc(v_capacity_3018_);
lean_inc_ref(v_consumers_3017_);
lean_inc_ref(v_producers_3016_);
v___x_3034_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3034_, 0, v_producers_3016_);
lean_ctor_set(v___x_3034_, 1, v_consumers_3017_);
lean_ctor_set(v___x_3034_, 2, v_capacity_3018_);
lean_ctor_set(v___x_3034_, 3, v_buf_3019_);
lean_ctor_set(v___x_3034_, 4, v___x_3033_);
lean_ctor_set(v___x_3034_, 5, v_sendIdx_3020_);
lean_ctor_set(v___x_3034_, 6, v___y_3031_);
lean_ctor_set_uint8(v___x_3034_, sizeof(void*)*7, v_closed_3021_);
v___x_3035_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3016_);
if (lean_obj_tag(v___x_3035_) == 1)
{
lean_object* v_val_3036_; lean_object* v_fst_3037_; lean_object* v_snd_3038_; lean_object* v___x_3039_; lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_dec_ref(v___x_3034_);
lean_dec_ref(v___f_3028_);
lean_dec(v_inst_3013_);
v_val_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_val_3036_);
lean_dec_ref(v___x_3035_);
v_fst_3037_ = lean_ctor_get(v_val_3036_, 0);
lean_inc(v_fst_3037_);
v_snd_3038_ = lean_ctor_get(v_val_3036_, 1);
lean_inc(v_snd_3038_);
lean_dec(v_val_3036_);
v___x_3039_ = lean_box(v_closed_3021_);
v___f_3040_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3040_, 0, v_snd_3038_);
lean_closure_set(v___f_3040_, 1, v_consumers_3017_);
lean_closure_set(v___f_3040_, 2, v_capacity_3018_);
lean_closure_set(v___f_3040_, 3, v_buf_3019_);
lean_closure_set(v___f_3040_, 4, v___x_3033_);
lean_closure_set(v___f_3040_, 5, v_sendIdx_3020_);
lean_closure_set(v___f_3040_, 6, v___y_3031_);
lean_closure_set(v___f_3040_, 7, v___x_3039_);
lean_closure_set(v___f_3040_, 8, v___f_3029_);
lean_closure_set(v___f_3040_, 9, v_a_3022_);
v___x_3041_ = lean_box(v___x_3023_);
v___x_3042_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3042_, 0, lean_box(0));
lean_closure_set(v___x_3042_, 1, v___x_3041_);
lean_closure_set(v___x_3042_, 2, v_fst_3037_);
v___x_3043_ = lean_apply_2(v_inst_3024_, lean_box(0), v___x_3042_);
v___x_3044_ = lean_apply_4(v_toBind_3014_, lean_box(0), lean_box(0), v___x_3043_, v___f_3040_);
return v___x_3044_;
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec(v___x_3035_);
lean_dec(v___x_3033_);
lean_dec(v___y_3031_);
lean_dec_ref(v___f_3029_);
lean_dec(v_inst_3024_);
lean_dec(v_sendIdx_3020_);
lean_dec_ref(v_buf_3019_);
lean_dec(v_capacity_3018_);
lean_dec_ref(v_consumers_3017_);
v___x_3045_ = lean_box(0);
v___x_3046_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3013_, v_toBind_3014_, v___f_3028_, v___x_3045_, v___x_3034_, v_a_3022_);
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3050_, lean_object* v_inst_3051_, lean_object* v_toBind_3052_, lean_object* v_bufCount_3053_, lean_object* v_producers_3054_, lean_object* v_consumers_3055_, lean_object* v_capacity_3056_, lean_object* v_buf_3057_, lean_object* v_sendIdx_3058_, lean_object* v_closed_3059_, lean_object* v_a_3060_, lean_object* v___x_3061_, lean_object* v_inst_3062_, lean_object* v_recvIdx_3063_, lean_object* v___x_3064_, lean_object* v_a_3065_){
_start:
{
uint8_t v_closed_boxed_3066_; uint8_t v___x_735__boxed_3067_; lean_object* v_res_3068_; 
v_closed_boxed_3066_ = lean_unbox(v_closed_3059_);
v___x_735__boxed_3067_ = lean_unbox(v___x_3061_);
v_res_3068_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3050_, v_inst_3051_, v_toBind_3052_, v_bufCount_3053_, v_producers_3054_, v_consumers_3055_, v_capacity_3056_, v_buf_3057_, v_sendIdx_3058_, v_closed_boxed_3066_, v_a_3060_, v___x_735__boxed_3067_, v_inst_3062_, v_recvIdx_3063_, v___x_3064_, v_a_3065_);
lean_dec(v_recvIdx_3063_);
lean_dec(v_bufCount_3053_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3069_, lean_object* v_inst_3070_, lean_object* v_toBind_3071_, lean_object* v_a_3072_, lean_object* v_inst_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_producers_3075_; lean_object* v_consumers_3076_; lean_object* v_capacity_3077_; lean_object* v_buf_3078_; lean_object* v_bufCount_3079_; lean_object* v_sendIdx_3080_; lean_object* v_recvIdx_3081_; uint8_t v_closed_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v_producers_3075_ = lean_ctor_get(v_a_3074_, 0);
lean_inc_ref(v_producers_3075_);
v_consumers_3076_ = lean_ctor_get(v_a_3074_, 1);
lean_inc_ref(v_consumers_3076_);
v_capacity_3077_ = lean_ctor_get(v_a_3074_, 2);
lean_inc(v_capacity_3077_);
v_buf_3078_ = lean_ctor_get(v_a_3074_, 3);
lean_inc_ref(v_buf_3078_);
v_bufCount_3079_ = lean_ctor_get(v_a_3074_, 4);
lean_inc(v_bufCount_3079_);
v_sendIdx_3080_ = lean_ctor_get(v_a_3074_, 5);
lean_inc(v_sendIdx_3080_);
v_recvIdx_3081_ = lean_ctor_get(v_a_3074_, 6);
lean_inc(v_recvIdx_3081_);
v_closed_3082_ = lean_ctor_get_uint8(v_a_3074_, sizeof(void*)*7);
lean_dec_ref(v_a_3074_);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = lean_nat_dec_eq(v_bufCount_3079_, v___x_3083_);
if (v___x_3084_ == 0)
{
uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___f_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3085_ = 1;
v___x_3086_ = lean_box(v_closed_3082_);
v___x_3087_ = lean_box(v___x_3085_);
lean_inc(v_recvIdx_3081_);
lean_inc_ref(v_buf_3078_);
lean_inc(v_toBind_3071_);
lean_inc(v_inst_3070_);
v___f_3088_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3088_, 0, v_toApplicative_3069_);
lean_closure_set(v___f_3088_, 1, v_inst_3070_);
lean_closure_set(v___f_3088_, 2, v_toBind_3071_);
lean_closure_set(v___f_3088_, 3, v_bufCount_3079_);
lean_closure_set(v___f_3088_, 4, v_producers_3075_);
lean_closure_set(v___f_3088_, 5, v_consumers_3076_);
lean_closure_set(v___f_3088_, 6, v_capacity_3077_);
lean_closure_set(v___f_3088_, 7, v_buf_3078_);
lean_closure_set(v___f_3088_, 8, v_sendIdx_3080_);
lean_closure_set(v___f_3088_, 9, v___x_3086_);
lean_closure_set(v___f_3088_, 10, v_a_3072_);
lean_closure_set(v___f_3088_, 11, v___x_3087_);
lean_closure_set(v___f_3088_, 12, v_inst_3073_);
lean_closure_set(v___f_3088_, 13, v_recvIdx_3081_);
lean_closure_set(v___f_3088_, 14, v___x_3083_);
v___x_3089_ = lean_array_fget(v_buf_3078_, v_recvIdx_3081_);
lean_dec(v_recvIdx_3081_);
lean_dec_ref(v_buf_3078_);
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3091_, 0, lean_box(0));
lean_closure_set(v___x_3091_, 1, lean_box(0));
lean_closure_set(v___x_3091_, 2, v___x_3089_);
lean_closure_set(v___x_3091_, 3, v___x_3090_);
v___x_3092_ = lean_apply_2(v_inst_3070_, lean_box(0), v___x_3091_);
v___x_3093_ = lean_apply_4(v_toBind_3071_, lean_box(0), lean_box(0), v___x_3092_, v___f_3088_);
return v___x_3093_;
}
else
{
lean_object* v_toPure_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
lean_dec(v_recvIdx_3081_);
lean_dec(v_sendIdx_3080_);
lean_dec(v_bufCount_3079_);
lean_dec_ref(v_buf_3078_);
lean_dec(v_capacity_3077_);
lean_dec_ref(v_consumers_3076_);
lean_dec_ref(v_producers_3075_);
lean_dec(v_inst_3073_);
lean_dec(v_a_3072_);
lean_dec(v_toBind_3071_);
lean_dec(v_inst_3070_);
v_toPure_3094_ = lean_ctor_get(v_toApplicative_3069_, 1);
lean_inc(v_toPure_3094_);
lean_dec_ref(v_toApplicative_3069_);
v___x_3095_ = lean_box(0);
v___x_3096_ = lean_apply_2(v_toPure_3094_, lean_box(0), v___x_3095_);
return v___x_3096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3097_, lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_toApplicative_3101_; lean_object* v_toBind_3102_; lean_object* v___f_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_toApplicative_3101_ = lean_ctor_get(v_inst_3097_, 0);
lean_inc_ref(v_toApplicative_3101_);
v_toBind_3102_ = lean_ctor_get(v_inst_3097_, 1);
lean_inc(v_toBind_3102_);
lean_dec_ref(v_inst_3097_);
lean_inc(v_a_3100_);
lean_inc(v_toBind_3102_);
lean_inc(v_inst_3098_);
v___f_3103_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4), 6, 5);
lean_closure_set(v___f_3103_, 0, v_toApplicative_3101_);
lean_closure_set(v___f_3103_, 1, v_inst_3098_);
lean_closure_set(v___f_3103_, 2, v_toBind_3102_);
lean_closure_set(v___f_3103_, 3, v_a_3100_);
lean_closure_set(v___f_3103_, 4, v_inst_3099_);
v___x_3104_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3104_, 0, lean_box(0));
lean_closure_set(v___x_3104_, 1, lean_box(0));
lean_closure_set(v___x_3104_, 2, v_a_3100_);
v___x_3105_ = lean_apply_2(v_inst_3098_, lean_box(0), v___x_3104_);
v___x_3106_ = lean_apply_4(v_toBind_3102_, lean_box(0), lean_box(0), v___x_3105_, v___f_3103_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3107_, lean_object* v_00_u03b1_3108_, lean_object* v_inst_3109_, lean_object* v_inst_3110_, lean_object* v_inst_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v___x_3113_; 
v___x_3113_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3109_, v_inst_3110_, v_inst_3111_, v_a_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3114_){
_start:
{
lean_object* v___x_3116_; lean_object* v_producers_3117_; lean_object* v_consumers_3118_; lean_object* v_capacity_3119_; lean_object* v_buf_3120_; lean_object* v_bufCount_3121_; lean_object* v_sendIdx_3122_; lean_object* v_recvIdx_3123_; uint8_t v_closed_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3156_; 
v___x_3116_ = lean_st_ref_get(v_a_3114_);
v_producers_3117_ = lean_ctor_get(v___x_3116_, 0);
v_consumers_3118_ = lean_ctor_get(v___x_3116_, 1);
v_capacity_3119_ = lean_ctor_get(v___x_3116_, 2);
v_buf_3120_ = lean_ctor_get(v___x_3116_, 3);
v_bufCount_3121_ = lean_ctor_get(v___x_3116_, 4);
v_sendIdx_3122_ = lean_ctor_get(v___x_3116_, 5);
v_recvIdx_3123_ = lean_ctor_get(v___x_3116_, 6);
v_closed_3124_ = lean_ctor_get_uint8(v___x_3116_, sizeof(void*)*7);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3126_ = v___x_3116_;
v_isShared_3127_ = v_isSharedCheck_3156_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_recvIdx_3123_);
lean_inc(v_sendIdx_3122_);
lean_inc(v_bufCount_3121_);
lean_inc(v_buf_3120_);
lean_inc(v_capacity_3119_);
lean_inc(v_consumers_3118_);
lean_inc(v_producers_3117_);
lean_dec(v___x_3116_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3156_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = lean_nat_dec_eq(v_bufCount_3121_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_st_3134_; lean_object* v___y_3135_; uint8_t v___x_3137_; lean_object* v___y_3139_; lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3130_ = lean_array_fget_borrowed(v_buf_3120_, v_recvIdx_3123_);
v___x_3131_ = lean_box(0);
v___x_3132_ = lean_st_ref_swap(v___x_3130_, v___x_3131_);
v___x_3137_ = 1;
v___x_3152_ = lean_unsigned_to_nat(1u);
v___x_3153_ = lean_nat_add(v_recvIdx_3123_, v___x_3152_);
lean_dec(v_recvIdx_3123_);
v___x_3154_ = lean_nat_dec_eq(v___x_3153_, v_capacity_3119_);
if (v___x_3154_ == 0)
{
v___y_3139_ = v___x_3153_;
goto v___jp_3138_;
}
else
{
lean_dec(v___x_3153_);
v___y_3139_ = v___x_3128_;
goto v___jp_3138_;
}
v___jp_3133_:
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_st_ref_set(v___y_3135_, v_st_3134_);
return v___x_3132_;
}
v___jp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3140_ = lean_unsigned_to_nat(1u);
v___x_3141_ = lean_nat_sub(v_bufCount_3121_, v___x_3140_);
lean_dec(v_bufCount_3121_);
lean_inc(v___y_3139_);
lean_inc(v_sendIdx_3122_);
lean_inc(v___x_3141_);
lean_inc_ref(v_buf_3120_);
lean_inc(v_capacity_3119_);
lean_inc_ref(v_consumers_3118_);
lean_inc_ref(v_producers_3117_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 6, v___y_3139_);
lean_ctor_set(v___x_3126_, 4, v___x_3141_);
v___x_3143_ = v___x_3126_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_producers_3117_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_consumers_3118_);
lean_ctor_set(v_reuseFailAlloc_3151_, 2, v_capacity_3119_);
lean_ctor_set(v_reuseFailAlloc_3151_, 3, v_buf_3120_);
lean_ctor_set(v_reuseFailAlloc_3151_, 4, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3151_, 5, v_sendIdx_3122_);
lean_ctor_set(v_reuseFailAlloc_3151_, 6, v___y_3139_);
lean_ctor_set_uint8(v_reuseFailAlloc_3151_, sizeof(void*)*7, v_closed_3124_);
v___x_3143_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3117_);
if (lean_obj_tag(v___x_3144_) == 1)
{
lean_object* v_val_3145_; lean_object* v_fst_3146_; lean_object* v_snd_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec_ref(v___x_3143_);
v_val_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_val_3145_);
lean_dec_ref(v___x_3144_);
v_fst_3146_ = lean_ctor_get(v_val_3145_, 0);
lean_inc(v_fst_3146_);
v_snd_3147_ = lean_ctor_get(v_val_3145_, 1);
lean_inc(v_snd_3147_);
lean_dec(v_val_3145_);
v___x_3148_ = lean_box(v___x_3137_);
v___x_3149_ = lean_io_promise_resolve(v___x_3148_, v_fst_3146_);
lean_dec(v_fst_3146_);
v___x_3150_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3150_, 0, v_snd_3147_);
lean_ctor_set(v___x_3150_, 1, v_consumers_3118_);
lean_ctor_set(v___x_3150_, 2, v_capacity_3119_);
lean_ctor_set(v___x_3150_, 3, v_buf_3120_);
lean_ctor_set(v___x_3150_, 4, v___x_3141_);
lean_ctor_set(v___x_3150_, 5, v_sendIdx_3122_);
lean_ctor_set(v___x_3150_, 6, v___y_3139_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*7, v_closed_3124_);
v_st_3134_ = v___x_3150_;
v___y_3135_ = v_a_3114_;
goto v___jp_3133_;
}
else
{
lean_dec(v___x_3144_);
lean_dec(v___x_3141_);
lean_dec(v___y_3139_);
lean_dec(v_sendIdx_3122_);
lean_dec_ref(v_buf_3120_);
lean_dec(v_capacity_3119_);
lean_dec_ref(v_consumers_3118_);
v_st_3134_ = v___x_3143_;
v___y_3135_ = v_a_3114_;
goto v___jp_3133_;
}
}
}
}
else
{
lean_object* v___x_3155_; 
lean_del_object(v___x_3126_);
lean_dec(v_recvIdx_3123_);
lean_dec(v_sendIdx_3122_);
lean_dec(v_bufCount_3121_);
lean_dec_ref(v_buf_3120_);
lean_dec(v_capacity_3119_);
lean_dec_ref(v_consumers_3118_);
lean_dec_ref(v_producers_3117_);
v___x_3155_ = lean_box(0);
return v___x_3155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3157_);
lean_dec(v_a_3157_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3164_, lean_object* v_a_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3164_, v_a_3165_);
lean_dec(v_a_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3169_){
_start:
{
lean_object* v___f_3171_; lean_object* v___x_3172_; 
v___f_3171_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3172_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3169_, v___f_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3173_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3176_, lean_object* v_ch_3177_){
_start:
{
lean_object* v___x_3179_; 
v___x_3179_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3177_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3180_, lean_object* v_ch_3181_, lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3180_, v_ch_3181_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3185_);
if (lean_obj_tag(v___x_3187_) == 1)
{
lean_object* v___x_3188_; 
lean_dec_ref(v___f_3184_);
v___x_3188_ = lean_task_pure(v___x_3187_);
return v___x_3188_;
}
else
{
lean_object* v___x_3189_; uint8_t v_closed_3190_; 
lean_dec(v___x_3187_);
v___x_3189_ = lean_st_ref_get(v___y_3185_);
v_closed_3190_ = lean_ctor_get_uint8(v___x_3189_, sizeof(void*)*7);
lean_dec(v___x_3189_);
if (v_closed_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v_producers_3193_; lean_object* v_consumers_3194_; lean_object* v_capacity_3195_; lean_object* v_buf_3196_; lean_object* v_bufCount_3197_; lean_object* v_sendIdx_3198_; lean_object* v_recvIdx_3199_; uint8_t v_closed_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3214_; 
v___x_3191_ = lean_io_promise_new();
v___x_3192_ = lean_st_ref_take(v___y_3185_);
v_producers_3193_ = lean_ctor_get(v___x_3192_, 0);
v_consumers_3194_ = lean_ctor_get(v___x_3192_, 1);
v_capacity_3195_ = lean_ctor_get(v___x_3192_, 2);
v_buf_3196_ = lean_ctor_get(v___x_3192_, 3);
v_bufCount_3197_ = lean_ctor_get(v___x_3192_, 4);
v_sendIdx_3198_ = lean_ctor_get(v___x_3192_, 5);
v_recvIdx_3199_ = lean_ctor_get(v___x_3192_, 6);
v_closed_3200_ = lean_ctor_get_uint8(v___x_3192_, sizeof(void*)*7);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3202_ = v___x_3192_;
v_isShared_3203_ = v_isSharedCheck_3214_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_recvIdx_3199_);
lean_inc(v_sendIdx_3198_);
lean_inc(v_bufCount_3197_);
lean_inc(v_buf_3196_);
lean_inc(v_capacity_3195_);
lean_inc(v_consumers_3194_);
lean_inc(v_producers_3193_);
lean_dec(v___x_3192_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3214_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3204_ = lean_box(0);
lean_inc(v___x_3191_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3191_);
lean_ctor_set(v___x_3205_, 1, v___x_3204_);
v___x_3206_ = l_Std_Queue_enqueue___redArg(v___x_3205_, v_consumers_3194_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v___x_3206_);
v___x_3208_ = v___x_3202_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_producers_3193_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v_capacity_3195_);
lean_ctor_set(v_reuseFailAlloc_3213_, 3, v_buf_3196_);
lean_ctor_set(v_reuseFailAlloc_3213_, 4, v_bufCount_3197_);
lean_ctor_set(v_reuseFailAlloc_3213_, 5, v_sendIdx_3198_);
lean_ctor_set(v_reuseFailAlloc_3213_, 6, v_recvIdx_3199_);
lean_ctor_set_uint8(v_reuseFailAlloc_3213_, sizeof(void*)*7, v_closed_3200_);
v___x_3208_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3209_ = lean_st_ref_set(v___y_3185_, v___x_3208_);
v___x_3210_ = lean_io_promise_result_opt(v___x_3191_);
lean_dec(v___x_3191_);
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = lean_io_bind_task(v___x_3210_, v___f_3184_, v___x_3211_, v_closed_3190_);
return v___x_3212_;
}
}
}
else
{
lean_object* v___x_3215_; 
lean_dec_ref(v___f_3184_);
v___x_3215_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3216_, v___y_3217_);
lean_dec(v___y_3217_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3220_, lean_object* v_res_3221_){
_start:
{
if (lean_obj_tag(v_res_3221_) == 0)
{
lean_dec_ref(v_ch_3220_);
goto v___jp_3223_;
}
else
{
lean_object* v_val_3225_; uint8_t v___x_3226_; 
v_val_3225_ = lean_ctor_get(v_res_3221_, 0);
v___x_3226_ = lean_unbox(v_val_3225_);
if (v___x_3226_ == 0)
{
lean_dec_ref(v_ch_3220_);
goto v___jp_3223_;
}
else
{
lean_object* v___x_3227_; 
v___x_3227_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3220_);
return v___x_3227_;
}
}
v___jp_3223_:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3228_, lean_object* v_res_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3228_, v_res_3229_);
lean_dec(v_res_3229_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3232_){
_start:
{
lean_object* v___f_3234_; lean_object* v___f_3235_; lean_object* v___x_3236_; 
lean_inc_ref(v_ch_3232_);
v___f_3234_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3234_, 0, v_ch_3232_);
v___f_3235_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3235_, 0, v___f_3234_);
v___x_3236_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3232_, v___f_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3237_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3240_, lean_object* v_ch_3241_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3241_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3244_, lean_object* v_ch_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3244_, v_ch_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3248_, lean_object* v_a_3249_){
_start:
{
uint8_t v___y_3251_; lean_object* v_bufCount_3255_; uint8_t v_closed_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_bufCount_3255_ = lean_ctor_get(v_a_3249_, 4);
v_closed_3256_ = lean_ctor_get_uint8(v_a_3249_, sizeof(void*)*7);
v___x_3257_ = lean_unsigned_to_nat(0u);
v___x_3258_ = lean_nat_dec_eq(v_bufCount_3255_, v___x_3257_);
if (v___x_3258_ == 0)
{
uint8_t v___x_3259_; 
v___x_3259_ = 1;
v___y_3251_ = v___x_3259_;
goto v___jp_3250_;
}
else
{
v___y_3251_ = v_closed_3256_;
goto v___jp_3250_;
}
v___jp_3250_:
{
lean_object* v_toPure_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_toPure_3252_ = lean_ctor_get(v_toApplicative_3248_, 1);
lean_inc(v_toPure_3252_);
lean_dec_ref(v_toApplicative_3248_);
v___x_3253_ = lean_box(v___y_3251_);
v___x_3254_ = lean_apply_2(v_toPure_3252_, lean_box(0), v___x_3253_);
return v___x_3254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3260_, v_a_3261_);
lean_dec_ref(v_a_3261_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_toApplicative_3266_; lean_object* v_toBind_3267_; lean_object* v___f_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_toApplicative_3266_ = lean_ctor_get(v_inst_3263_, 0);
lean_inc_ref(v_toApplicative_3266_);
v_toBind_3267_ = lean_ctor_get(v_inst_3263_, 1);
lean_inc(v_toBind_3267_);
lean_dec_ref(v_inst_3263_);
v___f_3268_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3268_, 0, v_toApplicative_3266_);
v___x_3269_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3269_, 0, lean_box(0));
lean_closure_set(v___x_3269_, 1, lean_box(0));
lean_closure_set(v___x_3269_, 2, v_a_3265_);
v___x_3270_ = lean_apply_2(v_inst_3264_, lean_box(0), v___x_3269_);
v___x_3271_ = lean_apply_4(v_toBind_3267_, lean_box(0), lean_box(0), v___x_3270_, v___f_3268_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3272_, lean_object* v_00_u03b1_3273_, lean_object* v_inst_3274_, lean_object* v_inst_3275_, lean_object* v_a_3276_){
_start:
{
lean_object* v_toApplicative_3277_; lean_object* v_toBind_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_toApplicative_3277_ = lean_ctor_get(v_inst_3274_, 0);
lean_inc_ref(v_toApplicative_3277_);
v_toBind_3278_ = lean_ctor_get(v_inst_3274_, 1);
lean_inc(v_toBind_3278_);
lean_dec_ref(v_inst_3274_);
v___f_3279_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3279_, 0, v_toApplicative_3277_);
v___x_3280_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3280_, 0, lean_box(0));
lean_closure_set(v___x_3280_, 1, lean_box(0));
lean_closure_set(v___x_3280_, 2, v_a_3276_);
v___x_3281_ = lean_apply_2(v_inst_3275_, lean_box(0), v___x_3280_);
v___x_3282_ = lean_apply_4(v_toBind_3278_, lean_box(0), lean_box(0), v___x_3281_, v___f_3279_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3283_){
_start:
{
lean_object* v___x_3285_; lean_object* v_producers_3286_; lean_object* v_consumers_3287_; lean_object* v_capacity_3288_; lean_object* v_buf_3289_; lean_object* v_bufCount_3290_; lean_object* v_sendIdx_3291_; lean_object* v_recvIdx_3292_; uint8_t v_closed_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3327_; 
v___x_3285_ = lean_st_ref_get(v_a_3283_);
v_producers_3286_ = lean_ctor_get(v___x_3285_, 0);
v_consumers_3287_ = lean_ctor_get(v___x_3285_, 1);
v_capacity_3288_ = lean_ctor_get(v___x_3285_, 2);
v_buf_3289_ = lean_ctor_get(v___x_3285_, 3);
v_bufCount_3290_ = lean_ctor_get(v___x_3285_, 4);
v_sendIdx_3291_ = lean_ctor_get(v___x_3285_, 5);
v_recvIdx_3292_ = lean_ctor_get(v___x_3285_, 6);
v_closed_3293_ = lean_ctor_get_uint8(v___x_3285_, sizeof(void*)*7);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3295_ = v___x_3285_;
v_isShared_3296_ = v_isSharedCheck_3327_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_recvIdx_3292_);
lean_inc(v_sendIdx_3291_);
lean_inc(v_bufCount_3290_);
lean_inc(v_buf_3289_);
lean_inc(v_capacity_3288_);
lean_inc(v_consumers_3287_);
lean_inc(v_producers_3286_);
lean_dec(v___x_3285_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3327_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = lean_unsigned_to_nat(0u);
v___x_3298_ = lean_nat_dec_eq(v_bufCount_3290_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v_st_3303_; lean_object* v___y_3304_; uint8_t v___x_3307_; lean_object* v___y_3309_; lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3299_ = lean_array_fget_borrowed(v_buf_3289_, v_recvIdx_3292_);
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_st_ref_swap(v___x_3299_, v___x_3300_);
v___x_3307_ = 1;
v___x_3322_ = lean_unsigned_to_nat(1u);
v___x_3323_ = lean_nat_add(v_recvIdx_3292_, v___x_3322_);
lean_dec(v_recvIdx_3292_);
v___x_3324_ = lean_nat_dec_eq(v___x_3323_, v_capacity_3288_);
if (v___x_3324_ == 0)
{
v___y_3309_ = v___x_3323_;
goto v___jp_3308_;
}
else
{
lean_dec(v___x_3323_);
v___y_3309_ = v___x_3297_;
goto v___jp_3308_;
}
v___jp_3302_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3305_ = lean_st_ref_set(v___y_3304_, v_st_3303_);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3301_);
return v___x_3306_;
}
v___jp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3310_ = lean_unsigned_to_nat(1u);
v___x_3311_ = lean_nat_sub(v_bufCount_3290_, v___x_3310_);
lean_dec(v_bufCount_3290_);
lean_inc(v___y_3309_);
lean_inc(v_sendIdx_3291_);
lean_inc(v___x_3311_);
lean_inc_ref(v_buf_3289_);
lean_inc(v_capacity_3288_);
lean_inc_ref(v_consumers_3287_);
lean_inc_ref(v_producers_3286_);
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 6, v___y_3309_);
lean_ctor_set(v___x_3295_, 4, v___x_3311_);
v___x_3313_ = v___x_3295_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_producers_3286_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_consumers_3287_);
lean_ctor_set(v_reuseFailAlloc_3321_, 2, v_capacity_3288_);
lean_ctor_set(v_reuseFailAlloc_3321_, 3, v_buf_3289_);
lean_ctor_set(v_reuseFailAlloc_3321_, 4, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3321_, 5, v_sendIdx_3291_);
lean_ctor_set(v_reuseFailAlloc_3321_, 6, v___y_3309_);
lean_ctor_set_uint8(v_reuseFailAlloc_3321_, sizeof(void*)*7, v_closed_3293_);
v___x_3313_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3286_);
if (lean_obj_tag(v___x_3314_) == 1)
{
lean_object* v_val_3315_; lean_object* v_fst_3316_; lean_object* v_snd_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec_ref(v___x_3313_);
v_val_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_val_3315_);
lean_dec_ref(v___x_3314_);
v_fst_3316_ = lean_ctor_get(v_val_3315_, 0);
lean_inc(v_fst_3316_);
v_snd_3317_ = lean_ctor_get(v_val_3315_, 1);
lean_inc(v_snd_3317_);
lean_dec(v_val_3315_);
v___x_3318_ = lean_box(v___x_3307_);
v___x_3319_ = lean_io_promise_resolve(v___x_3318_, v_fst_3316_);
lean_dec(v_fst_3316_);
v___x_3320_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3320_, 0, v_snd_3317_);
lean_ctor_set(v___x_3320_, 1, v_consumers_3287_);
lean_ctor_set(v___x_3320_, 2, v_capacity_3288_);
lean_ctor_set(v___x_3320_, 3, v_buf_3289_);
lean_ctor_set(v___x_3320_, 4, v___x_3311_);
lean_ctor_set(v___x_3320_, 5, v_sendIdx_3291_);
lean_ctor_set(v___x_3320_, 6, v___y_3309_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*7, v_closed_3293_);
v_st_3303_ = v___x_3320_;
v___y_3304_ = v_a_3283_;
goto v___jp_3302_;
}
else
{
lean_dec(v___x_3314_);
lean_dec(v___x_3311_);
lean_dec(v___y_3309_);
lean_dec(v_sendIdx_3291_);
lean_dec_ref(v_buf_3289_);
lean_dec(v_capacity_3288_);
lean_dec_ref(v_consumers_3287_);
v_st_3303_ = v___x_3313_;
v___y_3304_ = v_a_3283_;
goto v___jp_3302_;
}
}
}
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_del_object(v___x_3295_);
lean_dec(v_recvIdx_3292_);
lean_dec(v_sendIdx_3291_);
lean_dec(v_bufCount_3290_);
lean_dec_ref(v_buf_3289_);
lean_dec(v_capacity_3288_);
lean_dec_ref(v_consumers_3287_);
lean_dec_ref(v_producers_3286_);
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
return v___x_3326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3328_);
lean_dec(v_a_3328_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3332_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3335_, lean_object* v_a_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3335_, v_a_3336_);
lean_dec(v_a_3336_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3339_, lean_object* v_lose_3340_){
_start:
{
lean_object* v_finished_3342_; lean_object* v_promise_3343_; lean_object* v___x_3344_; uint8_t v___y_3346_; uint8_t v___x_3354_; 
v_finished_3342_ = lean_ctor_get(v_w_3339_, 0);
v_promise_3343_ = lean_ctor_get(v_w_3339_, 1);
v___x_3344_ = lean_st_ref_take(v_finished_3342_);
v___x_3354_ = lean_unbox(v___x_3344_);
lean_dec(v___x_3344_);
if (v___x_3354_ == 0)
{
uint8_t v___x_3355_; 
v___x_3355_ = 1;
v___y_3346_ = v___x_3355_;
goto v___jp_3345_;
}
else
{
uint8_t v___x_3356_; 
v___x_3356_ = 0;
v___y_3346_ = v___x_3356_;
goto v___jp_3345_;
}
v___jp_3345_:
{
uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = 1;
v___x_3348_ = lean_box(v___x_3347_);
v___x_3349_ = lean_st_ref_set(v_finished_3342_, v___x_3348_);
if (v___y_3346_ == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_apply_1(v_lose_3340_, lean_box(0));
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v_lose_3340_);
v___x_3351_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0));
v___x_3352_ = lean_io_promise_resolve(v___x_3351_, v_promise_3343_);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
return v___x_3353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3357_, lean_object* v_lose_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3357_, v_lose_3358_);
lean_dec_ref(v_w_3357_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3361_, lean_object* v_w_3362_, lean_object* v_lose_3363_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3362_, v_lose_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3366_, lean_object* v_w_3367_, lean_object* v_lose_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3366_, v_w_3367_, v_lose_3368_);
lean_dec_ref(v_w_3367_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3371_, lean_object* v_lose_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_finished_3375_; lean_object* v_promise_3376_; lean_object* v___x_3377_; uint8_t v___y_3379_; uint8_t v___x_3395_; 
v_finished_3375_ = lean_ctor_get(v_w_3371_, 0);
v_promise_3376_ = lean_ctor_get(v_w_3371_, 1);
v___x_3377_ = lean_st_ref_take(v_finished_3375_);
v___x_3395_ = lean_unbox(v___x_3377_);
lean_dec(v___x_3377_);
if (v___x_3395_ == 0)
{
uint8_t v___x_3396_; 
v___x_3396_ = 1;
v___y_3379_ = v___x_3396_;
goto v___jp_3378_;
}
else
{
uint8_t v___x_3397_; 
v___x_3397_ = 0;
v___y_3379_ = v___x_3397_;
goto v___jp_3378_;
}
v___jp_3378_:
{
uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3380_ = 1;
v___x_3381_ = lean_box(v___x_3380_);
v___x_3382_ = lean_st_ref_set(v_finished_3375_, v___x_3381_);
if (v___y_3379_ == 0)
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_apply_2(v_lose_3372_, v___y_3373_, lean_box(0));
return v___x_3383_;
}
else
{
lean_object* v___x_3384_; lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v_lose_3372_);
v___x_3384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3373_);
lean_dec(v___y_3373_);
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3394_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3389_, 0, v_a_3385_);
v___x_3390_ = lean_io_promise_resolve(v___x_3389_, v_promise_3376_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 0, v___x_3390_);
v___x_3392_ = v___x_3387_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3398_, lean_object* v_lose_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3398_, v_lose_3399_, v___y_3400_);
lean_dec_ref(v_w_3398_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3403_, lean_object* v_w_3404_, lean_object* v_lose_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3404_, v_lose_3405_, v___y_3406_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3409_, lean_object* v_w_3410_, lean_object* v_lose_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3409_, v_w_3410_, v_lose_3411_, v___y_3412_);
lean_dec_ref(v_w_3410_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3415_, lean_object* v_k_3416_){
_start:
{
lean_object* v_ref_3418_; lean_object* v_mutex_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_ref_3418_ = lean_ctor_get(v_mutex_3415_, 0);
lean_inc(v_ref_3418_);
v_mutex_3419_ = lean_ctor_get(v_mutex_3415_, 1);
lean_inc(v_mutex_3419_);
lean_dec_ref(v_mutex_3415_);
v___x_3420_ = lean_io_basemutex_lock(v_mutex_3419_);
v___x_3421_ = lean_apply_2(v_k_3416_, v_ref_3418_, lean_box(0));
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3430_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3430_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3430_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
v___x_3426_ = lean_io_basemutex_unlock(v_mutex_3419_);
lean_dec(v_mutex_3419_);
if (v_isShared_3425_ == 0)
{
v___x_3428_ = v___x_3424_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3422_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3439_; 
v_a_3431_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3433_ = v___x_3421_;
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3421_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3435_ = lean_io_basemutex_unlock(v_mutex_3419_);
lean_dec(v_mutex_3419_);
if (v_isShared_3434_ == 0)
{
v___x_3437_ = v___x_3433_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3431_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3440_, lean_object* v_k_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3440_, v_k_3441_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3444_, lean_object* v_00_u03b2_3445_, lean_object* v_mutex_3446_, lean_object* v_k_3447_){
_start:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3446_, v_k_3447_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3450_, lean_object* v_00_u03b2_3451_, lean_object* v_mutex_3452_, lean_object* v_k_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3450_, v_00_u03b2_3451_, v_mutex_3452_, v_k_3453_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3459_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v___x_3465_; lean_object* v_producers_3466_; lean_object* v_consumers_3467_; lean_object* v_capacity_3468_; lean_object* v_buf_3469_; lean_object* v_bufCount_3470_; lean_object* v_sendIdx_3471_; lean_object* v_recvIdx_3472_; uint8_t v_closed_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3495_; 
v___x_3465_ = lean_st_ref_get(v___y_3463_);
v_producers_3466_ = lean_ctor_get(v___x_3465_, 0);
v_consumers_3467_ = lean_ctor_get(v___x_3465_, 1);
v_capacity_3468_ = lean_ctor_get(v___x_3465_, 2);
v_buf_3469_ = lean_ctor_get(v___x_3465_, 3);
v_bufCount_3470_ = lean_ctor_get(v___x_3465_, 4);
v_sendIdx_3471_ = lean_ctor_get(v___x_3465_, 5);
v_recvIdx_3472_ = lean_ctor_get(v___x_3465_, 6);
v_closed_3473_ = lean_ctor_get_uint8(v___x_3465_, sizeof(void*)*7);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3475_ = v___x_3465_;
v_isShared_3476_ = v_isSharedCheck_3495_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_recvIdx_3472_);
lean_inc(v_sendIdx_3471_);
lean_inc(v_bufCount_3470_);
lean_inc(v_buf_3469_);
lean_inc(v_capacity_3468_);
lean_inc(v_consumers_3467_);
lean_inc(v_producers_3466_);
lean_dec(v___x_3465_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3495_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3467_);
if (lean_obj_tag(v___x_3477_) == 1)
{
lean_object* v_val_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3492_; 
v_val_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3492_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_val_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3492_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_fst_3482_; lean_object* v_snd_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v_fst_3482_ = lean_ctor_get(v_val_3478_, 0);
lean_inc(v_fst_3482_);
v_snd_3483_ = lean_ctor_get(v_val_3478_, 1);
lean_inc(v_snd_3483_);
lean_dec(v_val_3478_);
v___x_3484_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3482_, v_____do__lift_3462_);
lean_dec(v_fst_3482_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 1, v_snd_3483_);
v___x_3486_ = v___x_3475_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_producers_3466_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_snd_3483_);
lean_ctor_set(v_reuseFailAlloc_3491_, 2, v_capacity_3468_);
lean_ctor_set(v_reuseFailAlloc_3491_, 3, v_buf_3469_);
lean_ctor_set(v_reuseFailAlloc_3491_, 4, v_bufCount_3470_);
lean_ctor_set(v_reuseFailAlloc_3491_, 5, v_sendIdx_3471_);
lean_ctor_set(v_reuseFailAlloc_3491_, 6, v_recvIdx_3472_);
lean_ctor_set_uint8(v_reuseFailAlloc_3491_, sizeof(void*)*7, v_closed_3473_);
v___x_3486_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
v___x_3487_ = lean_st_ref_set(v___y_3463_, v___x_3486_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set_tag(v___x_3480_, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3487_);
v___x_3489_ = v___x_3480_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_dec(v___x_3477_);
lean_del_object(v___x_3475_);
lean_dec(v_recvIdx_3472_);
lean_dec(v_sendIdx_3471_);
lean_dec(v_bufCount_3470_);
lean_dec_ref(v_buf_3469_);
lean_dec(v_capacity_3468_);
lean_dec_ref(v_producers_3466_);
v___x_3493_ = lean_box(0);
v___x_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
return v___x_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
uint8_t v_____do__lift_5609__boxed_3499_; lean_object* v_res_3500_; 
v_____do__lift_5609__boxed_3499_ = lean_unbox(v_____do__lift_3496_);
v_res_3500_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_5609__boxed_3499_, v___y_3497_);
lean_dec(v___y_3497_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3501_, lean_object* v___f_3502_, uint8_t v_____do__lift_3503_, lean_object* v___y_3504_){
_start:
{
if (v_____do__lift_3503_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v_producers_3508_; lean_object* v_consumers_3509_; lean_object* v_capacity_3510_; lean_object* v_buf_3511_; lean_object* v_bufCount_3512_; lean_object* v_sendIdx_3513_; lean_object* v_recvIdx_3514_; uint8_t v_closed_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3529_; 
v___x_3506_ = lean_io_promise_new();
v___x_3507_ = lean_st_ref_take(v___y_3504_);
v_producers_3508_ = lean_ctor_get(v___x_3507_, 0);
v_consumers_3509_ = lean_ctor_get(v___x_3507_, 1);
v_capacity_3510_ = lean_ctor_get(v___x_3507_, 2);
v_buf_3511_ = lean_ctor_get(v___x_3507_, 3);
v_bufCount_3512_ = lean_ctor_get(v___x_3507_, 4);
v_sendIdx_3513_ = lean_ctor_get(v___x_3507_, 5);
v_recvIdx_3514_ = lean_ctor_get(v___x_3507_, 6);
v_closed_3515_ = lean_ctor_get_uint8(v___x_3507_, sizeof(void*)*7);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3517_ = v___x_3507_;
v_isShared_3518_ = v_isSharedCheck_3529_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_recvIdx_3514_);
lean_inc(v_sendIdx_3513_);
lean_inc(v_bufCount_3512_);
lean_inc(v_buf_3511_);
lean_inc(v_capacity_3510_);
lean_inc(v_consumers_3509_);
lean_inc(v_producers_3508_);
lean_dec(v___x_3507_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3529_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v_waiter_3501_);
lean_inc(v___x_3506_);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3506_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = l_Std_Queue_enqueue___redArg(v___x_3520_, v_consumers_3509_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 1, v___x_3521_);
v___x_3523_ = v___x_3517_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_producers_3508_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v_capacity_3510_);
lean_ctor_set(v_reuseFailAlloc_3528_, 3, v_buf_3511_);
lean_ctor_set(v_reuseFailAlloc_3528_, 4, v_bufCount_3512_);
lean_ctor_set(v_reuseFailAlloc_3528_, 5, v_sendIdx_3513_);
lean_ctor_set(v_reuseFailAlloc_3528_, 6, v_recvIdx_3514_);
lean_ctor_set_uint8(v_reuseFailAlloc_3528_, sizeof(void*)*7, v_closed_3515_);
v___x_3523_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3524_ = lean_st_ref_set(v___y_3504_, v___x_3523_);
lean_dec(v___y_3504_);
v___x_3525_ = lean_io_promise_result_opt(v___x_3506_);
lean_dec(v___x_3506_);
v___x_3526_ = lean_unsigned_to_nat(0u);
v___x_3527_ = l_EIO_chainTask___redArg(v___x_3525_, v___f_3502_, v___x_3526_, v_____do__lift_3503_);
return v___x_3527_;
}
}
}
else
{
lean_object* v___x_3530_; lean_object* v_lose_3531_; lean_object* v___x_3532_; 
lean_dec_ref(v___f_3502_);
v___x_3530_ = lean_box(v_____do__lift_3503_);
v_lose_3531_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3531_, 0, v___x_3530_);
v___x_3532_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3501_, v_lose_3531_, v___y_3504_);
lean_dec_ref(v_waiter_3501_);
return v___x_3532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3533_, lean_object* v___f_3534_, lean_object* v_____do__lift_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
uint8_t v_____do__lift_5665__boxed_3538_; lean_object* v_res_3539_; 
v_____do__lift_5665__boxed_3538_ = lean_unbox(v_____do__lift_3535_);
v_res_3539_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3533_, v___f_3534_, v_____do__lift_5665__boxed_3538_, v___y_3536_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3543_; lean_object* v_bufCount_3544_; uint8_t v_closed_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v___x_3543_ = lean_st_ref_get(v___y_3541_);
v_bufCount_3544_ = lean_ctor_get(v___x_3543_, 4);
lean_inc(v_bufCount_3544_);
v_closed_3545_ = lean_ctor_get_uint8(v___x_3543_, sizeof(void*)*7);
lean_dec(v___x_3543_);
v___x_3546_ = lean_unsigned_to_nat(0u);
v___x_3547_ = lean_nat_dec_eq(v_bufCount_3544_, v___x_3546_);
lean_dec(v_bufCount_3544_);
if (v___x_3547_ == 0)
{
uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = 1;
v___x_3549_ = lean_box(v___x_3548_);
v___x_3550_ = lean_apply_3(v___f_3540_, v___x_3549_, v___y_3541_, lean_box(0));
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = lean_box(v_closed_3545_);
v___x_3552_ = lean_apply_3(v___f_3540_, v___x_3551_, v___y_3541_, lean_box(0));
return v___x_3552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3553_, v___y_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3559_, lean_object* v_ch_3560_, lean_object* v_x_3561_){
_start:
{
if (lean_obj_tag(v_x_3561_) == 0)
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
lean_dec_ref(v_ch_3560_);
lean_dec_ref(v_waiter_3559_);
v___x_3563_ = lean_box(0);
v___x_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
return v___x_3564_;
}
else
{
lean_object* v_val_3565_; uint8_t v___x_3566_; 
v_val_3565_ = lean_ctor_get(v_x_3561_, 0);
v___x_3566_ = lean_unbox(v_val_3565_);
if (v___x_3566_ == 0)
{
lean_object* v___f_3567_; lean_object* v___x_3568_; 
lean_dec_ref(v_ch_3560_);
v___f_3567_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3568_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3559_, v___f_3567_);
lean_dec_ref(v_waiter_3559_);
return v___x_3568_;
}
else
{
lean_object* v___x_3569_; 
v___x_3569_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3560_, v_waiter_3559_);
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3570_, lean_object* v_ch_3571_, lean_object* v_x_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3570_, v_ch_3571_, v_x_3572_);
lean_dec(v_x_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3575_, lean_object* v_waiter_3576_){
_start:
{
lean_object* v___f_3578_; lean_object* v___f_3579_; lean_object* v___f_3580_; lean_object* v___x_3581_; 
lean_inc_ref(v_ch_3575_);
lean_inc_ref(v_waiter_3576_);
v___f_3578_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3578_, 0, v_waiter_3576_);
lean_closure_set(v___f_3578_, 1, v_ch_3575_);
v___f_3579_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3579_, 0, v_waiter_3576_);
lean_closure_set(v___f_3579_, 1, v___f_3578_);
v___f_3580_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3580_, 0, v___f_3579_);
v___x_3581_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3575_, v___f_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3582_, lean_object* v_waiter_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3582_, v_waiter_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3586_, lean_object* v_ch_3587_, lean_object* v_waiter_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3587_, v_waiter_3588_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3591_, lean_object* v_ch_3592_, lean_object* v_waiter_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3591_, v_ch_3592_, v_waiter_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
if (lean_obj_tag(v_x_3597_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3607_; 
lean_dec_ref(v_x_3596_);
v_a_3599_ = lean_ctor_get(v_x_3597_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_x_3597_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3601_ = v_x_3597_;
v_isShared_3602_ = v_isSharedCheck_3607_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v_x_3597_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3607_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
return v___x_3605_;
}
}
}
else
{
lean_object* v___x_3608_; 
lean_dec_ref(v_x_3597_);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v_x_3596_);
return v___x_3608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3609_, lean_object* v_x_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3609_, v_x_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3613_, uint8_t v___x_3614_, lean_object* v___f_3615_, lean_object* v_____r_3616_, lean_object* v_st_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3620_ = lean_st_ref_set(v___y_3618_, v_st_3617_);
v___x_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
v___x_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
v___x_3623_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3613_, v___x_3614_, v___x_3622_, v___f_3615_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3624_, lean_object* v___x_3625_, lean_object* v___f_3626_, lean_object* v_____r_3627_, lean_object* v_st_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
uint8_t v___x_6270__boxed_3631_; lean_object* v_res_3632_; 
v___x_6270__boxed_3631_ = lean_unbox(v___x_3625_);
v_res_3632_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3624_, v___x_6270__boxed_3631_, v___f_3626_, v_____r_3627_, v_st_3628_, v___y_3629_);
lean_dec(v___y_3629_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3633_, lean_object* v_consumers_3634_, lean_object* v_capacity_3635_, lean_object* v_buf_3636_, lean_object* v___x_3637_, lean_object* v_sendIdx_3638_, lean_object* v___y_3639_, uint8_t v_closed_3640_, lean_object* v___f_3641_, lean_object* v_a_3642_, lean_object* v_x_3643_){
_start:
{
if (lean_obj_tag(v_x_3643_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3653_; 
lean_dec(v_a_3642_);
lean_dec_ref(v___f_3641_);
lean_dec(v___y_3639_);
lean_dec(v_sendIdx_3638_);
lean_dec(v___x_3637_);
lean_dec_ref(v_buf_3636_);
lean_dec(v_capacity_3635_);
lean_dec_ref(v_consumers_3634_);
lean_dec_ref(v_snd_3633_);
v_a_3645_ = lean_ctor_get(v_x_3643_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_x_3643_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3647_ = v_x_3643_;
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v_x_3643_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
return v___x_3651_;
}
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
lean_dec_ref(v_x_3643_);
v___x_3654_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3654_, 0, v_snd_3633_);
lean_ctor_set(v___x_3654_, 1, v_consumers_3634_);
lean_ctor_set(v___x_3654_, 2, v_capacity_3635_);
lean_ctor_set(v___x_3654_, 3, v_buf_3636_);
lean_ctor_set(v___x_3654_, 4, v___x_3637_);
lean_ctor_set(v___x_3654_, 5, v_sendIdx_3638_);
lean_ctor_set(v___x_3654_, 6, v___y_3639_);
lean_ctor_set_uint8(v___x_3654_, sizeof(void*)*7, v_closed_3640_);
v___x_3655_ = lean_box(0);
v___x_3656_ = lean_apply_4(v___f_3641_, v___x_3655_, v___x_3654_, v_a_3642_, lean_box(0));
return v___x_3656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3657_, lean_object* v_consumers_3658_, lean_object* v_capacity_3659_, lean_object* v_buf_3660_, lean_object* v___x_3661_, lean_object* v_sendIdx_3662_, lean_object* v___y_3663_, lean_object* v_closed_3664_, lean_object* v___f_3665_, lean_object* v_a_3666_, lean_object* v_x_3667_, lean_object* v___y_3668_){
_start:
{
uint8_t v_closed_boxed_3669_; lean_object* v_res_3670_; 
v_closed_boxed_3669_ = lean_unbox(v_closed_3664_);
v_res_3670_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3657_, v_consumers_3658_, v_capacity_3659_, v_buf_3660_, v___x_3661_, v_sendIdx_3662_, v___y_3663_, v_closed_boxed_3669_, v___f_3665_, v_a_3666_, v_x_3667_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3671_, uint8_t v___x_3672_, lean_object* v_bufCount_3673_, lean_object* v_producers_3674_, lean_object* v_consumers_3675_, lean_object* v_capacity_3676_, lean_object* v_buf_3677_, lean_object* v_sendIdx_3678_, uint8_t v_closed_3679_, uint8_t v___x_3680_, lean_object* v_a_3681_, lean_object* v_recvIdx_3682_, lean_object* v_x_3683_){
_start:
{
if (lean_obj_tag(v_x_3683_) == 0)
{
lean_object* v___x_3685_; 
lean_dec(v_a_3681_);
lean_dec(v_sendIdx_3678_);
lean_dec_ref(v_buf_3677_);
lean_dec(v_capacity_3676_);
lean_dec_ref(v_consumers_3675_);
lean_dec_ref(v_producers_3674_);
lean_dec(v___x_3671_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_x_3683_);
return v___x_3685_;
}
else
{
lean_object* v___f_3686_; lean_object* v___x_3687_; lean_object* v___f_3688_; lean_object* v___y_3690_; lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___f_3686_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3686_, 0, v_x_3683_);
v___x_3687_ = lean_box(v___x_3672_);
lean_inc_ref(v___f_3686_);
lean_inc(v___x_3671_);
v___f_3688_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3688_, 0, v___x_3671_);
lean_closure_set(v___f_3688_, 1, v___x_3687_);
lean_closure_set(v___f_3688_, 2, v___f_3686_);
v___x_3713_ = lean_unsigned_to_nat(1u);
v___x_3714_ = lean_nat_add(v_recvIdx_3682_, v___x_3713_);
v___x_3715_ = lean_nat_dec_eq(v___x_3714_, v_capacity_3676_);
if (v___x_3715_ == 0)
{
v___y_3690_ = v___x_3714_;
goto v___jp_3689_;
}
else
{
lean_dec(v___x_3714_);
lean_inc(v___x_3671_);
v___y_3690_ = v___x_3671_;
goto v___jp_3689_;
}
v___jp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3691_ = lean_unsigned_to_nat(1u);
v___x_3692_ = lean_nat_sub(v_bufCount_3673_, v___x_3691_);
lean_inc(v___y_3690_);
lean_inc(v_sendIdx_3678_);
lean_inc(v___x_3692_);
lean_inc_ref(v_buf_3677_);
lean_inc(v_capacity_3676_);
lean_inc_ref(v_consumers_3675_);
lean_inc_ref(v_producers_3674_);
v___x_3693_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3693_, 0, v_producers_3674_);
lean_ctor_set(v___x_3693_, 1, v_consumers_3675_);
lean_ctor_set(v___x_3693_, 2, v_capacity_3676_);
lean_ctor_set(v___x_3693_, 3, v_buf_3677_);
lean_ctor_set(v___x_3693_, 4, v___x_3692_);
lean_ctor_set(v___x_3693_, 5, v_sendIdx_3678_);
lean_ctor_set(v___x_3693_, 6, v___y_3690_);
lean_ctor_set_uint8(v___x_3693_, sizeof(void*)*7, v_closed_3679_);
v___x_3694_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3674_);
if (lean_obj_tag(v___x_3694_) == 1)
{
lean_object* v_val_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v___x_3693_);
lean_dec_ref(v___f_3686_);
v_val_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3710_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_val_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3710_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v_fst_3699_; lean_object* v_snd_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___f_3704_; lean_object* v___x_3706_; 
v_fst_3699_ = lean_ctor_get(v_val_3695_, 0);
lean_inc(v_fst_3699_);
v_snd_3700_ = lean_ctor_get(v_val_3695_, 1);
lean_inc(v_snd_3700_);
lean_dec(v_val_3695_);
v___x_3701_ = lean_box(v___x_3680_);
v___x_3702_ = lean_io_promise_resolve(v___x_3701_, v_fst_3699_);
lean_dec(v_fst_3699_);
v___x_3703_ = lean_box(v_closed_3679_);
v___f_3704_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3704_, 0, v_snd_3700_);
lean_closure_set(v___f_3704_, 1, v_consumers_3675_);
lean_closure_set(v___f_3704_, 2, v_capacity_3676_);
lean_closure_set(v___f_3704_, 3, v_buf_3677_);
lean_closure_set(v___f_3704_, 4, v___x_3692_);
lean_closure_set(v___f_3704_, 5, v_sendIdx_3678_);
lean_closure_set(v___f_3704_, 6, v___y_3690_);
lean_closure_set(v___f_3704_, 7, v___x_3703_);
lean_closure_set(v___f_3704_, 8, v___f_3688_);
lean_closure_set(v___f_3704_, 9, v_a_3681_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3702_);
v___x_3706_ = v___x_3697_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3702_);
v___x_3706_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
v___x_3708_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3671_, v___x_3672_, v___x_3707_, v___f_3704_);
return v___x_3708_;
}
}
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_dec(v___x_3694_);
lean_dec(v___x_3692_);
lean_dec(v___y_3690_);
lean_dec_ref(v___f_3688_);
lean_dec(v_sendIdx_3678_);
lean_dec_ref(v_buf_3677_);
lean_dec(v_capacity_3676_);
lean_dec_ref(v_consumers_3675_);
v___x_3711_ = lean_box(0);
v___x_3712_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3671_, v___x_3672_, v___f_3686_, v___x_3711_, v___x_3693_, v_a_3681_);
lean_dec(v_a_3681_);
return v___x_3712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3716_, lean_object* v___x_3717_, lean_object* v_bufCount_3718_, lean_object* v_producers_3719_, lean_object* v_consumers_3720_, lean_object* v_capacity_3721_, lean_object* v_buf_3722_, lean_object* v_sendIdx_3723_, lean_object* v_closed_3724_, lean_object* v___x_3725_, lean_object* v_a_3726_, lean_object* v_recvIdx_3727_, lean_object* v_x_3728_, lean_object* v___y_3729_){
_start:
{
uint8_t v___x_6342__boxed_3730_; uint8_t v_closed_boxed_3731_; uint8_t v___x_6343__boxed_3732_; lean_object* v_res_3733_; 
v___x_6342__boxed_3730_ = lean_unbox(v___x_3717_);
v_closed_boxed_3731_ = lean_unbox(v_closed_3724_);
v___x_6343__boxed_3732_ = lean_unbox(v___x_3725_);
v_res_3733_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3716_, v___x_6342__boxed_3730_, v_bufCount_3718_, v_producers_3719_, v_consumers_3720_, v_capacity_3721_, v_buf_3722_, v_sendIdx_3723_, v_closed_boxed_3731_, v___x_6343__boxed_3732_, v_a_3726_, v_recvIdx_3727_, v_x_3728_);
lean_dec(v_recvIdx_3727_);
lean_dec(v_bufCount_3718_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3734_, lean_object* v_x_3735_){
_start:
{
if (lean_obj_tag(v_x_3735_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3734_);
v_a_3737_ = lean_ctor_get(v_x_3735_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_x_3735_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3739_ = v_x_3735_;
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v_x_3735_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3745_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
return v___x_3743_;
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3774_; 
v_a_3746_ = lean_ctor_get(v_x_3735_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_x_3735_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3748_ = v_x_3735_;
v_isShared_3749_ = v_isSharedCheck_3774_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v_x_3735_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3774_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v_producers_3750_; lean_object* v_consumers_3751_; lean_object* v_capacity_3752_; lean_object* v_buf_3753_; lean_object* v_bufCount_3754_; lean_object* v_sendIdx_3755_; lean_object* v_recvIdx_3756_; uint8_t v_closed_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v_producers_3750_ = lean_ctor_get(v_a_3746_, 0);
lean_inc_ref(v_producers_3750_);
v_consumers_3751_ = lean_ctor_get(v_a_3746_, 1);
lean_inc_ref(v_consumers_3751_);
v_capacity_3752_ = lean_ctor_get(v_a_3746_, 2);
lean_inc(v_capacity_3752_);
v_buf_3753_ = lean_ctor_get(v_a_3746_, 3);
lean_inc_ref(v_buf_3753_);
v_bufCount_3754_ = lean_ctor_get(v_a_3746_, 4);
lean_inc(v_bufCount_3754_);
v_sendIdx_3755_ = lean_ctor_get(v_a_3746_, 5);
lean_inc(v_sendIdx_3755_);
v_recvIdx_3756_ = lean_ctor_get(v_a_3746_, 6);
lean_inc(v_recvIdx_3756_);
v_closed_3757_ = lean_ctor_get_uint8(v_a_3746_, sizeof(void*)*7);
lean_dec(v_a_3746_);
v___x_3758_ = lean_unsigned_to_nat(0u);
v___x_3759_ = lean_nat_dec_eq(v_bufCount_3754_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___f_3767_; lean_object* v___x_3769_; 
v___x_3760_ = lean_array_fget_borrowed(v_buf_3753_, v_recvIdx_3756_);
v___x_3761_ = lean_box(0);
v___x_3762_ = lean_st_ref_swap(v___x_3760_, v___x_3761_);
v___x_3763_ = 1;
v___x_3764_ = lean_box(v___x_3759_);
v___x_3765_ = lean_box(v_closed_3757_);
v___x_3766_ = lean_box(v___x_3763_);
v___f_3767_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3767_, 0, v___x_3758_);
lean_closure_set(v___f_3767_, 1, v___x_3764_);
lean_closure_set(v___f_3767_, 2, v_bufCount_3754_);
lean_closure_set(v___f_3767_, 3, v_producers_3750_);
lean_closure_set(v___f_3767_, 4, v_consumers_3751_);
lean_closure_set(v___f_3767_, 5, v_capacity_3752_);
lean_closure_set(v___f_3767_, 6, v_buf_3753_);
lean_closure_set(v___f_3767_, 7, v_sendIdx_3755_);
lean_closure_set(v___f_3767_, 8, v___x_3765_);
lean_closure_set(v___f_3767_, 9, v___x_3766_);
lean_closure_set(v___f_3767_, 10, v_a_3734_);
lean_closure_set(v___f_3767_, 11, v_recvIdx_3756_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3762_);
v___x_3769_ = v___x_3748_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3762_);
v___x_3769_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
v___x_3771_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3758_, v___x_3759_, v___x_3770_, v___f_3767_);
return v___x_3771_;
}
}
else
{
lean_object* v___x_3773_; 
lean_dec(v_recvIdx_3756_);
lean_dec(v_sendIdx_3755_);
lean_dec(v_bufCount_3754_);
lean_dec_ref(v_buf_3753_);
lean_dec(v_capacity_3752_);
lean_dec_ref(v_consumers_3751_);
lean_dec_ref(v_producers_3750_);
lean_del_object(v___x_3748_);
lean_dec(v_a_3734_);
v___x_3773_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_3773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3775_, lean_object* v_x_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3775_, v_x_3776_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3779_){
_start:
{
lean_object* v___x_3781_; lean_object* v___f_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; lean_object* v___x_3787_; 
v___x_3781_ = lean_st_ref_get(v_a_3779_);
v___f_3782_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3782_, 0, v_a_3779_);
v___x_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = 0;
v___x_3787_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3785_, v___x_3786_, v___x_3784_, v___f_3782_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3788_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3795_, lean_object* v_a_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3795_, v_a_3796_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3799_, lean_object* v_x_3800_){
_start:
{
lean_object* v_val_3803_; lean_object* v___x_3805_; 
v___x_3805_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3799_, v_x_3800_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3805_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set_tag(v___x_3808_, 1);
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
v_val_3803_ = v___x_3811_;
goto v___jp_3802_;
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
v_a_3814_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3805_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3805_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
lean_ctor_set_tag(v___x_3816_, 0);
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
v_val_3803_ = v___x_3819_;
goto v___jp_3802_;
}
}
}
v___jp_3802_:
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v_val_3803_);
return v___x_3804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3822_, lean_object* v_x_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3822_, v_x_3823_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v_x_3826_){
_start:
{
uint8_t v___y_3829_; 
if (lean_obj_tag(v_x_3826_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3841_; 
v_a_3833_ = lean_ctor_get(v_x_3826_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_x_3826_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3835_ = v_x_3826_;
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v_x_3826_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3838_);
return v___x_3839_;
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v_bufCount_3843_; uint8_t v_closed_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_a_3842_ = lean_ctor_get(v_x_3826_, 0);
lean_inc(v_a_3842_);
lean_dec_ref(v_x_3826_);
v_bufCount_3843_ = lean_ctor_get(v_a_3842_, 4);
lean_inc(v_bufCount_3843_);
v_closed_3844_ = lean_ctor_get_uint8(v_a_3842_, sizeof(void*)*7);
lean_dec(v_a_3842_);
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = lean_nat_dec_eq(v_bufCount_3843_, v___x_3845_);
lean_dec(v_bufCount_3843_);
if (v___x_3846_ == 0)
{
uint8_t v___x_3847_; 
v___x_3847_ = 1;
v___y_3829_ = v___x_3847_;
goto v___jp_3828_;
}
else
{
v___y_3829_ = v_closed_3844_;
goto v___jp_3828_;
}
}
v___jp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3830_ = lean_box(v___y_3829_);
v___x_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
v___x_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
return v___x_3832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v_x_3848_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___y_3851_, lean_object* v___f_3852_, lean_object* v_x_3853_){
_start:
{
if (lean_obj_tag(v_x_3853_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v___f_3852_);
lean_dec(v___y_3851_);
v_a_3855_ = lean_ctor_get(v_x_3853_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_x_3853_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3857_ = v_x_3853_;
v_isShared_3858_ = v_isSharedCheck_3863_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v_x_3853_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3863_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
return v___x_3861_;
}
}
}
else
{
lean_object* v_a_3864_; uint8_t v___x_3865_; 
v_a_3864_ = lean_ctor_get(v_x_3853_, 0);
lean_inc(v_a_3864_);
lean_dec_ref(v_x_3853_);
v___x_3865_ = lean_unbox(v_a_3864_);
lean_dec(v_a_3864_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; 
lean_dec_ref(v___f_3852_);
lean_dec(v___y_3851_);
v___x_3866_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3866_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; lean_object* v___x_3870_; 
v___x_3867_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3851_);
v___x_3868_ = lean_unsigned_to_nat(0u);
v___x_3869_ = 0;
v___x_3870_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3868_, v___x_3869_, v___x_3867_, v___f_3852_);
return v___x_3870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___y_3871_, lean_object* v___f_3872_, lean_object* v_x_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___y_3871_, v___f_3872_, v_x_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3876_, lean_object* v___f_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; uint8_t v___x_3884_; lean_object* v___x_3885_; lean_object* v___f_3886_; lean_object* v___x_3887_; 
v___x_3880_ = lean_st_ref_get(v___y_3878_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = 0;
v___x_3885_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3883_, v___x_3884_, v___x_3882_, v___f_3876_);
v___f_3886_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3886_, 0, v___y_3878_);
lean_closure_set(v___f_3886_, 1, v___f_3877_);
v___x_3887_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3883_, v___x_3884_, v___x_3885_, v___f_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3888_, lean_object* v___f_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3888_, v___f_3889_, v___y_3890_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3893_, lean_object* v_capacity_3894_, lean_object* v_buf_3895_, lean_object* v_bufCount_3896_, lean_object* v_sendIdx_3897_, lean_object* v_recvIdx_3898_, uint8_t v_closed_3899_, lean_object* v___y_3900_, lean_object* v_x_3901_){
_start:
{
if (lean_obj_tag(v_x_3901_) == 0)
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3911_; 
lean_dec(v_recvIdx_3898_);
lean_dec(v_sendIdx_3897_);
lean_dec(v_bufCount_3896_);
lean_dec_ref(v_buf_3895_);
lean_dec(v_capacity_3894_);
lean_dec_ref(v_producers_3893_);
v_a_3903_ = lean_ctor_get(v_x_3901_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_x_3901_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3905_ = v_x_3901_;
v_isShared_3906_ = v_isSharedCheck_3911_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v_x_3901_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3911_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; 
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3922_; 
v_a_3912_ = lean_ctor_get(v_x_3901_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_x_3901_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3914_ = v_x_3901_;
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v_x_3901_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3916_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3916_, 0, v_producers_3893_);
lean_ctor_set(v___x_3916_, 1, v_a_3912_);
lean_ctor_set(v___x_3916_, 2, v_capacity_3894_);
lean_ctor_set(v___x_3916_, 3, v_buf_3895_);
lean_ctor_set(v___x_3916_, 4, v_bufCount_3896_);
lean_ctor_set(v___x_3916_, 5, v_sendIdx_3897_);
lean_ctor_set(v___x_3916_, 6, v_recvIdx_3898_);
lean_ctor_set_uint8(v___x_3916_, sizeof(void*)*7, v_closed_3899_);
v___x_3917_ = lean_st_ref_set(v___y_3900_, v___x_3916_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v___x_3917_);
v___x_3919_ = v___x_3914_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3917_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_3923_, lean_object* v_capacity_3924_, lean_object* v_buf_3925_, lean_object* v_bufCount_3926_, lean_object* v_sendIdx_3927_, lean_object* v_recvIdx_3928_, lean_object* v_closed_3929_, lean_object* v___y_3930_, lean_object* v_x_3931_, lean_object* v___y_3932_){
_start:
{
uint8_t v_closed_boxed_3933_; lean_object* v_res_3934_; 
v_closed_boxed_3933_ = lean_unbox(v_closed_3929_);
v_res_3934_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_3923_, v_capacity_3924_, v_buf_3925_, v_bufCount_3926_, v_sendIdx_3927_, v_recvIdx_3928_, v_closed_boxed_3933_, v___y_3930_, v_x_3931_);
lean_dec(v___y_3930_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_3935_, lean_object* v_x_3936_, lean_object* v_head_3937_, lean_object* v_x_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_3935_, v_x_3936_, v_head_3937_, v_x_3938_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_3941_, lean_object* v_x_3942_){
_start:
{
if (lean_obj_tag(v_x_3941_) == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3944_, 0, v_x_3942_);
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
return v___x_3945_;
}
else
{
lean_object* v_head_3946_; lean_object* v_tail_3947_; lean_object* v_waiter_3948_; lean_object* v___f_3949_; lean_object* v_val_3951_; 
v_head_3946_ = lean_ctor_get(v_x_3941_, 0);
lean_inc(v_head_3946_);
v_tail_3947_ = lean_ctor_get(v_x_3941_, 1);
lean_inc(v_tail_3947_);
lean_dec_ref(v_x_3941_);
v_waiter_3948_ = lean_ctor_get(v_head_3946_, 1);
lean_inc(v_waiter_3948_);
v___f_3949_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3949_, 0, v_tail_3947_);
lean_closure_set(v___f_3949_, 1, v_x_3942_);
lean_closure_set(v___f_3949_, 2, v_head_3946_);
if (lean_obj_tag(v_waiter_3948_) == 0)
{
lean_object* v___x_3955_; 
v___x_3955_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_3951_ = v___x_3955_;
goto v___jp_3950_;
}
else
{
lean_object* v_val_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3970_; 
v_val_3956_ = lean_ctor_get(v_waiter_3948_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_waiter_3948_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3958_ = v_waiter_3948_;
v_isShared_3959_ = v_isSharedCheck_3970_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_val_3956_);
lean_dec(v_waiter_3948_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3970_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v_finished_3960_; lean_object* v___x_3961_; lean_object* v___f_3962_; lean_object* v___x_3964_; 
v_finished_3960_ = lean_ctor_get(v_val_3956_, 0);
lean_inc(v_finished_3960_);
lean_dec(v_val_3956_);
v___x_3961_ = lean_st_ref_get(v_finished_3960_);
lean_dec(v_finished_3960_);
v___f_3962_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3961_);
v___x_3964_ = v___x_3958_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3961_);
v___x_3964_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
v___x_3966_ = lean_unsigned_to_nat(0u);
v___x_3967_ = 0;
v___x_3968_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3966_, v___x_3967_, v___x_3965_, v___f_3962_);
v_val_3951_ = v___x_3968_;
goto v___jp_3950_;
}
}
}
v___jp_3950_:
{
lean_object* v___x_3952_; uint8_t v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = lean_unsigned_to_nat(0u);
v___x_3953_ = 0;
v___x_3954_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3952_, v___x_3953_, v_val_3951_, v___f_3949_);
return v___x_3954_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_3971_, lean_object* v_x_3972_, lean_object* v_head_3973_, lean_object* v_x_3974_){
_start:
{
if (lean_obj_tag(v_x_3974_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v_head_3973_);
lean_dec(v_x_3972_);
lean_dec(v_tail_3971_);
v_a_3976_ = lean_ctor_get(v_x_3974_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_x_3974_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3978_ = v_x_3974_;
v_isShared_3979_ = v_isSharedCheck_3984_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v_x_3974_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3984_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3982_; 
v___x_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
return v___x_3982_;
}
}
}
else
{
lean_object* v_a_3985_; uint8_t v___x_3986_; 
v_a_3985_ = lean_ctor_get(v_x_3974_, 0);
lean_inc(v_a_3985_);
lean_dec_ref(v_x_3974_);
v___x_3986_ = lean_unbox(v_a_3985_);
lean_dec(v_a_3985_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; 
lean_dec_ref(v_head_3973_);
v___x_3987_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_3971_, v_x_3972_);
return v___x_3987_;
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3988_, 0, v_head_3973_);
lean_ctor_set(v___x_3988_, 1, v_x_3972_);
v___x_3989_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_3971_, v___x_3988_);
return v___x_3989_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_3990_, lean_object* v_x_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_3990_, v_x_3991_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_3994_){
_start:
{
if (lean_obj_tag(v_x_3994_) == 0)
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3996_, 0, v_x_3994_);
return v___x_3996_;
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4006_; 
v_a_3997_ = lean_ctor_get(v_x_3994_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_x_3994_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3999_ = v_x_3994_;
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v_x_3994_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_4001_ = l_List_reverse___redArg(v_a_3997_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4001_);
v___x_4003_ = v___x_3999_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4001_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4007_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4010_, lean_object* v___x_4011_, lean_object* v_x_4012_){
_start:
{
if (lean_obj_tag(v_x_4012_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v___x_4011_);
lean_dec(v_a_4010_);
v_a_4014_ = lean_ctor_get(v_x_4012_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v_x_4012_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4016_ = v_x_4012_;
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v_x_4012_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4022_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
lean_object* v___x_4020_; 
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
return v___x_4020_;
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4039_; 
v_a_4023_ = lean_ctor_get(v_x_4012_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_x_4012_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4025_ = v_x_4012_;
v_isShared_4026_ = v_isSharedCheck_4039_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v_x_4012_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4039_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
uint8_t v___x_4027_; 
v___x_4027_ = l_List_isEmpty___redArg(v_a_4010_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
lean_dec(v___x_4011_);
v___x_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4028_, 0, v_a_4023_);
lean_ctor_set(v___x_4028_, 1, v_a_4010_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4028_);
v___x_4030_ = v___x_4025_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
return v___x_4031_;
}
}
else
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
lean_dec(v_a_4010_);
v___x_4033_ = l_List_reverse___redArg(v_a_4023_);
v___x_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4011_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4034_);
v___x_4036_ = v___x_4025_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4037_; 
v___x_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
return v___x_4037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4040_, lean_object* v___x_4041_, lean_object* v_x_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4040_, v___x_4041_, v_x_4042_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_eList_4045_, lean_object* v___x_4046_, lean_object* v___f_4047_, lean_object* v_x_4048_){
_start:
{
if (lean_obj_tag(v_x_4048_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4058_; 
lean_dec_ref(v___f_4047_);
lean_dec(v___x_4046_);
lean_dec(v_eList_4045_);
v_a_4050_ = lean_ctor_get(v_x_4048_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_x_4048_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4052_ = v_x_4048_;
v_isShared_4053_ = v_isSharedCheck_4058_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v_x_4048_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4058_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4050_);
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
else
{
lean_object* v_a_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; lean_object* v___f_4064_; lean_object* v___x_4065_; 
v_a_4059_ = lean_ctor_get(v_x_4048_, 0);
lean_inc(v_a_4059_);
lean_dec_ref(v_x_4048_);
lean_inc(v___x_4046_);
v___x_4060_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4045_, v___x_4046_);
v___x_4061_ = lean_unsigned_to_nat(0u);
v___x_4062_ = 0;
v___x_4063_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4061_, v___x_4062_, v___x_4060_, v___f_4047_);
v___f_4064_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4064_, 0, v_a_4059_);
lean_closure_set(v___f_4064_, 1, v___x_4046_);
v___x_4065_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4061_, v___x_4062_, v___x_4063_, v___f_4064_);
return v___x_4065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_eList_4066_, lean_object* v___x_4067_, lean_object* v___f_4068_, lean_object* v_x_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v_eList_4066_, v___x_4067_, v___f_4068_, v_x_4069_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_eList_4076_; lean_object* v_dList_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___f_4080_; lean_object* v___x_4081_; uint8_t v___x_4082_; lean_object* v___x_4083_; lean_object* v___f_4084_; lean_object* v___x_4085_; 
v_eList_4076_ = lean_ctor_get(v_q_4073_, 0);
lean_inc(v_eList_4076_);
v_dList_4077_ = lean_ctor_get(v_q_4073_, 1);
lean_inc(v_dList_4077_);
lean_dec_ref(v_q_4073_);
v___x_4078_ = lean_box(0);
v___x_4079_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4077_, v___x_4078_);
v___f_4080_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4081_ = lean_unsigned_to_nat(0u);
v___x_4082_ = 0;
v___x_4083_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4081_, v___x_4082_, v___x_4079_, v___f_4080_);
v___f_4084_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4084_, 0, v_eList_4076_);
lean_closure_set(v___f_4084_, 1, v___x_4078_);
lean_closure_set(v___f_4084_, 2, v___f_4080_);
v___x_4085_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4081_, v___x_4082_, v___x_4083_, v___f_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4086_, v___y_4087_);
lean_dec(v___y_4087_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4090_, lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4091_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v___y_4090_);
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
lean_object* v_a_4102_; lean_object* v_producers_4103_; lean_object* v_consumers_4104_; lean_object* v_capacity_4105_; lean_object* v_buf_4106_; lean_object* v_bufCount_4107_; lean_object* v_sendIdx_4108_; lean_object* v_recvIdx_4109_; uint8_t v_closed_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___f_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; lean_object* v___x_4116_; 
v_a_4102_ = lean_ctor_get(v_x_4091_, 0);
lean_inc(v_a_4102_);
lean_dec_ref(v_x_4091_);
v_producers_4103_ = lean_ctor_get(v_a_4102_, 0);
lean_inc_ref(v_producers_4103_);
v_consumers_4104_ = lean_ctor_get(v_a_4102_, 1);
lean_inc_ref(v_consumers_4104_);
v_capacity_4105_ = lean_ctor_get(v_a_4102_, 2);
lean_inc(v_capacity_4105_);
v_buf_4106_ = lean_ctor_get(v_a_4102_, 3);
lean_inc_ref(v_buf_4106_);
v_bufCount_4107_ = lean_ctor_get(v_a_4102_, 4);
lean_inc(v_bufCount_4107_);
v_sendIdx_4108_ = lean_ctor_get(v_a_4102_, 5);
lean_inc(v_sendIdx_4108_);
v_recvIdx_4109_ = lean_ctor_get(v_a_4102_, 6);
lean_inc(v_recvIdx_4109_);
v_closed_4110_ = lean_ctor_get_uint8(v_a_4102_, sizeof(void*)*7);
lean_dec(v_a_4102_);
v___x_4111_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4104_, v___y_4090_);
v___x_4112_ = lean_box(v_closed_4110_);
v___f_4113_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4113_, 0, v_producers_4103_);
lean_closure_set(v___f_4113_, 1, v_capacity_4105_);
lean_closure_set(v___f_4113_, 2, v_buf_4106_);
lean_closure_set(v___f_4113_, 3, v_bufCount_4107_);
lean_closure_set(v___f_4113_, 4, v_sendIdx_4108_);
lean_closure_set(v___f_4113_, 5, v_recvIdx_4109_);
lean_closure_set(v___f_4113_, 6, v___x_4112_);
lean_closure_set(v___f_4113_, 7, v___y_4090_);
v___x_4114_ = lean_unsigned_to_nat(0u);
v___x_4115_ = 0;
v___x_4116_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4114_, v___x_4115_, v___x_4111_, v___f_4113_);
return v___x_4116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4117_, lean_object* v_x_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4117_, v_x_4118_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; lean_object* v___f_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; 
v___x_4123_ = lean_st_ref_get(v___y_4121_);
v___f_4124_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4124_, 0, v___y_4121_);
v___x_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4123_);
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
v___x_4127_ = lean_unsigned_to_nat(0u);
v___x_4128_ = 0;
v___x_4129_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4127_, v___x_4128_, v___x_4126_, v___f_4124_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4130_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4138_){
_start:
{
lean_object* v___f_4139_; lean_object* v___f_4140_; lean_object* v___f_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_inc_ref(v_ch_4138_);
v___f_4139_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4139_, 0, v_ch_4138_);
v___f_4140_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___f_4141_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2));
lean_inc_ref(v_ch_4138_);
v___x_4142_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4142_, 0, lean_box(0));
lean_closure_set(v___x_4142_, 1, lean_box(0));
lean_closure_set(v___x_4142_, 2, v_ch_4138_);
lean_closure_set(v___x_4142_, 3, v___f_4140_);
v___x_4143_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4143_, 0, lean_box(0));
lean_closure_set(v___x_4143_, 1, lean_box(0));
lean_closure_set(v___x_4143_, 2, v_ch_4138_);
lean_closure_set(v___x_4143_, 3, v___f_4141_);
v___x_4144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___f_4139_);
lean_ctor_set(v___x_4144_, 2, v___x_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4145_, lean_object* v_ch_4146_){
_start:
{
lean_object* v___x_4147_; 
v___x_4147_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4146_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4148_, lean_object* v_q_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4149_, v___y_4150_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4153_, lean_object* v_q_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4153_, v_q_4154_, v___y_4155_);
lean_dec(v___y_4155_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4158_, lean_object* v_x_4159_, lean_object* v_x_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v___x_4163_; 
v___x_4163_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4159_, v_x_4160_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4164_, lean_object* v_x_4165_, lean_object* v_x_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4164_, v_x_4165_, v_x_4166_, v___y_4167_);
lean_dec(v___y_4167_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object* v_x_4170_){
_start:
{
switch(lean_obj_tag(v_x_4170_))
{
case 0:
{
lean_object* v___x_4171_; 
v___x_4171_ = lean_unsigned_to_nat(0u);
return v___x_4171_;
}
case 1:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_unsigned_to_nat(1u);
return v___x_4172_;
}
default: 
{
lean_object* v___x_4173_; 
v___x_4173_ = lean_unsigned_to_nat(2u);
return v___x_4173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object* v_x_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4174_);
lean_dec_ref(v_x_4174_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object* v_00_u03b1_4176_, lean_object* v_x_4177_){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object* v_00_u03b1_4179_, lean_object* v_x_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_4179_, v_x_4180_);
lean_dec_ref(v_x_4180_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4182_, lean_object* v_k_4183_){
_start:
{
lean_object* v_ch_4184_; lean_object* v___x_4185_; 
v_ch_4184_ = lean_ctor_get(v_t_4182_, 0);
lean_inc_ref(v_ch_4184_);
lean_dec_ref(v_t_4182_);
v___x_4185_ = lean_apply_1(v_k_4183_, v_ch_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4186_, lean_object* v_motive_4187_, lean_object* v_ctorIdx_4188_, lean_object* v_t_4189_, lean_object* v_h_4190_, lean_object* v_k_4191_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4189_, v_k_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4193_, lean_object* v_motive_4194_, lean_object* v_ctorIdx_4195_, lean_object* v_t_4196_, lean_object* v_h_4197_, lean_object* v_k_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4193_, v_motive_4194_, v_ctorIdx_4195_, v_t_4196_, v_h_4197_, v_k_4198_);
lean_dec(v_ctorIdx_4195_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4200_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4201_){
_start:
{
lean_object* v___x_4202_; 
v___x_4202_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4200_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4203_, lean_object* v_motive_4204_, lean_object* v_t_4205_, lean_object* v_h_4206_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4207_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4205_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4209_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4210_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4209_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4212_, lean_object* v_motive_4213_, lean_object* v_t_4214_, lean_object* v_h_4215_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4214_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4218_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4219_){
_start:
{
lean_object* v___x_4220_; 
v___x_4220_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4218_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4219_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4221_, lean_object* v_motive_4222_, lean_object* v_t_4223_, lean_object* v_h_4224_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4223_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4225_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4227_){
_start:
{
if (lean_obj_tag(v_capacity_4227_) == 0)
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4229_);
return v___x_4230_;
}
else
{
lean_object* v_val_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4248_; 
v_val_4231_ = lean_ctor_get(v_capacity_4227_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v_capacity_4227_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4233_ = v_capacity_4227_;
v_isShared_4234_ = v_isSharedCheck_4248_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_val_4231_);
lean_dec(v_capacity_4227_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4248_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v_zero_4235_; uint8_t v_isZero_4236_; 
v_zero_4235_ = lean_unsigned_to_nat(0u);
v_isZero_4236_ = lean_nat_dec_eq(v_val_4231_, v_zero_4235_);
if (v_isZero_4236_ == 1)
{
lean_object* v___x_4237_; lean_object* v___x_4239_; 
lean_dec(v_val_4231_);
v___x_4237_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4237_);
v___x_4239_ = v___x_4233_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
else
{
lean_object* v_one_4241_; lean_object* v_n_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4246_; 
v_one_4241_ = lean_unsigned_to_nat(1u);
v_n_4242_ = lean_nat_sub(v_val_4231_, v_one_4241_);
lean_dec(v_val_4231_);
v___x_4243_ = lean_nat_add(v_n_4242_, v_one_4241_);
lean_dec(v_n_4242_);
v___x_4244_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4243_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set_tag(v___x_4233_, 2);
lean_ctor_set(v___x_4233_, 0, v___x_4244_);
v___x_4246_ = v___x_4233_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4244_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Std_CloseableChannel_new___redArg(v_capacity_4249_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4252_, lean_object* v_capacity_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Std_CloseableChannel_new___redArg(v_capacity_4253_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4256_, lean_object* v_capacity_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Std_CloseableChannel_new(v_00_u03b1_4256_, v_capacity_4257_);
return v_res_4259_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4260_, lean_object* v_v_4261_){
_start:
{
switch(lean_obj_tag(v_ch_4260_))
{
case 0:
{
lean_object* v_ch_4263_; uint8_t v___x_4264_; 
v_ch_4263_ = lean_ctor_get(v_ch_4260_, 0);
lean_inc_ref(v_ch_4263_);
lean_dec_ref(v_ch_4260_);
v___x_4264_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4263_, v_v_4261_);
return v___x_4264_;
}
case 1:
{
lean_object* v_ch_4265_; uint8_t v___x_4266_; 
v_ch_4265_ = lean_ctor_get(v_ch_4260_, 0);
lean_inc_ref(v_ch_4265_);
lean_dec_ref(v_ch_4260_);
v___x_4266_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4265_, v_v_4261_);
return v___x_4266_;
}
default: 
{
lean_object* v_ch_4267_; uint8_t v___x_4268_; 
v_ch_4267_ = lean_ctor_get(v_ch_4260_, 0);
lean_inc_ref(v_ch_4267_);
lean_dec_ref(v_ch_4260_);
v___x_4268_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4267_, v_v_4261_);
return v___x_4268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4269_, lean_object* v_v_4270_, lean_object* v_a_4271_){
_start:
{
uint8_t v_res_4272_; lean_object* v_r_4273_; 
v_res_4272_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4269_, v_v_4270_);
v_r_4273_ = lean_box(v_res_4272_);
return v_r_4273_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4274_, lean_object* v_ch_4275_, lean_object* v_v_4276_){
_start:
{
uint8_t v___x_4278_; 
v___x_4278_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4275_, v_v_4276_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4279_, lean_object* v_ch_4280_, lean_object* v_v_4281_, lean_object* v_a_4282_){
_start:
{
uint8_t v_res_4283_; lean_object* v_r_4284_; 
v_res_4283_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4279_, v_ch_4280_, v_v_4281_);
v_r_4284_ = lean_box(v_res_4283_);
return v_r_4284_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4285_, lean_object* v_v_4286_){
_start:
{
switch(lean_obj_tag(v_ch_4285_))
{
case 0:
{
lean_object* v_ch_4288_; lean_object* v___x_4289_; 
v_ch_4288_ = lean_ctor_get(v_ch_4285_, 0);
lean_inc_ref(v_ch_4288_);
lean_dec_ref(v_ch_4285_);
v___x_4289_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4288_, v_v_4286_);
return v___x_4289_;
}
case 1:
{
lean_object* v_ch_4290_; lean_object* v___x_4291_; 
v_ch_4290_ = lean_ctor_get(v_ch_4285_, 0);
lean_inc_ref(v_ch_4290_);
lean_dec_ref(v_ch_4285_);
v___x_4291_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4290_, v_v_4286_);
return v___x_4291_;
}
default: 
{
lean_object* v_ch_4292_; lean_object* v___x_4293_; 
v_ch_4292_ = lean_ctor_get(v_ch_4285_, 0);
lean_inc_ref(v_ch_4292_);
lean_dec_ref(v_ch_4285_);
v___x_4293_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4292_, v_v_4286_);
return v___x_4293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4294_, lean_object* v_v_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Std_CloseableChannel_send___redArg(v_ch_4294_, v_v_4295_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4298_, lean_object* v_ch_4299_, lean_object* v_v_4300_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Std_CloseableChannel_send___redArg(v_ch_4299_, v_v_4300_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4303_, lean_object* v_ch_4304_, lean_object* v_v_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l_Std_CloseableChannel_send(v_00_u03b1_4303_, v_ch_4304_, v_v_4305_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4308_){
_start:
{
switch(lean_obj_tag(v_ch_4308_))
{
case 0:
{
lean_object* v_ch_4310_; lean_object* v___x_4311_; 
v_ch_4310_ = lean_ctor_get(v_ch_4308_, 0);
lean_inc_ref(v_ch_4310_);
lean_dec_ref(v_ch_4308_);
v___x_4311_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4310_);
return v___x_4311_;
}
case 1:
{
lean_object* v_ch_4312_; lean_object* v___x_4313_; 
v_ch_4312_ = lean_ctor_get(v_ch_4308_, 0);
lean_inc_ref(v_ch_4312_);
lean_dec_ref(v_ch_4308_);
v___x_4313_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4312_);
return v___x_4313_;
}
default: 
{
lean_object* v_ch_4314_; lean_object* v___x_4315_; 
v_ch_4314_ = lean_ctor_get(v_ch_4308_, 0);
lean_inc_ref(v_ch_4314_);
lean_dec_ref(v_ch_4308_);
v___x_4315_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4314_);
return v___x_4315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4316_, lean_object* v_a_4317_){
_start:
{
lean_object* v_res_4318_; 
v_res_4318_ = l_Std_CloseableChannel_close___redArg(v_ch_4316_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4319_, lean_object* v_ch_4320_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l_Std_CloseableChannel_close___redArg(v_ch_4320_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4323_, lean_object* v_ch_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Std_CloseableChannel_close(v_00_u03b1_4323_, v_ch_4324_);
return v_res_4326_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4327_){
_start:
{
switch(lean_obj_tag(v_ch_4327_))
{
case 0:
{
lean_object* v_ch_4329_; uint8_t v___x_4330_; 
v_ch_4329_ = lean_ctor_get(v_ch_4327_, 0);
lean_inc_ref(v_ch_4329_);
lean_dec_ref(v_ch_4327_);
v___x_4330_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4329_);
return v___x_4330_;
}
case 1:
{
lean_object* v_ch_4331_; uint8_t v___x_4332_; 
v_ch_4331_ = lean_ctor_get(v_ch_4327_, 0);
lean_inc_ref(v_ch_4331_);
lean_dec_ref(v_ch_4327_);
v___x_4332_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4331_);
return v___x_4332_;
}
default: 
{
lean_object* v_ch_4333_; uint8_t v___x_4334_; 
v_ch_4333_ = lean_ctor_get(v_ch_4327_, 0);
lean_inc_ref(v_ch_4333_);
lean_dec_ref(v_ch_4327_);
v___x_4334_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4333_);
return v___x_4334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4335_, lean_object* v_a_4336_){
_start:
{
uint8_t v_res_4337_; lean_object* v_r_4338_; 
v_res_4337_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4335_);
v_r_4338_ = lean_box(v_res_4337_);
return v_r_4338_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4339_, lean_object* v_ch_4340_){
_start:
{
uint8_t v___x_4342_; 
v___x_4342_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4340_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4343_, lean_object* v_ch_4344_, lean_object* v_a_4345_){
_start:
{
uint8_t v_res_4346_; lean_object* v_r_4347_; 
v_res_4346_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4343_, v_ch_4344_);
v_r_4347_ = lean_box(v_res_4346_);
return v_r_4347_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4348_){
_start:
{
switch(lean_obj_tag(v_ch_4348_))
{
case 0:
{
lean_object* v_ch_4350_; lean_object* v___x_4351_; 
v_ch_4350_ = lean_ctor_get(v_ch_4348_, 0);
lean_inc_ref(v_ch_4350_);
lean_dec_ref(v_ch_4348_);
v___x_4351_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4350_);
return v___x_4351_;
}
case 1:
{
lean_object* v_ch_4352_; lean_object* v___x_4353_; 
v_ch_4352_ = lean_ctor_get(v_ch_4348_, 0);
lean_inc_ref(v_ch_4352_);
lean_dec_ref(v_ch_4348_);
v___x_4353_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4352_);
return v___x_4353_;
}
default: 
{
lean_object* v_ch_4354_; lean_object* v___x_4355_; 
v_ch_4354_ = lean_ctor_get(v_ch_4348_, 0);
lean_inc_ref(v_ch_4354_);
lean_dec_ref(v_ch_4348_);
v___x_4355_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4354_);
return v___x_4355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4356_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4359_, lean_object* v_ch_4360_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4360_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4363_, lean_object* v_ch_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4363_, v_ch_4364_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4367_){
_start:
{
switch(lean_obj_tag(v_ch_4367_))
{
case 0:
{
lean_object* v_ch_4369_; lean_object* v___x_4370_; 
v_ch_4369_ = lean_ctor_get(v_ch_4367_, 0);
lean_inc_ref(v_ch_4369_);
lean_dec_ref(v_ch_4367_);
v___x_4370_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4369_);
return v___x_4370_;
}
case 1:
{
lean_object* v_ch_4371_; lean_object* v___x_4372_; 
v_ch_4371_ = lean_ctor_get(v_ch_4367_, 0);
lean_inc_ref(v_ch_4371_);
lean_dec_ref(v_ch_4367_);
v___x_4372_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4371_);
return v___x_4372_;
}
default: 
{
lean_object* v_ch_4373_; lean_object* v___x_4374_; 
v_ch_4373_ = lean_ctor_get(v_ch_4367_, 0);
lean_inc_ref(v_ch_4373_);
lean_dec_ref(v_ch_4367_);
v___x_4374_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4373_);
return v___x_4374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4375_, lean_object* v_a_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Std_CloseableChannel_recv___redArg(v_ch_4375_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4378_, lean_object* v_ch_4379_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Std_CloseableChannel_recv___redArg(v_ch_4379_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4382_, lean_object* v_ch_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Std_CloseableChannel_recv(v_00_u03b1_4382_, v_ch_4383_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4386_){
_start:
{
switch(lean_obj_tag(v_ch_4386_))
{
case 0:
{
lean_object* v_ch_4387_; lean_object* v___x_4388_; 
v_ch_4387_ = lean_ctor_get(v_ch_4386_, 0);
lean_inc_ref(v_ch_4387_);
lean_dec_ref(v_ch_4386_);
v___x_4388_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4387_);
return v___x_4388_;
}
case 1:
{
lean_object* v_ch_4389_; lean_object* v___x_4390_; 
v_ch_4389_ = lean_ctor_get(v_ch_4386_, 0);
lean_inc_ref(v_ch_4389_);
lean_dec_ref(v_ch_4386_);
v___x_4390_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4389_);
return v___x_4390_;
}
default: 
{
lean_object* v_ch_4391_; lean_object* v___x_4392_; 
v_ch_4391_ = lean_ctor_get(v_ch_4386_, 0);
lean_inc_ref(v_ch_4391_);
lean_dec_ref(v_ch_4386_);
v___x_4392_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4391_);
return v___x_4392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4393_, lean_object* v_ch_4394_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4394_);
return v___x_4395_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = lean_box(0);
v___x_4397_ = lean_task_pure(v___x_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4398_, lean_object* v_ch_4399_, lean_object* v_prio_4400_, lean_object* v_x_4401_){
_start:
{
if (lean_obj_tag(v_x_4401_) == 0)
{
lean_object* v___x_4403_; 
lean_dec(v_prio_4400_);
lean_dec_ref(v_ch_4399_);
lean_dec_ref(v_f_4398_);
v___x_4403_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4403_;
}
else
{
lean_object* v_val_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v_val_4404_ = lean_ctor_get(v_x_4401_, 0);
lean_inc(v_val_4404_);
lean_dec_ref(v_x_4401_);
lean_inc_ref(v_f_4398_);
v___x_4405_ = lean_apply_2(v_f_4398_, v_val_4404_, lean_box(0));
v___x_4406_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4398_, v_ch_4399_, v_prio_4400_);
return v___x_4406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4407_, lean_object* v_ch_4408_, lean_object* v_prio_4409_, lean_object* v_x_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4407_, v_ch_4408_, v_prio_4409_, v_x_4410_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4413_, lean_object* v_ch_4414_, lean_object* v_prio_4415_){
_start:
{
lean_object* v___x_4417_; lean_object* v___f_4418_; uint8_t v___x_4419_; lean_object* v___x_4420_; 
lean_inc_ref(v_ch_4414_);
v___x_4417_ = l_Std_CloseableChannel_recv___redArg(v_ch_4414_);
lean_inc(v_prio_4415_);
v___f_4418_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4418_, 0, v_f_4413_);
lean_closure_set(v___f_4418_, 1, v_ch_4414_);
lean_closure_set(v___f_4418_, 2, v_prio_4415_);
v___x_4419_ = 0;
v___x_4420_ = lean_io_bind_task(v___x_4417_, v___f_4418_, v_prio_4415_, v___x_4419_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4421_, lean_object* v_ch_4422_, lean_object* v_prio_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4421_, v_ch_4422_, v_prio_4423_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4426_, lean_object* v_f_4427_, lean_object* v_ch_4428_, lean_object* v_prio_4429_){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4427_, v_ch_4428_, v_prio_4429_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4432_, lean_object* v_f_4433_, lean_object* v_ch_4434_, lean_object* v_prio_4435_, lean_object* v_a_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4432_, v_f_4433_, v_ch_4434_, v_prio_4435_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(lean_object* v_x_4438_){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = lean_box(0);
v___x_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed(lean_object* v_x_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(v_x_4442_);
lean_dec_ref(v_x_4442_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4450_, lean_object* v_inst_4451_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4453_, lean_object* v_inst_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4453_, v_inst_4454_);
lean_dec(v_inst_4454_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_4456_){
_start:
{
lean_object* v___x_4457_; 
v___x_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4457_, 0, v_a_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_4458_, lean_object* v_x_4459_){
_start:
{
if (lean_obj_tag(v_x_4459_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4469_; 
lean_dec_ref(v___f_4458_);
v_a_4461_ = lean_ctor_get(v_x_4459_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v_x_4459_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4463_ = v_x_4459_;
v_isShared_4464_ = v_isSharedCheck_4469_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v_x_4459_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4469_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
lean_object* v___x_4467_; 
v___x_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
return v___x_4467_;
}
}
}
else
{
lean_object* v_a_4470_; 
v_a_4470_ = lean_ctor_get(v_x_4459_, 0);
lean_inc(v_a_4470_);
lean_dec_ref(v_x_4459_);
if (lean_obj_tag(v_a_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4479_; 
lean_dec_ref(v___f_4458_);
v_a_4471_ = lean_ctor_get(v_a_4470_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v_a_4470_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4473_ = v_a_4470_;
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v_a_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
}
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4480_ = lean_ctor_get(v_a_4470_, 0);
lean_inc(v_a_4480_);
lean_dec_ref(v_a_4470_);
v___x_4481_ = lean_unsigned_to_nat(0u);
v___x_4482_ = 0;
v___x_4483_ = lean_task_map(v___f_4458_, v_a_4480_, v___x_4481_, v___x_4482_);
v___x_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
return v___x_4484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_4485_, lean_object* v_x_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(v___f_4485_, v_x_4486_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_4489_, lean_object* v_receiver_4490_){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; uint8_t v___x_4497_; lean_object* v___x_4498_; 
v___x_4492_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4490_);
v___x_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
v___x_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
v___x_4496_ = lean_unsigned_to_nat(0u);
v___x_4497_ = 0;
v___x_4498_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4496_, v___x_4497_, v___x_4495_, v___f_4489_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_4499_, lean_object* v_receiver_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(v___f_4499_, v_receiver_4500_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4508_, lean_object* v_inst_4509_){
_start:
{
lean_object* v___f_4510_; 
v___f_4510_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2));
return v___f_4510_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4511_, lean_object* v_inst_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4511_, v_inst_4512_);
lean_dec(v_inst_4512_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_4515_, lean_object* v_x_4516_){
_start:
{
if (lean_obj_tag(v_x_4516_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4526_; 
lean_dec_ref(v___f_4515_);
v_a_4518_ = lean_ctor_get(v_x_4516_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_x_4516_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4520_ = v_x_4516_;
v_isShared_4521_ = v_isSharedCheck_4526_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v_x_4516_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4526_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4524_; 
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
return v___x_4524_;
}
}
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; uint8_t v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v_a_4527_ = lean_ctor_get(v_x_4516_, 0);
lean_inc(v_a_4527_);
lean_dec_ref(v_x_4516_);
v___x_4528_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0));
v___x_4529_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4529_, 0, lean_box(0));
lean_closure_set(v___x_4529_, 1, lean_box(0));
lean_closure_set(v___x_4529_, 2, lean_box(0));
lean_closure_set(v___x_4529_, 3, v___x_4528_);
lean_closure_set(v___x_4529_, 4, v___f_4515_);
v___x_4530_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4530_, 0, lean_box(0));
lean_closure_set(v___x_4530_, 1, lean_box(0));
lean_closure_set(v___x_4530_, 2, lean_box(0));
lean_closure_set(v___x_4530_, 3, v___x_4529_);
v___x_4531_ = lean_unsigned_to_nat(0u);
v___x_4532_ = 0;
v___x_4533_ = lean_task_map(v___x_4530_, v_a_4527_, v___x_4531_, v___x_4532_);
v___x_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
return v___x_4534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_4535_, lean_object* v_x_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(v___f_4535_, v_x_4536_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_4539_, lean_object* v_receiver_4540_, lean_object* v_x_4541_){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; lean_object* v___x_4548_; 
v___x_4543_ = l_Std_CloseableChannel_send___redArg(v_receiver_4540_, v_x_4541_);
v___x_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
v___x_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4544_);
v___x_4546_ = lean_unsigned_to_nat(0u);
v___x_4547_ = 0;
v___x_4548_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4546_, v___x_4547_, v___x_4545_, v___f_4539_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_4549_, lean_object* v_receiver_4550_, lean_object* v_x_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(v___f_4549_, v_receiver_4550_, v_x_4551_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(lean_object* v_x_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v_x_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(v_x_4557_);
lean_dec_ref(v_x_4557_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(lean_object* v___f_4560_, lean_object* v_socket_4561_, lean_object* v_x_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = lean_apply_3(v___f_4560_, v_socket_4561_, v___y_4563_, lean_box(0));
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v___f_4566_, lean_object* v_socket_4567_, lean_object* v_x_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(v___f_4566_, v_socket_4567_, v_x_4568_, v___y_4569_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_4572_, lean_object* v___x_4573_, lean_object* v_socket_4574_, lean_object* v_data_4575_){
_start:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; uint8_t v___x_4580_; 
v___x_4577_ = lean_unsigned_to_nat(0u);
v___x_4578_ = lean_array_get_size(v_data_4575_);
v___x_4579_ = lean_box(0);
v___x_4580_ = lean_nat_dec_lt(v___x_4577_, v___x_4578_);
if (v___x_4580_ == 0)
{
lean_object* v___x_4581_; 
lean_dec_ref(v_data_4575_);
lean_dec_ref(v_socket_4574_);
lean_dec_ref(v___x_4573_);
lean_dec_ref(v___f_4572_);
v___x_4581_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4581_;
}
else
{
lean_object* v___f_4582_; uint8_t v___x_4583_; 
v___f_4582_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4582_, 0, v___f_4572_);
lean_closure_set(v___f_4582_, 1, v_socket_4574_);
v___x_4583_ = lean_nat_dec_le(v___x_4578_, v___x_4578_);
if (v___x_4583_ == 0)
{
if (v___x_4580_ == 0)
{
lean_object* v___x_4584_; 
lean_dec_ref(v___f_4582_);
lean_dec_ref(v_data_4575_);
lean_dec_ref(v___x_4573_);
v___x_4584_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4584_;
}
else
{
size_t v___x_4585_; size_t v___x_4586_; lean_object* v___x_711__overap_4587_; lean_object* v___x_4588_; 
v___x_4585_ = ((size_t)0ULL);
v___x_4586_ = lean_usize_of_nat(v___x_4578_);
v___x_711__overap_4587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4573_, v___f_4582_, v_data_4575_, v___x_4585_, v___x_4586_, v___x_4579_);
v___x_4588_ = lean_apply_1(v___x_711__overap_4587_, lean_box(0));
return v___x_4588_;
}
}
else
{
size_t v___x_4589_; size_t v___x_4590_; lean_object* v___x_714__overap_4591_; lean_object* v___x_4592_; 
v___x_4589_ = ((size_t)0ULL);
v___x_4590_ = lean_usize_of_nat(v___x_4578_);
v___x_714__overap_4591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4573_, v___f_4582_, v_data_4575_, v___x_4589_, v___x_4590_, v___x_4579_);
v___x_4592_ = lean_apply_1(v___x_714__overap_4591_, lean_box(0));
return v___x_4592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_4593_, lean_object* v___x_4594_, lean_object* v_socket_4595_, lean_object* v_data_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(v___f_4593_, v___x_4594_, v_socket_4595_, v_data_4596_);
return v_res_4598_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l_Std_Internal_IO_Async_EAsync_instMonad(lean_box(0));
return v___x_4604_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_4605_; lean_object* v___f_4606_; lean_object* v___f_4607_; 
v___x_4605_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_4606_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___f_4607_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4607_, 0, v___f_4606_);
lean_closure_set(v___f_4607_, 1, v___x_4605_);
return v___f_4607_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___f_4608_; lean_object* v___f_4609_; lean_object* v___f_4610_; lean_object* v___x_4611_; 
v___f_4608_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_4609_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4);
v___f_4610_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___x_4611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4611_, 0, v___f_4610_);
lean_ctor_set(v___x_4611_, 1, v___f_4609_);
lean_ctor_set(v___x_4611_, 2, v___f_4608_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4612_, lean_object* v_inst_4613_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5);
return v___x_4614_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4615_, lean_object* v_inst_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4615_, v_inst_4616_);
lean_dec(v_inst_4616_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4618_){
_start:
{
lean_inc_ref(v_ch_4618_);
return v_ch_4618_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_Std_CloseableChannel_sync___redArg(v_ch_4619_);
lean_dec_ref(v_ch_4619_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4621_, lean_object* v_ch_4622_){
_start:
{
lean_inc_ref(v_ch_4622_);
return v_ch_4622_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4623_, lean_object* v_ch_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Std_CloseableChannel_sync(v_00_u03b1_4623_, v_ch_4624_);
lean_dec_ref(v_ch_4624_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4626_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l_Std_CloseableChannel_new___redArg(v_capacity_4626_);
return v___x_4628_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4629_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4632_, lean_object* v_capacity_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Std_CloseableChannel_new___redArg(v_capacity_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4636_, lean_object* v_capacity_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4636_, v_capacity_4637_);
return v_res_4639_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4640_, lean_object* v_v_4641_){
_start:
{
uint8_t v___x_4643_; 
v___x_4643_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4640_, v_v_4641_);
return v___x_4643_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4644_, lean_object* v_v_4645_, lean_object* v_a_4646_){
_start:
{
uint8_t v_res_4647_; lean_object* v_r_4648_; 
v_res_4647_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4644_, v_v_4645_);
v_r_4648_ = lean_box(v_res_4647_);
return v_r_4648_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4649_, lean_object* v_ch_4650_, lean_object* v_v_4651_){
_start:
{
uint8_t v___x_4653_; 
v___x_4653_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4650_, v_v_4651_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4654_, lean_object* v_ch_4655_, lean_object* v_v_4656_, lean_object* v_a_4657_){
_start:
{
uint8_t v_res_4658_; lean_object* v_r_4659_; 
v_res_4658_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4654_, v_ch_4655_, v_v_4656_);
v_r_4659_ = lean_box(v_res_4658_);
return v_r_4659_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4660_, lean_object* v_v_4661_){
_start:
{
lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4663_ = l_Std_CloseableChannel_send___redArg(v_ch_4660_, v_v_4661_);
v___x_4664_ = lean_io_wait(v___x_4663_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4664_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4664_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
lean_ctor_set_tag(v___x_4667_, 1);
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
v_a_4673_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4664_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4664_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
lean_ctor_set_tag(v___x_4675_, 0);
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4681_, lean_object* v_v_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4681_, v_v_4682_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4685_, lean_object* v_ch_4686_, lean_object* v_v_4687_){
_start:
{
lean_object* v___x_4689_; 
v___x_4689_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4686_, v_v_4687_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4690_, lean_object* v_ch_4691_, lean_object* v_v_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v_res_4694_; 
v_res_4694_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4690_, v_ch_4691_, v_v_4692_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4695_){
_start:
{
lean_object* v___x_4697_; 
v___x_4697_ = l_Std_CloseableChannel_close___redArg(v_ch_4695_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4698_, lean_object* v_a_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4698_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4701_, lean_object* v_ch_4702_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l_Std_CloseableChannel_close___redArg(v_ch_4702_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4705_, lean_object* v_ch_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4705_, v_ch_4706_);
return v_res_4708_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4709_){
_start:
{
uint8_t v___x_4711_; 
v___x_4711_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4709_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4712_, lean_object* v_a_4713_){
_start:
{
uint8_t v_res_4714_; lean_object* v_r_4715_; 
v_res_4714_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4712_);
v_r_4715_ = lean_box(v_res_4714_);
return v_r_4715_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4716_, lean_object* v_ch_4717_){
_start:
{
uint8_t v___x_4719_; 
v___x_4719_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4717_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4720_, lean_object* v_ch_4721_, lean_object* v_a_4722_){
_start:
{
uint8_t v_res_4723_; lean_object* v_r_4724_; 
v_res_4723_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4720_, v_ch_4721_);
v_r_4724_ = lean_box(v_res_4723_);
return v_r_4724_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4725_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4728_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4731_, lean_object* v_ch_4732_){
_start:
{
lean_object* v___x_4734_; 
v___x_4734_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4732_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4735_, lean_object* v_ch_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4735_, v_ch_4736_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4739_){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4741_ = l_Std_CloseableChannel_recv___redArg(v_ch_4739_);
v___x_4742_ = lean_io_wait(v___x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4743_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4746_, lean_object* v_ch_4747_){
_start:
{
lean_object* v___x_4749_; 
v___x_4749_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4747_);
return v___x_4749_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4750_, lean_object* v_ch_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4750_, v_ch_4751_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4754_, lean_object* v_b_4755_, lean_object* v_f_4756_, lean_object* v_toBind_4757_, lean_object* v___f_4758_, lean_object* v_____do__lift_4759_){
_start:
{
if (lean_obj_tag(v_____do__lift_4759_) == 0)
{
lean_object* v___x_4760_; 
lean_dec(v___f_4758_);
lean_dec(v_toBind_4757_);
lean_dec(v_f_4756_);
v___x_4760_ = lean_apply_2(v_toPure_4754_, lean_box(0), v_b_4755_);
return v___x_4760_;
}
else
{
lean_object* v_val_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
lean_dec(v_toPure_4754_);
v_val_4761_ = lean_ctor_get(v_____do__lift_4759_, 0);
lean_inc(v_val_4761_);
lean_dec_ref(v_____do__lift_4759_);
v___x_4762_ = lean_apply_2(v_f_4756_, v_val_4761_, v_b_4755_);
v___x_4763_ = lean_apply_4(v_toBind_4757_, lean_box(0), lean_box(0), v___x_4762_, v___f_4758_);
return v___x_4763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4764_, lean_object* v_inst_4765_, lean_object* v_ch_4766_, lean_object* v_f_4767_, lean_object* v_b_4768_){
_start:
{
lean_object* v_toApplicative_4769_; lean_object* v_toBind_4770_; lean_object* v_toPure_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___f_4774_; lean_object* v___f_4775_; lean_object* v___x_4776_; 
v_toApplicative_4769_ = lean_ctor_get(v_inst_4764_, 0);
v_toBind_4770_ = lean_ctor_get(v_inst_4764_, 1);
lean_inc(v_toBind_4770_);
v_toPure_4771_ = lean_ctor_get(v_toApplicative_4769_, 1);
lean_inc(v_toPure_4771_);
lean_inc_ref(v_ch_4766_);
v___x_4772_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4772_, 0, lean_box(0));
lean_closure_set(v___x_4772_, 1, v_ch_4766_);
lean_inc(v_inst_4765_);
v___x_4773_ = lean_apply_2(v_inst_4765_, lean_box(0), v___x_4772_);
lean_inc(v_f_4767_);
lean_inc(v_toPure_4771_);
v___f_4774_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4774_, 0, v_toPure_4771_);
lean_closure_set(v___f_4774_, 1, v_inst_4764_);
lean_closure_set(v___f_4774_, 2, v_inst_4765_);
lean_closure_set(v___f_4774_, 3, v_ch_4766_);
lean_closure_set(v___f_4774_, 4, v_f_4767_);
lean_inc(v_toBind_4770_);
v___f_4775_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4775_, 0, v_toPure_4771_);
lean_closure_set(v___f_4775_, 1, v_b_4768_);
lean_closure_set(v___f_4775_, 2, v_f_4767_);
lean_closure_set(v___f_4775_, 3, v_toBind_4770_);
lean_closure_set(v___f_4775_, 4, v___f_4774_);
v___x_4776_ = lean_apply_4(v_toBind_4770_, lean_box(0), lean_box(0), v___x_4773_, v___f_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4777_, lean_object* v_inst_4778_, lean_object* v_inst_4779_, lean_object* v_ch_4780_, lean_object* v_f_4781_, lean_object* v_____do__lift_4782_){
_start:
{
if (lean_obj_tag(v_____do__lift_4782_) == 0)
{
lean_object* v_a_4783_; lean_object* v___x_4784_; 
lean_dec(v_f_4781_);
lean_dec_ref(v_ch_4780_);
lean_dec(v_inst_4779_);
lean_dec_ref(v_inst_4778_);
v_a_4783_ = lean_ctor_get(v_____do__lift_4782_, 0);
lean_inc(v_a_4783_);
lean_dec_ref(v_____do__lift_4782_);
v___x_4784_ = lean_apply_2(v_toPure_4777_, lean_box(0), v_a_4783_);
return v___x_4784_;
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4786_; 
lean_dec(v_toPure_4777_);
v_a_4785_ = lean_ctor_get(v_____do__lift_4782_, 0);
lean_inc(v_a_4785_);
lean_dec_ref(v_____do__lift_4782_);
v___x_4786_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4778_, v_inst_4779_, v_ch_4780_, v_f_4781_, v_a_4785_);
return v___x_4786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4787_, lean_object* v_00_u03b1_4788_, lean_object* v_00_u03b2_4789_, lean_object* v_inst_4790_, lean_object* v_inst_4791_, lean_object* v_ch_4792_, lean_object* v_f_4793_, lean_object* v_b_4794_){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4790_, v_inst_4791_, v_ch_4792_, v_f_4793_, v_b_4794_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4796_, lean_object* v_inst_4797_, lean_object* v_ch_4798_, lean_object* v_b_4799_, lean_object* v_f_4800_){
_start:
{
lean_object* v___x_4801_; 
v___x_4801_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4796_, v_inst_4797_, v_ch_4798_, v_f_4800_, v_b_4799_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4802_, lean_object* v_00_u03b1_4803_, lean_object* v_inst_4804_, lean_object* v_inst_4805_, lean_object* v_00_u03b2_4806_, lean_object* v_ch_4807_, lean_object* v_b_4808_, lean_object* v_f_4809_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4804_, v_inst_4805_, v_ch_4807_, v_f_4809_, v_b_4808_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4811_, lean_object* v_inst_4812_, lean_object* v_00_u03b2_4813_, lean_object* v_ch_4814_, lean_object* v_b_4815_, lean_object* v_f_4816_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4811_, v_inst_4812_, v_ch_4814_, v_f_4816_, v_b_4815_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4818_, lean_object* v_inst_4819_){
_start:
{
lean_object* v___f_4820_; 
v___f_4820_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4820_, 0, v_inst_4818_);
lean_closure_set(v___f_4820_, 1, v_inst_4819_);
return v___f_4820_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4821_, lean_object* v_00_u03b1_4822_, lean_object* v_inst_4823_, lean_object* v_inst_4824_){
_start:
{
lean_object* v___f_4825_; 
v___f_4825_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4825_, 0, v_inst_4823_);
lean_closure_set(v___f_4825_, 1, v_inst_4824_);
return v___f_4825_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4826_){
_start:
{
lean_object* v___x_4828_; 
v___x_4828_ = l_Std_CloseableChannel_new___redArg(v_capacity_4826_);
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_Std_Channel_new___redArg(v_capacity_4829_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4832_, lean_object* v_capacity_4833_){
_start:
{
lean_object* v___x_4835_; 
v___x_4835_ = l_Std_CloseableChannel_new___redArg(v_capacity_4833_);
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4836_, lean_object* v_capacity_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Std_Channel_new(v_00_u03b1_4836_, v_capacity_4837_);
return v_res_4839_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4840_, lean_object* v_v_4841_){
_start:
{
uint8_t v___x_4843_; 
v___x_4843_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4840_, v_v_4841_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4844_, lean_object* v_v_4845_, lean_object* v_a_4846_){
_start:
{
uint8_t v_res_4847_; lean_object* v_r_4848_; 
v_res_4847_ = l_Std_Channel_trySend___redArg(v_ch_4844_, v_v_4845_);
v_r_4848_ = lean_box(v_res_4847_);
return v_r_4848_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4849_, lean_object* v_ch_4850_, lean_object* v_v_4851_){
_start:
{
uint8_t v___x_4853_; 
v___x_4853_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4850_, v_v_4851_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4854_, lean_object* v_ch_4855_, lean_object* v_v_4856_, lean_object* v_a_4857_){
_start:
{
uint8_t v_res_4858_; lean_object* v_r_4859_; 
v_res_4858_ = l_Std_Channel_trySend(v_00_u03b1_4854_, v_ch_4855_, v_v_4856_);
v_r_4859_ = lean_box(v_res_4858_);
return v_r_4859_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = l_instMonadST(lean_box(0));
return v___x_4860_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; 
v___x_4861_ = lean_box(0);
v___x_4862_ = lean_task_pure(v___x_4861_);
return v___x_4862_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4863_){
_start:
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_251__overap_4868_; lean_object* v___x_4869_; 
v___x_4865_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4866_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__1, &l_panic___at___00Std_Channel_send_spec__0___closed__1_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__1);
v___x_4867_ = l_instInhabitedOfMonad___redArg(v___x_4865_, v___x_4866_);
v___x_251__overap_4868_ = lean_panic_fn(v___x_4867_, v_msg_4863_);
v___x_4869_ = lean_apply_1(v___x_251__overap_4868_, lean_box(0));
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4870_, lean_object* v___y_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4870_);
return v_res_4872_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4876_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4877_ = lean_unsigned_to_nat(21u);
v___x_4878_ = lean_unsigned_to_nat(869u);
v___x_4879_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4880_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4881_ = l_mkPanicMessageWithDecl(v___x_4880_, v___x_4879_, v___x_4878_, v___x_4877_, v___x_4876_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4882_){
_start:
{
if (lean_obj_tag(v_x_4882_) == 0)
{
lean_object* v___x_4884_; lean_object* v___x_4885_; 
v___x_4884_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4885_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4884_);
return v___x_4885_;
}
else
{
lean_object* v___x_4886_; 
v___x_4886_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4887_, lean_object* v___y_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l_Std_Channel_send___redArg___lam__0(v_x_4887_);
lean_dec_ref(v_x_4887_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4891_, lean_object* v_v_4892_){
_start:
{
lean_object* v___x_4894_; lean_object* v___f_4895_; lean_object* v___x_4896_; uint8_t v___x_4897_; lean_object* v___x_4898_; 
v___x_4894_ = l_Std_CloseableChannel_send___redArg(v_ch_4891_, v_v_4892_);
v___f_4895_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4896_ = lean_unsigned_to_nat(0u);
v___x_4897_ = 1;
v___x_4898_ = lean_io_bind_task(v___x_4894_, v___f_4895_, v___x_4896_, v___x_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4899_, lean_object* v_v_4900_, lean_object* v_a_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l_Std_Channel_send___redArg(v_ch_4899_, v_v_4900_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_4903_, lean_object* v_ch_4904_, lean_object* v_v_4905_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l_Std_Channel_send___redArg(v_ch_4904_, v_v_4905_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_4908_, lean_object* v_ch_4909_, lean_object* v_v_4910_, lean_object* v_a_4911_){
_start:
{
lean_object* v_res_4912_; 
v_res_4912_ = l_Std_Channel_send(v_00_u03b1_4908_, v_ch_4909_, v_v_4910_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_4913_){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4913_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_4916_, lean_object* v_a_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Std_Channel_tryRecv___redArg(v_ch_4916_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_4919_, lean_object* v_ch_4920_){
_start:
{
lean_object* v___x_4922_; 
v___x_4922_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4920_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_4923_, lean_object* v_ch_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Std_Channel_tryRecv(v_00_u03b1_4923_, v_ch_4924_);
return v_res_4926_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4928_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4929_ = lean_unsigned_to_nat(16u);
v___x_4930_ = lean_unsigned_to_nat(880u);
v___x_4931_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_4932_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4933_ = l_mkPanicMessageWithDecl(v___x_4932_, v___x_4931_, v___x_4930_, v___x_4929_, v___x_4928_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_4934_, lean_object* v_x_4935_){
_start:
{
if (lean_obj_tag(v_x_4935_) == 0)
{
lean_object* v___x_4937_; lean_object* v___x_250__overap_4938_; lean_object* v___x_4939_; 
v___x_4937_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_250__overap_4938_ = l_panic___redArg(v___x_4934_, v___x_4937_);
v___x_4939_ = lean_apply_1(v___x_250__overap_4938_, lean_box(0));
return v___x_4939_;
}
else
{
lean_object* v_val_4940_; lean_object* v___x_4941_; 
lean_dec_ref(v___x_4934_);
v_val_4940_ = lean_ctor_get(v_x_4935_, 0);
lean_inc(v_val_4940_);
lean_dec_ref(v_x_4935_);
v___x_4941_ = lean_task_pure(v_val_4940_);
return v___x_4941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_4942_, lean_object* v_x_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Std_Channel_recv___redArg___lam__0(v___x_4942_, v_x_4943_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_4946_, lean_object* v_ch_4947_){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___f_4953_; lean_object* v___x_4954_; uint8_t v___x_4955_; lean_object* v___x_4956_; 
v___x_4949_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4950_ = l_Std_CloseableChannel_recv___redArg(v_ch_4947_);
v___x_4951_ = lean_task_pure(v_inst_4946_);
v___x_4952_ = l_instInhabitedOfMonad___redArg(v___x_4949_, v___x_4951_);
v___f_4953_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4953_, 0, v___x_4952_);
v___x_4954_ = lean_unsigned_to_nat(0u);
v___x_4955_ = 1;
v___x_4956_ = lean_io_bind_task(v___x_4950_, v___f_4953_, v___x_4954_, v___x_4955_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_4957_, lean_object* v_ch_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l_Std_Channel_recv___redArg(v_inst_4957_, v_ch_4958_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_4961_, lean_object* v_inst_4962_, lean_object* v_ch_4963_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Std_Channel_recv___redArg(v_inst_4962_, v_ch_4963_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_4966_, lean_object* v_inst_4967_, lean_object* v_ch_4968_, lean_object* v_a_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Std_Channel_recv(v_00_u03b1_4966_, v_inst_4967_, v_ch_4968_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_4971_){
_start:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4973_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4971_);
v___x_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4973_);
v___x_4975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4974_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_4976_);
return v_res_4978_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4982_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_4983_ = lean_unsigned_to_nat(14u);
v___x_4984_ = lean_unsigned_to_nat(22u);
v___x_4985_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_4986_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_4987_ = l_mkPanicMessageWithDecl(v___x_4986_, v___x_4985_, v___x_4984_, v___x_4983_, v___x_4982_);
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_4988_, lean_object* v_inst_4989_, lean_object* v_x_4990_){
_start:
{
lean_object* v___y_4993_; lean_object* v___y_4997_; 
if (lean_obj_tag(v_x_4990_) == 0)
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
lean_dec(v_inst_4989_);
v___x_4999_ = lean_box(0);
v___x_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
return v___x_5000_;
}
else
{
lean_object* v_val_5001_; 
v_val_5001_ = lean_ctor_get(v_x_4990_, 0);
lean_inc(v_val_5001_);
lean_dec_ref(v_x_4990_);
if (lean_obj_tag(v_val_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec(v_inst_4989_);
v_a_5002_ = lean_ctor_get(v_val_5001_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v_val_5001_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v_val_5001_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v_val_5001_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
v___y_4993_ = v___x_5007_;
goto v___jp_4992_;
}
}
}
else
{
lean_object* v_a_5010_; 
v_a_5010_ = lean_ctor_get(v_val_5001_, 0);
lean_inc(v_a_5010_);
lean_dec_ref(v_val_5001_);
if (lean_obj_tag(v_a_5010_) == 0)
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5012_ = l_panic___redArg(v_inst_4989_, v___x_5011_);
v___y_4997_ = v___x_5012_;
goto v___jp_4996_;
}
else
{
lean_object* v_val_5013_; 
lean_dec(v_inst_4989_);
v_val_5013_ = lean_ctor_get(v_a_5010_, 0);
lean_inc(v_val_5013_);
lean_dec_ref(v_a_5010_);
v___y_4997_ = v_val_5013_;
goto v___jp_4996_;
}
}
}
v___jp_4992_:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4994_ = lean_io_promise_resolve(v___y_4993_, v_promise_4988_);
v___x_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
return v___x_4995_;
}
v___jp_4996_:
{
lean_object* v___x_4998_; 
v___x_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4998_, 0, v___y_4997_);
v___y_4993_ = v___x_4998_;
goto v___jp_4992_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5014_, lean_object* v_inst_5015_, lean_object* v_x_5016_, lean_object* v___y_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5014_, v_inst_5015_, v_x_5016_);
lean_dec(v_promise_5014_);
return v_res_5018_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5019_, lean_object* v___f_5020_, lean_object* v_x_5021_){
_start:
{
lean_object* v_val_5024_; 
if (lean_obj_tag(v_x_5021_) == 0)
{
lean_object* v___x_5026_; 
lean_dec_ref(v___f_5020_);
v___x_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5026_, 0, v_x_5021_);
return v___x_5026_;
}
else
{
lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5042_; 
v_isSharedCheck_5042_ = !lean_is_exclusive(v_x_5021_);
if (v_isSharedCheck_5042_ == 0)
{
lean_object* v_unused_5043_; 
v_unused_5043_ = lean_ctor_get(v_x_5021_, 0);
lean_dec(v_unused_5043_);
v___x_5028_ = v_x_5021_;
v_isShared_5029_ = v_isSharedCheck_5042_;
goto v_resetjp_5027_;
}
else
{
lean_dec(v_x_5021_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5042_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5030_; lean_object* v___x_5031_; uint8_t v___x_5032_; lean_object* v___x_5033_; 
v___x_5030_ = lean_io_promise_result_opt(v_a_5019_);
v___x_5031_ = lean_unsigned_to_nat(0u);
v___x_5032_ = 1;
v___x_5033_ = l_EIO_chainTask___redArg(v___x_5030_, v___f_5020_, v___x_5031_, v___x_5032_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_a_5034_; lean_object* v___x_5036_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5034_);
lean_dec_ref(v___x_5033_);
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 0, v_a_5034_);
v___x_5036_ = v___x_5028_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5034_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
v_val_5024_ = v___x_5036_;
goto v___jp_5023_;
}
}
else
{
lean_object* v_a_5038_; lean_object* v___x_5040_; 
v_a_5038_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5038_);
lean_dec_ref(v___x_5033_);
if (v_isShared_5029_ == 0)
{
lean_ctor_set_tag(v___x_5028_, 0);
lean_ctor_set(v___x_5028_, 0, v_a_5038_);
v___x_5040_ = v___x_5028_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5038_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
v_val_5024_ = v___x_5040_;
goto v___jp_5023_;
}
}
}
}
v___jp_5023_:
{
lean_object* v___x_5025_; 
v___x_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5025_, 0, v_val_5024_);
return v___x_5025_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5044_, lean_object* v___f_5045_, lean_object* v_x_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v_res_5048_; 
v_res_5048_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5044_, v___f_5045_, v_x_5046_);
lean_dec(v_a_5044_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5049_, lean_object* v_finished_5050_, lean_object* v___f_5051_, lean_object* v_x_5052_){
_start:
{
if (lean_obj_tag(v_x_5052_) == 0)
{
lean_object* v_a_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5062_; 
lean_dec_ref(v___f_5051_);
lean_dec(v_finished_5050_);
lean_dec_ref(v_sel_5049_);
v_a_5054_ = lean_ctor_get(v_x_5052_, 0);
v_isSharedCheck_5062_ = !lean_is_exclusive(v_x_5052_);
if (v_isSharedCheck_5062_ == 0)
{
v___x_5056_ = v_x_5052_;
v_isShared_5057_ = v_isSharedCheck_5062_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_a_5054_);
lean_dec(v_x_5052_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5062_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5059_; 
if (v_isShared_5057_ == 0)
{
v___x_5059_ = v___x_5056_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_a_5054_);
v___x_5059_ = v_reuseFailAlloc_5061_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
lean_object* v___x_5060_; 
v___x_5060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5060_, 0, v___x_5059_);
return v___x_5060_;
}
}
}
else
{
lean_object* v_a_5063_; lean_object* v_registerFn_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___f_5067_; lean_object* v___x_5068_; uint8_t v___x_5069_; lean_object* v___x_5070_; 
v_a_5063_ = lean_ctor_get(v_x_5052_, 0);
lean_inc(v_a_5063_);
lean_dec_ref(v_x_5052_);
v_registerFn_5064_ = lean_ctor_get(v_sel_5049_, 1);
lean_inc_ref(v_registerFn_5064_);
lean_dec_ref(v_sel_5049_);
lean_inc(v_a_5063_);
v___x_5065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5065_, 0, v_finished_5050_);
lean_ctor_set(v___x_5065_, 1, v_a_5063_);
v___x_5066_ = lean_apply_2(v_registerFn_5064_, v___x_5065_, lean_box(0));
v___f_5067_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5067_, 0, v_a_5063_);
lean_closure_set(v___f_5067_, 1, v___f_5051_);
v___x_5068_ = lean_unsigned_to_nat(0u);
v___x_5069_ = 0;
v___x_5070_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5068_, v___x_5069_, v___x_5066_, v___f_5067_);
return v___x_5070_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5071_, lean_object* v_finished_5072_, lean_object* v___f_5073_, lean_object* v_x_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5071_, v_finished_5072_, v___f_5073_, v_x_5074_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5077_, lean_object* v_sel_5078_, lean_object* v_waiter_5079_){
_start:
{
lean_object* v___x_5081_; lean_object* v_finished_5082_; lean_object* v_promise_5083_; lean_object* v___f_5084_; lean_object* v___f_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; uint8_t v___x_5089_; lean_object* v___x_5090_; 
v___x_5081_ = lean_io_promise_new();
v_finished_5082_ = lean_ctor_get(v_waiter_5079_, 0);
lean_inc(v_finished_5082_);
v_promise_5083_ = lean_ctor_get(v_waiter_5079_, 1);
lean_inc(v_promise_5083_);
lean_dec_ref(v_waiter_5079_);
v___f_5084_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5084_, 0, v_promise_5083_);
lean_closure_set(v___f_5084_, 1, v_inst_5077_);
v___f_5085_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5085_, 0, v_sel_5078_);
lean_closure_set(v___f_5085_, 1, v_finished_5082_);
lean_closure_set(v___f_5085_, 2, v___f_5084_);
v___x_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5086_, 0, v___x_5081_);
v___x_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5087_, 0, v___x_5086_);
v___x_5088_ = lean_unsigned_to_nat(0u);
v___x_5089_ = 0;
v___x_5090_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5088_, v___x_5089_, v___x_5087_, v___f_5085_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5091_, lean_object* v_sel_5092_, lean_object* v_waiter_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5091_, v_sel_5092_, v_waiter_5093_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5096_, lean_object* v_ch_5097_){
_start:
{
lean_object* v_sel_5098_; lean_object* v_unregisterFn_5099_; lean_object* v___f_5100_; lean_object* v___f_5101_; lean_object* v___x_5102_; 
lean_inc_ref(v_ch_5097_);
v_sel_5098_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5097_);
v_unregisterFn_5099_ = lean_ctor_get(v_sel_5098_, 2);
lean_inc_ref(v_unregisterFn_5099_);
v___f_5100_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5100_, 0, v_ch_5097_);
v___f_5101_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5101_, 0, v_inst_5096_);
lean_closure_set(v___f_5101_, 1, v_sel_5098_);
v___x_5102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5102_, 0, v___f_5100_);
lean_ctor_set(v___x_5102_, 1, v___f_5101_);
lean_ctor_set(v___x_5102_, 2, v_unregisterFn_5099_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5103_, lean_object* v_inst_5104_, lean_object* v_ch_5105_){
_start:
{
lean_object* v___x_5106_; 
v___x_5106_ = l_Std_Channel_recvSelector___redArg(v_inst_5104_, v_ch_5105_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5107_, lean_object* v_inst_5108_, lean_object* v_ch_5109_, lean_object* v_prio_5110_, lean_object* v_v_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5107_, v_inst_5108_, v_ch_5109_, v_prio_5110_, v_v_5111_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5114_, lean_object* v_f_5115_, lean_object* v_ch_5116_, lean_object* v_prio_5117_){
_start:
{
lean_object* v___x_5119_; lean_object* v___f_5120_; uint8_t v___x_5121_; lean_object* v___x_5122_; 
lean_inc_ref(v_ch_5116_);
lean_inc(v_inst_5114_);
v___x_5119_ = l_Std_Channel_recv___redArg(v_inst_5114_, v_ch_5116_);
lean_inc(v_prio_5117_);
v___f_5120_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5120_, 0, v_f_5115_);
lean_closure_set(v___f_5120_, 1, v_inst_5114_);
lean_closure_set(v___f_5120_, 2, v_ch_5116_);
lean_closure_set(v___f_5120_, 3, v_prio_5117_);
v___x_5121_ = 0;
v___x_5122_ = lean_io_bind_task(v___x_5119_, v___f_5120_, v_prio_5117_, v___x_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5123_, lean_object* v_inst_5124_, lean_object* v_ch_5125_, lean_object* v_prio_5126_, lean_object* v_v_5127_){
_start:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; 
lean_inc_ref(v_f_5123_);
v___x_5129_ = lean_apply_2(v_f_5123_, v_v_5127_, lean_box(0));
v___x_5130_ = l_Std_Channel_forAsync___redArg(v_inst_5124_, v_f_5123_, v_ch_5125_, v_prio_5126_);
return v___x_5130_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5131_, lean_object* v_f_5132_, lean_object* v_ch_5133_, lean_object* v_prio_5134_, lean_object* v_a_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Std_Channel_forAsync___redArg(v_inst_5131_, v_f_5132_, v_ch_5133_, v_prio_5134_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5137_, lean_object* v_inst_5138_, lean_object* v_f_5139_, lean_object* v_ch_5140_, lean_object* v_prio_5141_){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = l_Std_Channel_forAsync___redArg(v_inst_5138_, v_f_5139_, v_ch_5140_, v_prio_5141_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5144_, lean_object* v_inst_5145_, lean_object* v_f_5146_, lean_object* v_ch_5147_, lean_object* v_prio_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Std_Channel_forAsync(v_00_u03b1_5144_, v_inst_5145_, v_f_5146_, v_ch_5147_, v_prio_5148_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5151_, lean_object* v_channel_5152_){
_start:
{
lean_object* v___x_5153_; 
v___x_5153_ = l_Std_Channel_recvSelector___redArg(v_inst_5151_, v_channel_5152_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5154_){
_start:
{
lean_object* v___f_5155_; lean_object* v___f_5156_; lean_object* v___x_5157_; 
v___f_5155_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5155_, 0, v_inst_5154_);
v___f_5156_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1));
v___x_5157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5157_, 0, v___f_5155_);
lean_ctor_set(v___x_5157_, 1, v___f_5156_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5158_, lean_object* v_inst_5159_){
_start:
{
lean_object* v___x_5160_; 
v___x_5160_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5159_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5161_){
_start:
{
lean_object* v___x_5162_; 
v___x_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5162_, 0, v_a_5161_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5163_, lean_object* v_x_5164_){
_start:
{
if (lean_obj_tag(v_x_5164_) == 0)
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5174_; 
lean_dec_ref(v___f_5163_);
v_a_5166_ = lean_ctor_get(v_x_5164_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v_x_5164_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5168_ = v_x_5164_;
v_isShared_5169_ = v_isSharedCheck_5174_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v_x_5164_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5174_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5171_; 
if (v_isShared_5169_ == 0)
{
v___x_5171_ = v___x_5168_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5166_);
v___x_5171_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
lean_object* v___x_5172_; 
v___x_5172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5171_);
return v___x_5172_;
}
}
}
else
{
lean_object* v_a_5175_; 
v_a_5175_ = lean_ctor_get(v_x_5164_, 0);
lean_inc(v_a_5175_);
lean_dec_ref(v_x_5164_);
if (lean_obj_tag(v_a_5175_) == 0)
{
lean_object* v_a_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5184_; 
lean_dec_ref(v___f_5163_);
v_a_5176_ = lean_ctor_get(v_a_5175_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v_a_5175_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5178_ = v_a_5175_;
v_isShared_5179_ = v_isSharedCheck_5184_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_a_5176_);
lean_dec(v_a_5175_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5184_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5181_; 
if (v_isShared_5179_ == 0)
{
v___x_5181_ = v___x_5178_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5176_);
v___x_5181_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
lean_object* v___x_5182_; 
v___x_5182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5182_, 0, v___x_5181_);
return v___x_5182_;
}
}
}
else
{
lean_object* v_a_5185_; lean_object* v___x_5186_; uint8_t v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; 
v_a_5185_ = lean_ctor_get(v_a_5175_, 0);
lean_inc(v_a_5185_);
lean_dec_ref(v_a_5175_);
v___x_5186_ = lean_unsigned_to_nat(0u);
v___x_5187_ = 0;
v___x_5188_ = lean_task_map(v___f_5163_, v_a_5185_, v___x_5186_, v___x_5187_);
v___x_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5188_);
return v___x_5189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5190_, lean_object* v_x_5191_, lean_object* v___y_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5190_, v_x_5191_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5194_, lean_object* v___f_5195_, lean_object* v_receiver_5196_){
_start:
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; uint8_t v___x_5203_; lean_object* v___x_5204_; 
v___x_5198_ = l_Std_Channel_recv___redArg(v_inst_5194_, v_receiver_5196_);
v___x_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5198_);
v___x_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5199_);
v___x_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
v___x_5202_ = lean_unsigned_to_nat(0u);
v___x_5203_ = 0;
v___x_5204_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5202_, v___x_5203_, v___x_5201_, v___f_5195_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5205_, lean_object* v___f_5206_, lean_object* v_receiver_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5205_, v___f_5206_, v_receiver_5207_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5213_){
_start:
{
lean_object* v___f_5214_; lean_object* v___f_5215_; 
v___f_5214_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5215_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5215_, 0, v_inst_5213_);
lean_closure_set(v___f_5215_, 1, v___f_5214_);
return v___f_5215_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5216_, lean_object* v_inst_5217_){
_start:
{
lean_object* v___x_5218_; 
v___x_5218_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5217_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__0(lean_object* v_a_5219_){
_start:
{
lean_object* v___x_5220_; 
v___x_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5220_, 0, v_a_5219_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_5221_, lean_object* v_x_5222_){
_start:
{
if (lean_obj_tag(v_x_5222_) == 0)
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5232_; 
lean_dec_ref(v___f_5221_);
v_a_5224_ = lean_ctor_get(v_x_5222_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v_x_5222_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5226_ = v_x_5222_;
v_isShared_5227_ = v_isSharedCheck_5232_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v_x_5222_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5232_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5229_; 
if (v_isShared_5227_ == 0)
{
v___x_5229_ = v___x_5226_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5224_);
v___x_5229_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
lean_object* v___x_5230_; 
v___x_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5229_);
return v___x_5230_;
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5234_; uint8_t v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
v_a_5233_ = lean_ctor_get(v_x_5222_, 0);
lean_inc(v_a_5233_);
lean_dec_ref(v_x_5222_);
v___x_5234_ = lean_unsigned_to_nat(0u);
v___x_5235_ = 0;
v___x_5236_ = lean_task_map(v___f_5221_, v_a_5233_, v___x_5234_, v___x_5235_);
v___x_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5236_);
return v___x_5237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_5238_, lean_object* v_x_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v_res_5241_; 
v_res_5241_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__1(v___f_5238_, v_x_5239_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5242_, lean_object* v_receiver_5243_, lean_object* v_x_5244_){
_start:
{
lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; uint8_t v___x_5250_; lean_object* v___x_5251_; 
v___x_5246_ = l_Std_Channel_send___redArg(v_receiver_5243_, v_x_5244_);
v___x_5247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5247_, 0, v___x_5246_);
v___x_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5247_);
v___x_5249_ = lean_unsigned_to_nat(0u);
v___x_5250_ = 0;
v___x_5251_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5249_, v___x_5250_, v___x_5248_, v___f_5242_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5252_, lean_object* v_receiver_5253_, lean_object* v_x_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__2(v___f_5252_, v_receiver_5253_, v_x_5254_);
return v_res_5256_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_5262_; lean_object* v___f_5263_; lean_object* v___f_5264_; 
v___x_5262_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_5263_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___f_5264_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5264_, 0, v___f_5263_);
lean_closure_set(v___f_5264_, 1, v___x_5262_);
return v___f_5264_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___f_5265_; lean_object* v___f_5266_; lean_object* v___f_5267_; lean_object* v___x_5268_; 
v___f_5265_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_5266_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3);
v___f_5267_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___x_5268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5268_, 0, v___f_5267_);
lean_ctor_set(v___x_5268_, 1, v___f_5266_);
lean_ctor_set(v___x_5268_, 2, v___f_5265_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5269_, lean_object* v_inst_5270_){
_start:
{
lean_object* v___x_5271_; 
v___x_5271_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4);
return v___x_5271_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5272_, lean_object* v_inst_5273_){
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5272_, v_inst_5273_);
lean_dec(v_inst_5273_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5275_){
_start:
{
lean_inc_ref(v_ch_5275_);
return v_ch_5275_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5276_){
_start:
{
lean_object* v_res_5277_; 
v_res_5277_ = l_Std_Channel_sync___redArg(v_ch_5276_);
lean_dec_ref(v_ch_5276_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5278_, lean_object* v_ch_5279_){
_start:
{
lean_inc_ref(v_ch_5279_);
return v_ch_5279_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5280_, lean_object* v_ch_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Std_Channel_sync(v_00_u03b1_5280_, v_ch_5281_);
lean_dec_ref(v_ch_5281_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5283_){
_start:
{
lean_object* v___x_5285_; 
v___x_5285_ = l_Std_CloseableChannel_new___redArg(v_capacity_5283_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5286_, lean_object* v_a_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Std_Channel_Sync_new___redArg(v_capacity_5286_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5289_, lean_object* v_capacity_5290_){
_start:
{
lean_object* v___x_5292_; 
v___x_5292_ = l_Std_CloseableChannel_new___redArg(v_capacity_5290_);
return v___x_5292_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5293_, lean_object* v_capacity_5294_, lean_object* v_a_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l_Std_Channel_Sync_new(v_00_u03b1_5293_, v_capacity_5294_);
return v_res_5296_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5297_, lean_object* v_v_5298_){
_start:
{
uint8_t v___x_5300_; 
v___x_5300_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5297_, v_v_5298_);
return v___x_5300_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5301_, lean_object* v_v_5302_, lean_object* v_a_5303_){
_start:
{
uint8_t v_res_5304_; lean_object* v_r_5305_; 
v_res_5304_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5301_, v_v_5302_);
v_r_5305_ = lean_box(v_res_5304_);
return v_r_5305_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5306_, lean_object* v_ch_5307_, lean_object* v_v_5308_){
_start:
{
uint8_t v___x_5310_; 
v___x_5310_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5307_, v_v_5308_);
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5311_, lean_object* v_ch_5312_, lean_object* v_v_5313_, lean_object* v_a_5314_){
_start:
{
uint8_t v_res_5315_; lean_object* v_r_5316_; 
v_res_5315_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5311_, v_ch_5312_, v_v_5313_);
v_r_5316_ = lean_box(v_res_5315_);
return v_r_5316_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5317_, lean_object* v_v_5318_){
_start:
{
lean_object* v___x_5320_; lean_object* v___x_5321_; 
v___x_5320_ = l_Std_Channel_send___redArg(v_ch_5317_, v_v_5318_);
v___x_5321_ = lean_io_wait(v___x_5320_);
return v___x_5321_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5322_, lean_object* v_v_5323_, lean_object* v_a_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l_Std_Channel_Sync_send___redArg(v_ch_5322_, v_v_5323_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5326_, lean_object* v_ch_5327_, lean_object* v_v_5328_){
_start:
{
lean_object* v___x_5330_; 
v___x_5330_ = l_Std_Channel_Sync_send___redArg(v_ch_5327_, v_v_5328_);
return v___x_5330_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5331_, lean_object* v_ch_5332_, lean_object* v_v_5333_, lean_object* v_a_5334_){
_start:
{
lean_object* v_res_5335_; 
v_res_5335_ = l_Std_Channel_Sync_send(v_00_u03b1_5331_, v_ch_5332_, v_v_5333_);
return v_res_5335_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5336_){
_start:
{
lean_object* v___x_5338_; 
v___x_5338_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5336_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5339_, lean_object* v_a_5340_){
_start:
{
lean_object* v_res_5341_; 
v_res_5341_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5339_);
return v_res_5341_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5342_, lean_object* v_ch_5343_){
_start:
{
lean_object* v___x_5345_; 
v___x_5345_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5343_);
return v___x_5345_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5346_, lean_object* v_ch_5347_, lean_object* v_a_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5346_, v_ch_5347_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5350_, lean_object* v_ch_5351_){
_start:
{
lean_object* v___x_5353_; lean_object* v___x_5354_; 
v___x_5353_ = l_Std_Channel_recv___redArg(v_inst_5350_, v_ch_5351_);
v___x_5354_ = lean_io_wait(v___x_5353_);
return v___x_5354_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5355_, lean_object* v_ch_5356_, lean_object* v_a_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Std_Channel_Sync_recv___redArg(v_inst_5355_, v_ch_5356_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5359_, lean_object* v_inst_5360_, lean_object* v_ch_5361_){
_start:
{
lean_object* v___x_5363_; 
v___x_5363_ = l_Std_Channel_Sync_recv___redArg(v_inst_5360_, v_ch_5361_);
return v___x_5363_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5364_, lean_object* v_inst_5365_, lean_object* v_ch_5366_, lean_object* v_a_5367_){
_start:
{
lean_object* v_res_5368_; 
v_res_5368_ = l_Std_Channel_Sync_recv(v_00_u03b1_5364_, v_inst_5365_, v_ch_5366_);
return v_res_5368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5369_, lean_object* v_b_5370_, lean_object* v_toBind_5371_, lean_object* v___f_5372_, lean_object* v_a_5373_){
_start:
{
lean_object* v___x_5374_; lean_object* v___x_5375_; 
v___x_5374_ = lean_apply_2(v_f_5369_, v_a_5373_, v_b_5370_);
v___x_5375_ = lean_apply_4(v_toBind_5371_, lean_box(0), lean_box(0), v___x_5374_, v___f_5372_);
return v___x_5375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5376_, lean_object* v_inst_5377_, lean_object* v_inst_5378_, lean_object* v_ch_5379_, lean_object* v_f_5380_, lean_object* v_b_5381_){
_start:
{
lean_object* v_toApplicative_5382_; lean_object* v_toBind_5383_; lean_object* v_toPure_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___f_5387_; lean_object* v___f_5388_; lean_object* v___x_5389_; 
v_toApplicative_5382_ = lean_ctor_get(v_inst_5377_, 0);
v_toBind_5383_ = lean_ctor_get(v_inst_5377_, 1);
lean_inc(v_toBind_5383_);
v_toPure_5384_ = lean_ctor_get(v_toApplicative_5382_, 1);
lean_inc(v_toPure_5384_);
lean_inc_ref(v_ch_5379_);
lean_inc(v_inst_5376_);
v___x_5385_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5385_, 0, lean_box(0));
lean_closure_set(v___x_5385_, 1, v_inst_5376_);
lean_closure_set(v___x_5385_, 2, v_ch_5379_);
lean_inc(v_inst_5378_);
v___x_5386_ = lean_apply_2(v_inst_5378_, lean_box(0), v___x_5385_);
lean_inc(v_f_5380_);
v___f_5387_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5387_, 0, v_toPure_5384_);
lean_closure_set(v___f_5387_, 1, v_inst_5376_);
lean_closure_set(v___f_5387_, 2, v_inst_5377_);
lean_closure_set(v___f_5387_, 3, v_inst_5378_);
lean_closure_set(v___f_5387_, 4, v_ch_5379_);
lean_closure_set(v___f_5387_, 5, v_f_5380_);
lean_inc(v_toBind_5383_);
v___f_5388_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5388_, 0, v_f_5380_);
lean_closure_set(v___f_5388_, 1, v_b_5381_);
lean_closure_set(v___f_5388_, 2, v_toBind_5383_);
lean_closure_set(v___f_5388_, 3, v___f_5387_);
v___x_5389_ = lean_apply_4(v_toBind_5383_, lean_box(0), lean_box(0), v___x_5386_, v___f_5388_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5390_, lean_object* v_inst_5391_, lean_object* v_inst_5392_, lean_object* v_inst_5393_, lean_object* v_ch_5394_, lean_object* v_f_5395_, lean_object* v_____do__lift_5396_){
_start:
{
if (lean_obj_tag(v_____do__lift_5396_) == 0)
{
lean_object* v_a_5397_; lean_object* v___x_5398_; 
lean_dec(v_f_5395_);
lean_dec_ref(v_ch_5394_);
lean_dec(v_inst_5393_);
lean_dec_ref(v_inst_5392_);
lean_dec(v_inst_5391_);
v_a_5397_ = lean_ctor_get(v_____do__lift_5396_, 0);
lean_inc(v_a_5397_);
lean_dec_ref(v_____do__lift_5396_);
v___x_5398_ = lean_apply_2(v_toPure_5390_, lean_box(0), v_a_5397_);
return v___x_5398_;
}
else
{
lean_object* v_a_5399_; lean_object* v___x_5400_; 
lean_dec(v_toPure_5390_);
v_a_5399_ = lean_ctor_get(v_____do__lift_5396_, 0);
lean_inc(v_a_5399_);
lean_dec_ref(v_____do__lift_5396_);
v___x_5400_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5391_, v_inst_5392_, v_inst_5393_, v_ch_5394_, v_f_5395_, v_a_5399_);
return v___x_5400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5401_, lean_object* v_m_5402_, lean_object* v_00_u03b2_5403_, lean_object* v_inst_5404_, lean_object* v_inst_5405_, lean_object* v_inst_5406_, lean_object* v_ch_5407_, lean_object* v_f_5408_, lean_object* v_b_5409_){
_start:
{
lean_object* v___x_5410_; 
v___x_5410_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5404_, v_inst_5405_, v_inst_5406_, v_ch_5407_, v_f_5408_, v_b_5409_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5411_, lean_object* v_inst_5412_, lean_object* v_inst_5413_, lean_object* v_ch_5414_, lean_object* v_b_5415_, lean_object* v_f_5416_){
_start:
{
lean_object* v___x_5417_; 
v___x_5417_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5411_, v_inst_5412_, v_inst_5413_, v_ch_5414_, v_f_5416_, v_b_5415_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5418_, lean_object* v_m_5419_, lean_object* v_inst_5420_, lean_object* v_inst_5421_, lean_object* v_inst_5422_, lean_object* v_00_u03b2_5423_, lean_object* v_ch_5424_, lean_object* v_b_5425_, lean_object* v_f_5426_){
_start:
{
lean_object* v___x_5427_; 
v___x_5427_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5420_, v_inst_5421_, v_inst_5422_, v_ch_5424_, v_f_5426_, v_b_5425_);
return v___x_5427_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5428_, lean_object* v_inst_5429_, lean_object* v_inst_5430_, lean_object* v_00_u03b2_5431_, lean_object* v_ch_5432_, lean_object* v_b_5433_, lean_object* v_f_5434_){
_start:
{
lean_object* v___x_5435_; 
v___x_5435_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5428_, v_inst_5429_, v_inst_5430_, v_ch_5432_, v_f_5434_, v_b_5433_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5436_, lean_object* v_inst_5437_, lean_object* v_inst_5438_){
_start:
{
lean_object* v___f_5439_; 
v___f_5439_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5439_, 0, v_inst_5436_);
lean_closure_set(v___f_5439_, 1, v_inst_5437_);
lean_closure_set(v___f_5439_, 2, v_inst_5438_);
return v___f_5439_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5440_, lean_object* v_m_5441_, lean_object* v_inst_5442_, lean_object* v_inst_5443_, lean_object* v_inst_5444_){
_start:
{
lean_object* v___f_5445_; 
v___f_5445_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5445_, 0, v_inst_5442_);
lean_closure_set(v___f_5445_, 1, v_inst_5443_);
lean_closure_set(v___f_5445_, 2, v_inst_5444_);
return v___f_5445_;
}
}
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Async_IO(uint8_t builtin);
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
res = runtime_initialize_Std_Internal_Async_IO(builtin);
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
lean_object* initialize_Std_Internal_Async_IO(uint8_t builtin);
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
res = initialize_Std_Internal_Async_IO(builtin);
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

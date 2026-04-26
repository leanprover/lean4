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
lean_object* v_ref_445_; lean_object* v_mutex_446_; lean_object* v___x_447_; lean_object* v_r_448_; 
v_ref_445_ = lean_ctor_get(v_mutex_442_, 0);
lean_inc(v_ref_445_);
v_mutex_446_ = lean_ctor_get(v_mutex_442_, 1);
lean_inc(v_mutex_446_);
lean_dec_ref(v_mutex_442_);
v___x_447_ = lean_io_basemutex_lock(v_mutex_446_);
v_r_448_ = lean_apply_2(v_k_443_, v_ref_445_, lean_box(0));
if (lean_obj_tag(v_r_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_a_449_ = lean_ctor_get(v_r_448_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_r_448_);
if (v_isSharedCheck_457_ == 0)
{
v___x_451_ = v_r_448_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v_r_448_);
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
v_a_458_ = lean_ctor_get(v_r_448_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_r_448_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v_r_448_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v_r_448_);
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
lean_inc(v_a_609_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_634_, lean_object* v_a_635_, lean_object* v_inst_636_, lean_object* v_toBind_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(v_toApplicative_634_, v_a_635_, v_inst_636_, v_toBind_637_, v_a_638_);
lean_dec(v_a_635_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_toApplicative_643_; lean_object* v_toBind_644_; lean_object* v___f_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_toApplicative_643_ = lean_ctor_get(v_inst_640_, 0);
lean_inc_ref(v_toApplicative_643_);
v_toBind_644_ = lean_ctor_get(v_inst_640_, 1);
lean_inc_n(v_toBind_644_, 2);
lean_dec_ref(v_inst_640_);
lean_inc(v_inst_641_);
lean_inc_n(v_a_642_, 2);
v___f_645_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_645_, 0, v_toApplicative_643_);
lean_closure_set(v___f_645_, 1, v_a_642_);
lean_closure_set(v___f_645_, 2, v_inst_641_);
lean_closure_set(v___f_645_, 3, v_toBind_644_);
v___x_646_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_646_, 0, lean_box(0));
lean_closure_set(v___x_646_, 1, lean_box(0));
lean_closure_set(v___x_646_, 2, v_a_642_);
v___x_647_ = lean_apply_2(v_inst_641_, lean_box(0), v___x_646_);
v___x_648_ = lean_apply_4(v_toBind_644_, lean_box(0), lean_box(0), v___x_647_, v___f_645_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_649_, v_inst_650_, v_a_651_);
lean_dec(v_a_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object* v_m_653_, lean_object* v_00_u03b1_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_655_, v_inst_656_, v_a_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___boxed(lean_object* v_m_659_, lean_object* v_00_u03b1_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(v_m_659_, v_00_u03b1_660_, v_inst_661_, v_inst_662_, v_a_663_);
lean_dec(v_a_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(lean_object* v_a_665_){
_start:
{
lean_object* v___x_667_; lean_object* v_values_668_; lean_object* v_consumers_669_; uint8_t v_closed_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_690_; 
v___x_667_ = lean_st_ref_get(v_a_665_);
v_values_668_ = lean_ctor_get(v___x_667_, 0);
v_consumers_669_ = lean_ctor_get(v___x_667_, 1);
v_closed_670_ = lean_ctor_get_uint8(v___x_667_, sizeof(void*)*2);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_690_ == 0)
{
v___x_672_ = v___x_667_;
v_isShared_673_ = v_isSharedCheck_690_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_consumers_669_);
lean_inc(v_values_668_);
lean_dec(v___x_667_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_690_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_Queue_dequeue_x3f___redArg(v_values_668_);
if (lean_obj_tag(v___x_674_) == 1)
{
lean_object* v_val_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_688_; 
v_val_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_688_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_688_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_val_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_688_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_fst_679_; lean_object* v_snd_680_; lean_object* v___x_682_; 
v_fst_679_ = lean_ctor_get(v_val_675_, 0);
lean_inc(v_fst_679_);
v_snd_680_ = lean_ctor_get(v_val_675_, 1);
lean_inc(v_snd_680_);
lean_dec(v_val_675_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_snd_680_);
v___x_682_ = v___x_672_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_snd_680_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_consumers_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_687_, sizeof(void*)*2, v_closed_670_);
v___x_682_ = v_reuseFailAlloc_687_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_st_ref_set(v_a_665_, v___x_682_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_fst_679_);
v___x_685_ = v___x_677_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_fst_679_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v___x_689_; 
lean_dec(v___x_674_);
lean_del_object(v___x_672_);
lean_dec_ref(v_consumers_669_);
v___x_689_ = lean_box(0);
return v___x_689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_691_);
lean_dec(v_a_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_object* v_00_u03b1_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_698_, lean_object* v_a_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(v_00_u03b1_698_, v_a_699_);
lean_dec(v_a_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(lean_object* v_ch_703_){
_start:
{
lean_object* v___f_705_; lean_object* v___x_706_; 
v___f_705_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0));
v___x_706_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_703_, v___f_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(lean_object* v_ch_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_object* v_00_u03b1_710_, lean_object* v_ch_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(lean_object* v_00_u03b1_714_, lean_object* v_ch_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(v_00_u03b1_714_, v_ch_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v___x_719_; 
v___x_719_ = lean_box(0);
return v___x_719_;
}
else
{
lean_object* v_val_720_; 
v_val_720_ = lean_ctor_get(v_x_718_, 0);
lean_inc(v_val_720_);
return v_val_720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(lean_object* v_x_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(v_x_721_);
lean_dec(v_x_721_);
return v_res_722_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_box(0);
v___x_724_ = lean_task_pure(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(lean_object* v___f_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v___y_726_);
if (lean_obj_tag(v___x_728_) == 1)
{
lean_object* v___x_729_; 
lean_dec_ref(v___f_725_);
v___x_729_ = lean_task_pure(v___x_728_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; uint8_t v_closed_731_; 
lean_dec(v___x_728_);
v___x_730_ = lean_st_ref_get(v___y_726_);
v_closed_731_ = lean_ctor_get_uint8(v___x_730_, sizeof(void*)*2);
lean_dec(v___x_730_);
if (v_closed_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_values_734_; lean_object* v_consumers_735_; uint8_t v_closed_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_750_; 
v___x_732_ = lean_io_promise_new();
v___x_733_ = lean_st_ref_take(v___y_726_);
v_values_734_ = lean_ctor_get(v___x_733_, 0);
v_consumers_735_ = lean_ctor_get(v___x_733_, 1);
v_closed_736_ = lean_ctor_get_uint8(v___x_733_, sizeof(void*)*2);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_750_ == 0)
{
v___x_738_ = v___x_733_;
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_consumers_735_);
lean_inc(v_values_734_);
lean_dec(v___x_733_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_750_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
lean_inc(v___x_732_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_732_);
v___x_741_ = l_Std_Queue_enqueue___redArg(v___x_740_, v_consumers_735_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 1, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_values_734_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_749_, sizeof(void*)*2, v_closed_736_);
v___x_743_ = v_reuseFailAlloc_749_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_744_ = lean_st_ref_set(v___y_726_, v___x_743_);
v___x_745_ = 1;
v___x_746_ = lean_io_promise_result_opt(v___x_732_);
lean_dec(v___x_732_);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_task_map(v___f_725_, v___x_746_, v___x_747_, v___x_745_);
return v___x_748_;
}
}
}
else
{
lean_object* v___x_751_; 
lean_dec_ref(v___f_725_);
v___x_751_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(lean_object* v___f_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(v___f_752_, v___y_753_);
lean_dec(v___y_753_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(lean_object* v_ch_759_){
_start:
{
lean_object* v___f_761_; lean_object* v___x_762_; 
v___f_761_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1));
v___x_762_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_759_, v___f_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(lean_object* v_ch_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_763_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_object* v_00_u03b1_766_, lean_object* v_ch_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(lean_object* v_00_u03b1_770_, lean_object* v_ch_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(v_00_u03b1_770_, v_ch_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_774_, lean_object* v_a_775_){
_start:
{
uint8_t v___y_777_; lean_object* v_values_781_; uint8_t v_closed_782_; uint8_t v___x_783_; 
v_values_781_ = lean_ctor_get(v_a_775_, 0);
v_closed_782_ = lean_ctor_get_uint8(v_a_775_, sizeof(void*)*2);
v___x_783_ = l_Std_Queue_isEmpty___redArg(v_values_781_);
if (v___x_783_ == 0)
{
uint8_t v___x_784_; 
v___x_784_ = 1;
v___y_777_ = v___x_784_;
goto v___jp_776_;
}
else
{
v___y_777_ = v_closed_782_;
goto v___jp_776_;
}
v___jp_776_:
{
lean_object* v_toPure_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_toPure_778_ = lean_ctor_get(v_toApplicative_774_, 1);
lean_inc(v_toPure_778_);
lean_dec_ref(v_toApplicative_774_);
v___x_779_ = lean_box(v___y_777_);
v___x_780_ = lean_apply_2(v_toPure_778_, lean_box(0), v___x_779_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(v_toApplicative_785_, v_a_786_);
lean_dec_ref(v_a_786_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_toApplicative_791_; lean_object* v_toBind_792_; lean_object* v___f_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_toApplicative_791_ = lean_ctor_get(v_inst_788_, 0);
lean_inc_ref(v_toApplicative_791_);
v_toBind_792_ = lean_ctor_get(v_inst_788_, 1);
lean_inc(v_toBind_792_);
lean_dec_ref(v_inst_788_);
v___f_793_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_793_, 0, v_toApplicative_791_);
lean_inc(v_a_790_);
v___x_794_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_794_, 0, lean_box(0));
lean_closure_set(v___x_794_, 1, lean_box(0));
lean_closure_set(v___x_794_, 2, v_a_790_);
v___x_795_ = lean_apply_2(v_inst_789_, lean_box(0), v___x_794_);
v___x_796_ = lean_apply_4(v_toBind_792_, lean_box(0), lean_box(0), v___x_795_, v___f_793_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___boxed(lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(v_inst_797_, v_inst_798_, v_a_799_);
lean_dec(v_a_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object* v_m_801_, lean_object* v_00_u03b1_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_toApplicative_806_; lean_object* v_toBind_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_toApplicative_806_ = lean_ctor_get(v_inst_803_, 0);
lean_inc_ref(v_toApplicative_806_);
v_toBind_807_ = lean_ctor_get(v_inst_803_, 1);
lean_inc(v_toBind_807_);
lean_dec_ref(v_inst_803_);
v___f_808_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_808_, 0, v_toApplicative_806_);
lean_inc(v_a_805_);
v___x_809_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_809_, 0, lean_box(0));
lean_closure_set(v___x_809_, 1, lean_box(0));
lean_closure_set(v___x_809_, 2, v_a_805_);
v___x_810_ = lean_apply_2(v_inst_804_, lean_box(0), v___x_809_);
v___x_811_ = lean_apply_4(v_toBind_807_, lean_box(0), lean_box(0), v___x_810_, v___f_808_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___boxed(lean_object* v_m_812_, lean_object* v_00_u03b1_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(v_m_812_, v_00_u03b1_813_, v_inst_814_, v_inst_815_, v_a_816_);
lean_dec(v_a_816_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_fst_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_fst_818_);
v_a_821_ = lean_ctor_get(v_x_819_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_x_819_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v_x_819_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v_x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_828_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; 
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
else
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_838_; 
v_isSharedCheck_838_ = !lean_is_exclusive(v_x_819_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_x_819_, 0);
lean_dec(v_unused_839_);
v___x_831_ = v_x_819_;
v_isShared_832_ = v_isSharedCheck_838_;
goto v_resetjp_830_;
}
else
{
lean_dec(v_x_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_838_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_fst_818_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_833_);
v___x_835_ = v___x_831_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_837_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; 
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_840_, lean_object* v_x_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_840_, v_x_841_);
return v_res_843_;
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
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_894_; 
v_a_860_ = lean_ctor_get(v_x_849_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_849_);
if (v_isSharedCheck_894_ == 0)
{
v___x_862_ = v_x_849_;
v_isShared_863_ = v_isSharedCheck_894_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v_x_849_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_894_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_values_864_; lean_object* v_consumers_865_; uint8_t v_closed_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_893_; 
v_values_864_ = lean_ctor_get(v_a_860_, 0);
v_consumers_865_ = lean_ctor_get(v_a_860_, 1);
v_closed_866_ = lean_ctor_get_uint8(v_a_860_, sizeof(void*)*2);
v_isSharedCheck_893_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_893_ == 0)
{
v___x_868_ = v_a_860_;
v_isShared_869_ = v_isSharedCheck_893_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_consumers_865_);
lean_inc(v_values_864_);
lean_dec(v_a_860_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_893_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_Queue_dequeue_x3f___redArg(v_values_864_);
if (lean_obj_tag(v___x_870_) == 1)
{
lean_object* v_val_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_891_; 
v_val_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_891_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_891_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_val_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_891_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_fst_875_; lean_object* v_snd_876_; lean_object* v___x_878_; 
v_fst_875_ = lean_ctor_get(v_val_871_, 0);
lean_inc(v_fst_875_);
v_snd_876_ = lean_ctor_get(v_val_871_, 1);
lean_inc(v_snd_876_);
lean_dec(v_val_871_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v_snd_876_);
v___x_878_ = v___x_868_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_snd_876_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_consumers_865_);
lean_ctor_set_uint8(v_reuseFailAlloc_890_, sizeof(void*)*2, v_closed_866_);
v___x_878_ = v_reuseFailAlloc_890_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___f_880_; lean_object* v___x_882_; 
v___x_879_ = lean_st_ref_set(v_a_848_, v___x_878_);
v___f_880_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_880_, 0, v_fst_875_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_879_);
v___x_882_ = v___x_862_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_879_);
v___x_882_ = v_reuseFailAlloc_889_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set_tag(v___x_873_, 0);
lean_ctor_set(v___x_873_, 0, v___x_882_);
v___x_884_ = v___x_873_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = 0;
v___x_887_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_885_, v___x_886_, v___x_884_, v___f_880_);
return v___x_887_;
}
}
}
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v___x_870_);
lean_del_object(v___x_868_);
lean_dec_ref(v_consumers_865_);
lean_del_object(v___x_862_);
v___x_892_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_895_, lean_object* v_x_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_895_, v_x_896_);
lean_dec(v_a_895_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; 
v___x_901_ = lean_st_ref_get(v_a_899_);
lean_inc(v_a_899_);
v___f_902_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_902_, 0, v_a_899_);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = 0;
v___x_907_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_905_, v___x_906_, v___x_904_, v___f_902_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_908_);
lean_dec(v_a_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object* v_00_u03b1_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_915_, lean_object* v_a_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_915_, v_a_916_);
lean_dec(v_a_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_promise_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
v_a_922_ = lean_ctor_get(v_x_920_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_x_920_);
if (v_isSharedCheck_930_ == 0)
{
v___x_924_ = v_x_920_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v_x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_929_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_io_promise_resolve(v_x_920_, v_promise_919_);
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_promise_934_, lean_object* v_x_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_934_, v_x_935_);
lean_dec(v_promise_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_938_, lean_object* v___y_939_, lean_object* v___f_940_, lean_object* v_x_941_){
_start:
{
if (lean_obj_tag(v_x_941_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v___f_940_);
lean_dec_ref(v_lose_938_);
v_a_943_ = lean_ctor_get(v_x_941_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x_941_);
if (v_isSharedCheck_951_ == 0)
{
v___x_945_ = v_x_941_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v_x_941_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_950_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; 
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
}
else
{
lean_object* v_a_952_; uint8_t v___x_953_; 
v_a_952_ = lean_ctor_get(v_x_941_, 0);
lean_inc(v_a_952_);
lean_dec_ref(v_x_941_);
v___x_953_ = lean_unbox(v_a_952_);
lean_dec(v_a_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_dec_ref(v___f_940_);
lean_inc(v___y_939_);
v___x_954_ = lean_apply_2(v_lose_938_, v___y_939_, lean_box(0));
return v___x_954_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v_lose_938_);
v___x_955_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_939_);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = 0;
v___x_958_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_956_, v___x_957_, v___x_955_, v___f_940_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_959_, lean_object* v___y_960_, lean_object* v___f_961_, lean_object* v_x_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_959_, v___y_960_, v___f_961_, v_x_962_);
lean_dec(v___y_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object* v_w_965_, lean_object* v_lose_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_finished_969_; lean_object* v_promise_970_; lean_object* v___x_971_; lean_object* v___f_972_; lean_object* v___f_973_; uint8_t v___y_975_; uint8_t v___x_985_; 
v_finished_969_ = lean_ctor_get(v_w_965_, 0);
lean_inc(v_finished_969_);
v_promise_970_ = lean_ctor_get(v_w_965_, 1);
lean_inc(v_promise_970_);
lean_dec_ref(v_w_965_);
v___x_971_ = lean_st_ref_take(v_finished_969_);
v___f_972_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_972_, 0, v_promise_970_);
lean_inc(v___y_967_);
v___f_973_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_973_, 0, v_lose_966_);
lean_closure_set(v___f_973_, 1, v___y_967_);
lean_closure_set(v___f_973_, 2, v___f_972_);
v___x_985_ = lean_unbox(v___x_971_);
lean_dec(v___x_971_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; 
v___x_986_ = 1;
v___y_975_ = v___x_986_;
goto v___jp_974_;
}
else
{
uint8_t v___x_987_; 
v___x_987_ = 0;
v___y_975_ = v___x_987_;
goto v___jp_974_;
}
v___jp_974_:
{
uint8_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; lean_object* v___x_984_; 
v___x_976_ = 1;
v___x_977_ = lean_box(v___x_976_);
v___x_978_ = lean_st_ref_set(v_finished_969_, v___x_977_);
lean_dec(v_finished_969_);
v___x_979_ = lean_box(v___y_975_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = 0;
v___x_984_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_982_, v___x_983_, v___x_981_, v___f_973_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object* v_w_988_, lean_object* v_lose_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_988_, v_lose_989_, v___y_990_);
lean_dec(v___y_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object* v_00_u03b1_993_, lean_object* v_w_994_, lean_object* v_lose_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_994_, v_lose_995_, v___y_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_999_, lean_object* v_w_1000_, lean_object* v_lose_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_999_, v_w_1000_, v_lose_1001_, v___y_1002_);
lean_dec(v___y_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_io_basemutex_unlock(v_mutex_1005_);
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(v_mutex_1011_, v_x_1012_);
lean_dec(v_x_1012_);
lean_dec(v_mutex_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_1015_, lean_object* v_ref_1016_, lean_object* v_x_1017_){
_start:
{
if (lean_obj_tag(v_x_1017_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_ref_1016_);
lean_dec_ref(v_k_1015_);
v_a_1019_ = lean_ctor_get(v_x_1017_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_x_1017_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1021_ = v_x_1017_;
v_isShared_1022_ = v_isSharedCheck_1027_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v_x_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1027_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
}
else
{
lean_object* v___x_1028_; 
lean_dec_ref(v_x_1017_);
v___x_1028_ = lean_apply_2(v_k_1015_, v_ref_1016_, lean_box(0));
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_1029_, lean_object* v_ref_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_k_1029_, v_ref_1030_, v_x_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_1034_, lean_object* v___f_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1037_ = lean_io_basemutex_lock(v_mutex_1034_);
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = 0;
v___x_1042_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1040_, v___x_1041_, v___x_1039_, v___f_1035_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_1043_, lean_object* v___f_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_mutex_1043_, v___f_1044_);
lean_dec(v_mutex_1043_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_1047_){
_start:
{
if (lean_obj_tag(v___y_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
v_a_1048_ = lean_ctor_get(v___y_1047_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___y_1047_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___y_1047_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___y_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
v_a_1056_ = lean_ctor_get(v___y_1047_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___y_1047_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1058_ = v___y_1047_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___y_1047_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_fst_1060_; lean_object* v___x_1062_; 
v_fst_1060_ = lean_ctor_get(v_a_1056_, 0);
lean_inc(v_fst_1060_);
lean_dec(v_a_1056_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v_fst_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_fst_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object* v_mutex_1066_, lean_object* v_k_1067_){
_start:
{
lean_object* v_ref_1069_; lean_object* v_mutex_1070_; lean_object* v___f_1071_; lean_object* v___f_1072_; lean_object* v___f_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___y_1078_; 
v_ref_1069_ = lean_ctor_get(v_mutex_1066_, 0);
lean_inc(v_ref_1069_);
v_mutex_1070_ = lean_ctor_get(v_mutex_1066_, 1);
lean_inc_n(v_mutex_1070_, 2);
lean_dec_ref(v_mutex_1066_);
v___f_1071_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1071_, 0, v_mutex_1070_);
v___f_1072_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1072_, 0, v_k_1067_);
lean_closure_set(v___f_1072_, 1, v_ref_1069_);
v___f_1073_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_1073_, 0, v_mutex_1070_);
lean_closure_set(v___f_1073_, 1, v___f_1072_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = 0;
v___x_1076_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1073_, v___f_1071_, v___x_1074_, v___x_1075_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1080_; 
v_a_1080_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1076_);
if (lean_obj_tag(v_a_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
v_a_1081_ = lean_ctor_get(v_a_1080_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_a_1080_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v_a_1080_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v_a_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
v___y_1078_ = v___x_1086_;
goto v___jp_1077_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1097_; 
v_a_1089_ = lean_ctor_get(v_a_1080_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1080_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1091_ = v_a_1080_;
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v_a_1080_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_fst_1093_; lean_object* v___x_1095_; 
v_fst_1093_ = lean_ctor_get(v_a_1089_, 0);
lean_inc(v_fst_1093_);
lean_dec(v_a_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v_fst_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_fst_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
v___y_1078_ = v___x_1095_;
goto v___jp_1077_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1107_; 
v_a_1098_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1100_ = v___x_1076_;
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1076_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1107_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___f_1102_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0));
v___x_1103_ = lean_task_map(v___f_1102_, v_a_1098_, v___x_1074_, v___x_1075_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1103_);
v___x_1105_ = v___x_1100_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
v___jp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___y_1078_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_1108_, lean_object* v_k_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1108_, v_k_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_mutex_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1114_, v_k_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_mutex_1120_, lean_object* v_k_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_1118_, v_00_u03b2_1119_, v_mutex_1120_, v_k_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v_a_1126_ = lean_ctor_get(v_x_1124_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_x_1124_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1128_ = v_x_1124_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v_x_1124_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1144_; 
v_a_1135_ = lean_ctor_get(v_x_1124_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_x_1124_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1137_ = v_x_1124_;
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v_x_1124_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_a_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object* v_x_1148_){
_start:
{
uint8_t v___y_1151_; 
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1163_; 
v_a_1155_ = lean_ctor_get(v_x_1148_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1157_ = v_x_1148_;
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v_x_1148_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1163_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v_values_1165_; uint8_t v_closed_1166_; uint8_t v___x_1167_; 
v_a_1164_ = lean_ctor_get(v_x_1148_, 0);
lean_inc(v_a_1164_);
lean_dec_ref(v_x_1148_);
v_values_1165_ = lean_ctor_get(v_a_1164_, 0);
lean_inc_ref(v_values_1165_);
v_closed_1166_ = lean_ctor_get_uint8(v_a_1164_, sizeof(void*)*2);
lean_dec(v_a_1164_);
v___x_1167_ = l_Std_Queue_isEmpty___redArg(v_values_1165_);
lean_dec_ref(v_values_1165_);
if (v___x_1167_ == 0)
{
uint8_t v___x_1168_; 
v___x_1168_ = 1;
v___y_1151_ = v___x_1168_;
goto v___jp_1150_;
}
else
{
v___y_1151_ = v_closed_1166_;
goto v___jp_1150_;
}
}
v___jp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_box(v___y_1151_);
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object* v_x_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object* v___x_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1172_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1177_, v___y_1178_);
lean_dec(v___y_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object* v___y_1187_, lean_object* v_waiter_1188_, lean_object* v_x_1189_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_waiter_1188_);
v_a_1191_ = lean_ctor_get(v_x_1189_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_x_1189_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1193_ = v_x_1189_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v_x_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; uint8_t v___x_1201_; 
v_a_1200_ = lean_ctor_get(v_x_1189_, 0);
lean_inc(v_a_1200_);
lean_dec_ref(v_x_1189_);
v___x_1201_ = lean_unbox(v_a_1200_);
lean_dec(v_a_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v_values_1203_; lean_object* v_consumers_1204_; uint8_t v_closed_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1216_; 
v___x_1202_ = lean_st_ref_take(v___y_1187_);
v_values_1203_ = lean_ctor_get(v___x_1202_, 0);
v_consumers_1204_ = lean_ctor_get(v___x_1202_, 1);
v_closed_1205_ = lean_ctor_get_uint8(v___x_1202_, sizeof(void*)*2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1207_ = v___x_1202_;
v_isShared_1208_ = v_isSharedCheck_1216_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_consumers_1204_);
lean_inc(v_values_1203_);
lean_dec(v___x_1202_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1216_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_waiter_1188_);
v___x_1210_ = l_Std_Queue_enqueue___redArg(v___x_1209_, v_consumers_1204_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1210_);
v___x_1212_ = v___x_1207_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_values_1203_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*2, v_closed_1205_);
v___x_1212_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_st_ref_set(v___y_1187_, v___x_1212_);
v___x_1214_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_1214_;
}
}
}
else
{
lean_object* v_lose_1217_; lean_object* v___x_1218_; 
v_lose_1217_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_1218_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_1188_, v_lose_1217_, v___y_1187_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object* v___y_1219_, lean_object* v_waiter_1220_, lean_object* v_x_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1219_, v_waiter_1220_, v_x_1221_);
lean_dec(v___y_1219_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object* v___f_1224_, lean_object* v_waiter_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___f_1234_; lean_object* v___x_1235_; 
v___x_1228_ = lean_st_ref_get(v___y_1226_);
v___x_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
v___x_1231_ = lean_unsigned_to_nat(0u);
v___x_1232_ = 0;
v___x_1233_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1231_, v___x_1232_, v___x_1230_, v___f_1224_);
lean_inc(v___y_1226_);
v___f_1234_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1234_, 0, v___y_1226_);
lean_closure_set(v___f_1234_, 1, v_waiter_1225_);
v___x_1235_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1231_, v___x_1232_, v___x_1233_, v___f_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object* v___f_1236_, lean_object* v_waiter_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v___f_1236_, v_waiter_1237_, v___y_1238_);
lean_dec(v___y_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object* v___f_1241_, lean_object* v_ch_1242_, lean_object* v_waiter_1243_){
_start:
{
lean_object* v___f_1245_; lean_object* v___x_1246_; 
v___f_1245_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1245_, 0, v___f_1241_);
lean_closure_set(v___f_1245_, 1, v_waiter_1243_);
v___x_1246_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_1242_, v___f_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object* v___f_1247_, lean_object* v_ch_1248_, lean_object* v_waiter_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1247_, v_ch_1248_, v_waiter_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object* v___y_1256_, lean_object* v___f_1257_, lean_object* v_x_1258_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1268_; 
lean_dec_ref(v___f_1257_);
v_a_1260_ = lean_ctor_get(v_x_1258_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1262_ = v_x_1258_;
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v_x_1258_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
}
else
{
lean_object* v_a_1269_; uint8_t v___x_1270_; 
v_a_1269_ = lean_ctor_get(v_x_1258_, 0);
lean_inc(v_a_1269_);
lean_dec_ref(v_x_1258_);
v___x_1270_ = lean_unbox(v_a_1269_);
lean_dec(v_a_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_dec_ref(v___f_1257_);
v___x_1271_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_1271_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_1256_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = 0;
v___x_1275_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1273_, v___x_1274_, v___x_1272_, v___f_1257_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object* v___y_1276_, lean_object* v___f_1277_, lean_object* v_x_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1276_, v___f_1277_, v_x_1278_);
lean_dec(v___y_1276_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object* v___f_1281_, lean_object* v___f_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; 
v___x_1285_ = lean_st_ref_get(v___y_1283_);
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = 0;
v___x_1290_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1288_, v___x_1289_, v___x_1287_, v___f_1281_);
lean_inc(v___y_1283_);
v___f_1291_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1291_, 0, v___y_1283_);
lean_closure_set(v___f_1291_, 1, v___f_1282_);
v___x_1292_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1288_, v___x_1289_, v___x_1290_, v___f_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object* v___f_1293_, lean_object* v___f_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1293_, v___f_1294_, v___y_1295_);
lean_dec(v___y_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object* v_values_1298_, uint8_t v_closed_1299_, lean_object* v___y_1300_, lean_object* v_x_1301_){
_start:
{
if (lean_obj_tag(v_x_1301_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_values_1298_);
v_a_1303_ = lean_ctor_get(v_x_1301_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_x_1301_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1305_ = v_x_1301_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v_x_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1308_);
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1322_; 
v_a_1312_ = lean_ctor_get(v_x_1301_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_x_1301_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1314_ = v_x_1301_;
v_isShared_1315_ = v_isSharedCheck_1322_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v_x_1301_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1322_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1316_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1316_, 0, v_values_1298_);
lean_ctor_set(v___x_1316_, 1, v_a_1312_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*2, v_closed_1299_);
v___x_1317_ = lean_st_ref_set(v___y_1300_, v___x_1316_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1317_);
v___x_1319_ = v___x_1314_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(lean_object* v_values_1323_, lean_object* v_closed_1324_, lean_object* v___y_1325_, lean_object* v_x_1326_, lean_object* v___y_1327_){
_start:
{
uint8_t v_closed_boxed_1328_; lean_object* v_res_1329_; 
v_closed_boxed_1328_ = lean_unbox(v_closed_1324_);
v_res_1329_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_1323_, v_closed_boxed_1328_, v___y_1325_, v_x_1326_);
lean_dec(v___y_1325_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_1330_){
_start:
{
if (lean_obj_tag(v_x_1330_) == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v_x_1330_);
return v___x_1332_;
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1342_; 
v_a_1333_ = lean_ctor_get(v_x_1330_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_x_1330_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1335_ = v_x_1330_;
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v_x_1330_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = l_List_reverse___redArg(v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_1346_, lean_object* v___x_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v___x_1347_);
lean_dec(v_a_1346_);
v_a_1350_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1352_ = v_x_1348_;
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v_x_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1375_; 
v_a_1359_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1361_ = v_x_1348_;
v_isShared_1362_ = v_isSharedCheck_1375_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v_x_1348_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1375_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
uint8_t v___x_1363_; 
v___x_1363_ = l_List_isEmpty___redArg(v_a_1346_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
lean_dec(v___x_1347_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1359_);
lean_ctor_set(v___x_1364_, 1, v_a_1346_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1364_);
v___x_1366_ = v___x_1361_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec(v_a_1346_);
v___x_1369_ = l_List_reverse___redArg(v_a_1359_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1347_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1370_);
v___x_1372_ = v___x_1361_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1370_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_1376_, lean_object* v___x_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_1376_, v___x_1377_, v_x_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(lean_object* v_x_1381_){
_start:
{
uint8_t v___y_1384_; 
if (lean_obj_tag(v_x_1381_) == 0)
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_x_1381_);
return v___x_1388_;
}
else
{
lean_object* v_a_1389_; uint8_t v___x_1390_; 
v_a_1389_ = lean_ctor_get(v_x_1381_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v_x_1381_);
v___x_1390_ = lean_unbox(v_a_1389_);
lean_dec(v_a_1389_);
if (v___x_1390_ == 0)
{
uint8_t v___x_1391_; 
v___x_1391_ = 1;
v___y_1384_ = v___x_1391_;
goto v___jp_1383_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = 0;
v___y_1384_ = v___x_1392_;
goto v___jp_1383_;
}
}
v___jp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = lean_box(v___y_1384_);
v___x_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object* v_x_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_tail_1396_, lean_object* v_x_1397_, lean_object* v_head_1398_, lean_object* v_x_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1396_, v_x_1397_, v_head_1398_, v_x_1399_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
if (lean_obj_tag(v_x_1408_) == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_x_1409_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
else
{
lean_object* v_head_1413_; lean_object* v_tail_1414_; lean_object* v___f_1415_; lean_object* v_val_1417_; 
v_head_1413_ = lean_ctor_get(v_x_1408_, 0);
lean_inc_n(v_head_1413_, 2);
v_tail_1414_ = lean_ctor_get(v_x_1408_, 1);
lean_inc(v_tail_1414_);
lean_dec_ref(v_x_1408_);
v___f_1415_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1415_, 0, v_tail_1414_);
lean_closure_set(v___f_1415_, 1, v_x_1409_);
lean_closure_set(v___f_1415_, 2, v_head_1413_);
if (lean_obj_tag(v_head_1413_) == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_head_1413_);
v___x_1421_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_1417_ = v___x_1421_;
goto v___jp_1416_;
}
else
{
lean_object* v_finished_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1436_; 
v_finished_1422_ = lean_ctor_get(v_head_1413_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_head_1413_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1424_ = v_head_1413_;
v_isShared_1425_ = v_isSharedCheck_1436_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_finished_1422_);
lean_dec(v_head_1413_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1436_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_finished_1426_; lean_object* v___x_1427_; lean_object* v___f_1428_; lean_object* v___x_1430_; 
v_finished_1426_ = lean_ctor_get(v_finished_1422_, 0);
lean_inc(v_finished_1426_);
lean_dec_ref(v_finished_1422_);
v___x_1427_ = lean_st_ref_get(v_finished_1426_);
lean_dec(v_finished_1426_);
v___f_1428_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v___x_1427_);
v___x_1430_ = v___x_1424_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1427_);
v___x_1430_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = 0;
v___x_1434_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1432_, v___x_1433_, v___x_1431_, v___f_1428_);
v_val_1417_ = v___x_1434_;
goto v___jp_1416_;
}
}
}
v___jp_1416_:
{
lean_object* v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_unsigned_to_nat(0u);
v___x_1419_ = 0;
v___x_1420_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1418_, v___x_1419_, v_val_1417_, v___f_1415_);
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1437_, lean_object* v_x_1438_, lean_object* v_head_1439_, lean_object* v_x_1440_){
_start:
{
if (lean_obj_tag(v_x_1440_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v_head_1439_);
lean_dec(v_x_1438_);
lean_dec(v_tail_1437_);
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
lean_object* v_a_1451_; uint8_t v___x_1452_; 
v_a_1451_ = lean_ctor_get(v_x_1440_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v_x_1440_);
v___x_1452_ = lean_unbox(v_a_1451_);
lean_dec(v_a_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_dec_ref(v_head_1439_);
v___x_1453_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1437_, v_x_1438_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_head_1439_);
lean_ctor_set(v___x_1454_, 1, v_x_1438_);
v___x_1455_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1437_, v___x_1454_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1456_, v_x_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_1460_, lean_object* v___x_1461_, lean_object* v___f_1462_, lean_object* v_x_1463_){
_start:
{
if (lean_obj_tag(v_x_1463_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1473_; 
lean_dec_ref(v___f_1462_);
lean_dec(v___x_1461_);
lean_dec(v_eList_1460_);
v_a_1465_ = lean_ctor_get(v_x_1463_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1467_ = v_x_1463_;
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v_x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___f_1479_; lean_object* v___x_1480_; 
v_a_1474_ = lean_ctor_get(v_x_1463_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v_x_1463_);
lean_inc(v___x_1461_);
v___x_1475_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1460_, v___x_1461_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = 0;
v___x_1478_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1476_, v___x_1477_, v___x_1475_, v___f_1462_);
v___f_1479_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1479_, 0, v_a_1474_);
lean_closure_set(v___f_1479_, 1, v___x_1461_);
v___x_1480_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1476_, v___x_1477_, v___x_1478_, v___f_1479_);
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_1481_, lean_object* v___x_1482_, lean_object* v___f_1483_, lean_object* v_x_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v_eList_1481_, v___x_1482_, v___f_1483_, v_x_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_eList_1491_; lean_object* v_dList_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___f_1499_; lean_object* v___x_1500_; 
v_eList_1491_ = lean_ctor_get(v_q_1488_, 0);
lean_inc(v_eList_1491_);
v_dList_1492_ = lean_ctor_get(v_q_1488_, 1);
lean_inc(v_dList_1492_);
lean_dec_ref(v_q_1488_);
v___x_1493_ = lean_box(0);
v___x_1494_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1492_, v___x_1493_);
v___f_1495_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = 0;
v___x_1498_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1496_, v___x_1497_, v___x_1494_, v___f_1495_);
v___f_1499_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1499_, 0, v_eList_1491_);
lean_closure_set(v___f_1499_, 1, v___x_1493_);
lean_closure_set(v___f_1499_, 2, v___f_1495_);
v___x_1500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1496_, v___x_1497_, v___x_1498_, v___f_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1501_, v___y_1502_);
lean_dec(v___y_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1505_, lean_object* v_x_1506_){
_start:
{
if (lean_obj_tag(v_x_1506_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1516_; 
v_a_1508_ = lean_ctor_get(v_x_1506_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_x_1506_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1510_ = v_x_1506_;
v_isShared_1511_ = v_isSharedCheck_1516_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v_x_1506_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1516_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v_values_1518_; lean_object* v_consumers_1519_; uint8_t v_closed_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v_a_1517_ = lean_ctor_get(v_x_1506_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v_x_1506_);
v_values_1518_ = lean_ctor_get(v_a_1517_, 0);
lean_inc_ref(v_values_1518_);
v_consumers_1519_ = lean_ctor_get(v_a_1517_, 1);
lean_inc_ref(v_consumers_1519_);
v_closed_1520_ = lean_ctor_get_uint8(v_a_1517_, sizeof(void*)*2);
lean_dec(v_a_1517_);
v___x_1521_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1519_, v___y_1505_);
v___x_1522_ = lean_box(v_closed_1520_);
lean_inc(v___y_1505_);
v___f_1523_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1523_, 0, v_values_1518_);
lean_closure_set(v___f_1523_, 1, v___x_1522_);
lean_closure_set(v___f_1523_, 2, v___y_1505_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = 0;
v___x_1526_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1524_, v___x_1525_, v___x_1521_, v___f_1523_);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1527_, lean_object* v_x_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1527_, v_x_1528_);
lean_dec(v___y_1527_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; lean_object* v___f_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; 
v___x_1533_ = lean_st_ref_get(v___y_1531_);
lean_inc(v___y_1531_);
v___f_1534_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1534_, 0, v___y_1531_);
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
v___x_1537_ = lean_unsigned_to_nat(0u);
v___x_1538_ = 0;
v___x_1539_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1537_, v___x_1538_, v___x_1536_, v___f_1534_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1540_);
lean_dec(v___y_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1549_){
_start:
{
lean_object* v___f_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___f_1550_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref_n(v_ch_1549_, 2);
v___f_1551_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1551_, 0, v___f_1550_);
lean_closure_set(v___f_1551_, 1, v_ch_1549_);
v___f_1552_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1553_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
v___x_1554_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1554_, 0, lean_box(0));
lean_closure_set(v___x_1554_, 1, lean_box(0));
lean_closure_set(v___x_1554_, 2, v_ch_1549_);
lean_closure_set(v___x_1554_, 3, v___f_1552_);
v___x_1555_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1555_, 0, lean_box(0));
lean_closure_set(v___x_1555_, 1, lean_box(0));
lean_closure_set(v___x_1555_, 2, v_ch_1549_);
lean_closure_set(v___x_1555_, 3, v___f_1553_);
v___x_1556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___f_1551_);
lean_ctor_set(v___x_1556_, 2, v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1557_, lean_object* v_ch_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1560_, lean_object* v_q_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1561_, v___y_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_q_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1565_, v_q_1566_, v___y_1567_);
lean_dec(v___y_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1571_, v_x_1572_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1576_, v_x_1577_, v_x_1578_, v___y_1579_);
lean_dec(v___y_1579_);
return v_res_1581_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Std_Queue_empty(lean_box(0));
return v___x_1582_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = 0;
v___x_1584_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1585_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
lean_ctor_set_uint8(v___x_1585_, sizeof(void*)*2, v___x_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1);
v___x_1588_ = l_Std_Mutex_new___redArg(v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v_producers_1610_; lean_object* v_consumers_1611_; uint8_t v_closed_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1635_; 
v___x_1609_ = lean_st_ref_get(v___y_1607_);
v_producers_1610_ = lean_ctor_get(v___x_1609_, 0);
v_consumers_1611_ = lean_ctor_get(v___x_1609_, 1);
v_closed_1612_ = lean_ctor_get_uint8(v___x_1609_, sizeof(void*)*2);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1614_ = v___x_1609_;
v_isShared_1615_ = v_isSharedCheck_1635_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_consumers_1611_);
lean_inc(v_producers_1610_);
lean_dec(v___x_1609_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1635_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1611_);
if (lean_obj_tag(v___x_1616_) == 1)
{
lean_object* v_val_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1633_; 
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1633_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_val_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1633_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_fst_1621_; lean_object* v_snd_1622_; lean_object* v___x_1624_; 
v_fst_1621_ = lean_ctor_get(v_val_1617_, 0);
lean_inc(v_fst_1621_);
v_snd_1622_ = lean_ctor_get(v_val_1617_, 1);
lean_inc(v_snd_1622_);
lean_dec(v_val_1617_);
lean_inc(v_v_1606_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v_v_1606_);
v___x_1624_ = v___x_1619_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_v_1606_);
v___x_1624_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
uint8_t v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1621_, v___x_1624_);
lean_dec(v_fst_1621_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 1, v_snd_1622_);
v___x_1627_ = v___x_1614_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_producers_1610_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_snd_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1631_, sizeof(void*)*2, v_closed_1612_);
v___x_1627_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_st_ref_set(v___y_1607_, v___x_1627_);
if (v___x_1625_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_1630_; 
lean_dec(v_v_1606_);
v___x_1630_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
return v___x_1630_;
}
}
}
}
}
else
{
lean_object* v___x_1634_; 
lean_dec(v___x_1616_);
lean_del_object(v___x_1614_);
lean_dec_ref(v_producers_1610_);
lean_dec(v_v_1606_);
v___x_1634_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1636_, v___y_1637_);
lean_dec(v___y_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1643_; lean_object* v_fst_1644_; 
v___x_1643_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1640_, v_a_1641_);
v_fst_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_fst_1644_);
lean_dec_ref(v___x_1643_);
if (lean_obj_tag(v_fst_1644_) == 0)
{
uint8_t v___x_1645_; 
v___x_1645_ = 1;
return v___x_1645_;
}
else
{
lean_object* v_val_1646_; uint8_t v___x_1647_; 
v_val_1646_ = lean_ctor_get(v_fst_1644_, 0);
lean_inc(v_val_1646_);
lean_dec_ref(v_fst_1644_);
v___x_1647_ = lean_unbox(v_val_1646_);
lean_dec(v_val_1646_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
uint8_t v_res_1651_; lean_object* v_r_1652_; 
v_res_1651_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1648_, v_a_1649_);
lean_dec(v_a_1649_);
v_r_1652_ = lean_box(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1653_, lean_object* v_v_1654_, lean_object* v_a_1655_){
_start:
{
uint8_t v___x_1657_; 
v___x_1657_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1654_, v_a_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1658_, lean_object* v_v_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
uint8_t v_res_1662_; lean_object* v_r_1663_; 
v_res_1662_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1658_, v_v_1659_, v_a_1660_);
lean_dec(v_a_1660_);
v_r_1663_ = lean_box(v_res_1662_);
return v_r_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1664_, lean_object* v_v_1665_, lean_object* v_b_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1665_, v___y_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_v_1671_, lean_object* v_b_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1670_, v_v_1671_, v_b_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v_b_1672_);
return v_res_1675_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; uint8_t v_closed_1680_; 
v___x_1679_ = lean_st_ref_get(v___y_1677_);
v_closed_1680_ = lean_ctor_get_uint8(v___x_1679_, sizeof(void*)*2);
lean_dec(v___x_1679_);
if (v_closed_1680_ == 0)
{
uint8_t v___x_1681_; 
v___x_1681_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1676_, v___y_1677_);
return v___x_1681_;
}
else
{
uint8_t v___x_1682_; 
lean_dec(v_v_1676_);
v___x_1682_ = 0;
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v_res_1686_; lean_object* v_r_1687_; 
v_res_1686_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1683_, v___y_1684_);
lean_dec(v___y_1684_);
v_r_1687_ = lean_box(v_res_1686_);
return v_r_1687_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1688_, lean_object* v_v_1689_){
_start:
{
lean_object* v___f_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___f_1691_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1691_, 0, v_v_1689_);
v___x_1692_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1688_, v___f_1691_);
v___x_1693_ = lean_unbox(v___x_1692_);
lean_dec(v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1694_, lean_object* v_v_1695_, lean_object* v_a_1696_){
_start:
{
uint8_t v_res_1697_; lean_object* v_r_1698_; 
v_res_1697_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1694_, v_v_1695_);
v_r_1698_ = lean_box(v_res_1697_);
return v_r_1698_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1699_, lean_object* v_ch_1700_, lean_object* v_v_1701_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1700_, v_v_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_ch_1705_, lean_object* v_v_1706_, lean_object* v_a_1707_){
_start:
{
uint8_t v_res_1708_; lean_object* v_r_1709_; 
v_res_1708_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1704_, v_ch_1705_, v_v_1706_);
v_r_1709_ = lean_box(v_res_1708_);
return v_r_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
goto v___jp_1711_;
}
else
{
lean_object* v_val_1713_; uint8_t v___x_1714_; 
v_val_1713_ = lean_ctor_get(v_x_1710_, 0);
v___x_1714_ = lean_unbox(v_val_1713_);
if (v___x_1714_ == 0)
{
goto v___jp_1711_;
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1715_;
}
}
v___jp_1711_:
{
lean_object* v___x_1712_; 
v___x_1712_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1716_);
lean_dec(v_x_1716_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1718_, lean_object* v___f_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; uint8_t v_closed_1723_; 
v___x_1722_ = lean_st_ref_get(v___y_1720_);
v_closed_1723_ = lean_ctor_get_uint8(v___x_1722_, sizeof(void*)*2);
lean_dec(v___x_1722_);
if (v_closed_1723_ == 0)
{
uint8_t v___x_1724_; 
lean_inc(v_v_1718_);
v___x_1724_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1718_, v___y_1720_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v_producers_1727_; lean_object* v_consumers_1728_; uint8_t v_closed_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1743_; 
v___x_1725_ = lean_io_promise_new();
v___x_1726_ = lean_st_ref_take(v___y_1720_);
v_producers_1727_ = lean_ctor_get(v___x_1726_, 0);
v_consumers_1728_ = lean_ctor_get(v___x_1726_, 1);
v_closed_1729_ = lean_ctor_get_uint8(v___x_1726_, sizeof(void*)*2);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1731_ = v___x_1726_;
v_isShared_1732_ = v_isSharedCheck_1743_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_consumers_1728_);
lean_inc(v_producers_1727_);
lean_dec(v___x_1726_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1743_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_inc(v___x_1725_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_v_1718_);
lean_ctor_set(v___x_1733_, 1, v___x_1725_);
v___x_1734_ = l_Std_Queue_enqueue___redArg(v___x_1733_, v_producers_1727_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1734_);
v___x_1736_ = v___x_1731_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_consumers_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1742_, sizeof(void*)*2, v_closed_1729_);
v___x_1736_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1737_ = lean_st_ref_set(v___y_1720_, v___x_1736_);
v___x_1738_ = 1;
v___x_1739_ = lean_io_promise_result_opt(v___x_1725_);
lean_dec(v___x_1725_);
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = lean_task_map(v___f_1719_, v___x_1739_, v___x_1740_, v___x_1738_);
return v___x_1741_;
}
}
}
else
{
lean_object* v___x_1744_; 
lean_dec_ref(v___f_1719_);
lean_dec(v_v_1718_);
v___x_1744_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1744_;
}
}
else
{
lean_object* v___x_1745_; 
lean_dec_ref(v___f_1719_);
lean_dec(v_v_1718_);
v___x_1745_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1746_, lean_object* v___f_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1746_, v___f_1747_, v___y_1748_);
lean_dec(v___y_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1752_, lean_object* v_v_1753_){
_start:
{
lean_object* v___f_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; 
v___f_1755_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1756_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1756_, 0, v_v_1753_);
lean_closure_set(v___f_1756_, 1, v___f_1755_);
v___x_1757_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1752_, v___f_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1758_, lean_object* v_v_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1758_, v_v_1759_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1762_, lean_object* v_ch_1763_, lean_object* v_v_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1763_, v_v_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_ch_1768_, lean_object* v_v_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1767_, v_ch_1768_, v_v_1769_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1772_, size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_b_1775_){
_start:
{
uint8_t v___x_1777_; 
v___x_1777_ = lean_usize_dec_lt(v_i_1774_, v_sz_1773_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_b_1775_);
return v___x_1778_;
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; size_t v___x_1783_; size_t v___x_1784_; 
v_a_1779_ = lean_array_uget_borrowed(v_as_1772_, v_i_1774_);
v___x_1780_ = lean_box(0);
v___x_1781_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1779_, v___x_1780_);
v___x_1782_ = lean_box(0);
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_add(v_i_1774_, v___x_1783_);
v_i_1774_ = v___x_1784_;
v_b_1775_ = v___x_1782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1786_, lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1786_, v_sz_boxed_1791_, v_i_boxed_1792_, v_b_1789_);
lean_dec_ref(v_as_1786_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; uint8_t v_closed_1797_; 
v___x_1796_ = lean_st_ref_get(v___y_1794_);
v_closed_1797_ = lean_ctor_get_uint8(v___x_1796_, sizeof(void*)*2);
if (v_closed_1797_ == 0)
{
lean_object* v_producers_1798_; lean_object* v_consumers_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1822_; 
v_producers_1798_ = lean_ctor_get(v___x_1796_, 0);
v_consumers_1799_ = lean_ctor_get(v___x_1796_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1801_ = v___x_1796_;
v_isShared_1802_ = v_isSharedCheck_1822_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_consumers_1799_);
lean_inc(v_producers_1798_);
lean_dec(v___x_1796_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1822_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; size_t v_sz_1805_; size_t v___x_1806_; lean_object* v___x_1807_; 
v___x_1803_ = l_Std_Queue_toArray___redArg(v_consumers_1799_);
v___x_1804_ = lean_box(0);
v_sz_1805_ = lean_array_size(v___x_1803_);
v___x_1806_ = ((size_t)0ULL);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1803_, v_sz_1805_, v___x_1806_, v___x_1804_);
lean_dec_ref(v___x_1803_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1820_; 
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1807_, 0);
lean_dec(v_unused_1821_);
v___x_1809_ = v___x_1807_;
v_isShared_1810_ = v_isSharedCheck_1820_;
goto v_resetjp_1808_;
}
else
{
lean_dec(v___x_1807_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1820_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; uint8_t v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
v___x_1812_ = 1;
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1811_);
v___x_1814_ = v___x_1801_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_producers_1798_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1811_);
v___x_1814_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_ctor_set_uint8(v___x_1814_, sizeof(void*)*2, v___x_1812_);
v___x_1815_ = lean_st_ref_set(v___y_1794_, v___x_1814_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1804_);
v___x_1817_ = v___x_1809_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1804_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_del_object(v___x_1801_);
lean_dec_ref(v_producers_1798_);
return v___x_1807_;
}
}
}
else
{
uint8_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v___x_1796_);
v___x_1823_ = 1;
v___x_1824_ = lean_box(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1826_);
lean_dec(v___y_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1830_){
_start:
{
lean_object* v___f_1832_; lean_object* v___x_1833_; 
v___f_1832_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1833_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1830_, v___f_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1837_, lean_object* v_ch_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1838_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_ch_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1841_, v_ch_1842_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1845_, lean_object* v_as_1846_, size_t v_sz_1847_, size_t v_i_1848_, lean_object* v_b_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1846_, v_sz_1847_, v_i_1848_, v_b_1849_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1853_, lean_object* v_as_1854_, lean_object* v_sz_1855_, lean_object* v_i_1856_, lean_object* v_b_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
size_t v_sz_boxed_1860_; size_t v_i_boxed_1861_; lean_object* v_res_1862_; 
v_sz_boxed_1860_ = lean_unbox_usize(v_sz_1855_);
lean_dec(v_sz_1855_);
v_i_boxed_1861_ = lean_unbox_usize(v_i_1856_);
lean_dec(v_i_1856_);
v_res_1862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1853_, v_as_1854_, v_sz_boxed_1860_, v_i_boxed_1861_, v_b_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v_as_1854_);
return v_res_1862_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; uint8_t v_closed_1866_; 
v___x_1865_ = lean_st_ref_get(v___y_1863_);
v_closed_1866_ = lean_ctor_get_uint8(v___x_1865_, sizeof(void*)*2);
lean_dec(v___x_1865_);
return v_closed_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
uint8_t v_res_1869_; lean_object* v_r_1870_; 
v_res_1869_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1867_);
lean_dec(v___y_1867_);
v_r_1870_ = lean_box(v_res_1869_);
return v_r_1870_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1872_){
_start:
{
lean_object* v___f_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___f_1874_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1875_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1872_, v___f_1874_);
v___x_1876_ = lean_unbox(v___x_1875_);
lean_dec(v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1877_, lean_object* v_a_1878_){
_start:
{
uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_res_1879_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1877_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1881_, lean_object* v_ch_1882_){
_start:
{
uint8_t v___x_1884_; 
v___x_1884_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1885_, lean_object* v_ch_1886_, lean_object* v_a_1887_){
_start:
{
uint8_t v_res_1888_; lean_object* v_r_1889_; 
v_res_1888_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1885_, v_ch_1886_);
v_r_1889_ = lean_box(v_res_1888_);
return v_r_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1890_, lean_object* v_inst_1891_, lean_object* v_toBind_1892_, lean_object* v___f_1893_, lean_object* v_a_1894_){
_start:
{
uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1895_ = 1;
v___x_1896_ = lean_box(v___x_1895_);
v___x_1897_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1897_, 0, lean_box(0));
lean_closure_set(v___x_1897_, 1, v___x_1896_);
lean_closure_set(v___x_1897_, 2, v_snd_1890_);
v___x_1898_ = lean_apply_2(v_inst_1891_, lean_box(0), v___x_1897_);
v___x_1899_ = lean_apply_4(v_toBind_1892_, lean_box(0), lean_box(0), v___x_1898_, v___f_1893_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1900_, lean_object* v_inst_1901_, lean_object* v_toBind_1902_, lean_object* v_a_1903_, lean_object* v_inst_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_producers_1906_; lean_object* v_consumers_1907_; uint8_t v_closed_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1929_; 
v_producers_1906_ = lean_ctor_get(v_a_1905_, 0);
v_consumers_1907_ = lean_ctor_get(v_a_1905_, 1);
v_closed_1908_ = lean_ctor_get_uint8(v_a_1905_, sizeof(void*)*2);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_a_1905_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1910_ = v_a_1905_;
v_isShared_1911_ = v_isSharedCheck_1929_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_consumers_1907_);
lean_inc(v_producers_1906_);
lean_dec(v_a_1905_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1929_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1906_);
if (lean_obj_tag(v___x_1912_) == 1)
{
lean_object* v_val_1913_; lean_object* v_fst_1914_; lean_object* v_snd_1915_; lean_object* v_fst_1916_; lean_object* v_snd_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___x_1921_; 
v_val_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref(v___x_1912_);
v_fst_1914_ = lean_ctor_get(v_val_1913_, 0);
lean_inc(v_fst_1914_);
v_snd_1915_ = lean_ctor_get(v_val_1913_, 1);
lean_inc(v_snd_1915_);
lean_dec(v_val_1913_);
v_fst_1916_ = lean_ctor_get(v_fst_1914_, 0);
lean_inc(v_fst_1916_);
v_snd_1917_ = lean_ctor_get(v_fst_1914_, 1);
lean_inc(v_snd_1917_);
lean_dec(v_fst_1914_);
v___f_1918_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1918_, 0, v_toApplicative_1900_);
lean_closure_set(v___f_1918_, 1, v_fst_1916_);
lean_inc(v_toBind_1902_);
v___f_1919_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1919_, 0, v_snd_1917_);
lean_closure_set(v___f_1919_, 1, v_inst_1901_);
lean_closure_set(v___f_1919_, 2, v_toBind_1902_);
lean_closure_set(v___f_1919_, 3, v___f_1918_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v_snd_1915_);
v___x_1921_ = v___x_1910_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_snd_1915_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_consumers_1907_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*2, v_closed_1908_);
v___x_1921_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_inc(v_a_1903_);
v___x_1922_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1922_, 0, lean_box(0));
lean_closure_set(v___x_1922_, 1, lean_box(0));
lean_closure_set(v___x_1922_, 2, v_a_1903_);
lean_closure_set(v___x_1922_, 3, v___x_1921_);
v___x_1923_ = lean_apply_2(v_inst_1904_, lean_box(0), v___x_1922_);
v___x_1924_ = lean_apply_4(v_toBind_1902_, lean_box(0), lean_box(0), v___x_1923_, v___f_1919_);
return v___x_1924_;
}
}
else
{
lean_object* v_toPure_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec(v___x_1912_);
lean_del_object(v___x_1910_);
lean_dec_ref(v_consumers_1907_);
lean_dec(v_inst_1904_);
lean_dec(v_toBind_1902_);
lean_dec(v_inst_1901_);
v_toPure_1926_ = lean_ctor_get(v_toApplicative_1900_, 1);
lean_inc(v_toPure_1926_);
lean_dec_ref(v_toApplicative_1900_);
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_apply_2(v_toPure_1926_, lean_box(0), v___x_1927_);
return v___x_1928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_1930_, lean_object* v_inst_1931_, lean_object* v_toBind_1932_, lean_object* v_a_1933_, lean_object* v_inst_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(v_toApplicative_1930_, v_inst_1931_, v_toBind_1932_, v_a_1933_, v_inst_1934_, v_a_1935_);
lean_dec(v_a_1933_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_inst_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_toApplicative_1941_; lean_object* v_toBind_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v_toApplicative_1941_ = lean_ctor_get(v_inst_1937_, 0);
lean_inc_ref(v_toApplicative_1941_);
v_toBind_1942_ = lean_ctor_get(v_inst_1937_, 1);
lean_inc_n(v_toBind_1942_, 2);
lean_dec_ref(v_inst_1937_);
lean_inc(v_inst_1938_);
lean_inc_n(v_a_1940_, 2);
v___f_1943_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1943_, 0, v_toApplicative_1941_);
lean_closure_set(v___f_1943_, 1, v_inst_1939_);
lean_closure_set(v___f_1943_, 2, v_toBind_1942_);
lean_closure_set(v___f_1943_, 3, v_a_1940_);
lean_closure_set(v___f_1943_, 4, v_inst_1938_);
v___x_1944_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1944_, 0, lean_box(0));
lean_closure_set(v___x_1944_, 1, lean_box(0));
lean_closure_set(v___x_1944_, 2, v_a_1940_);
v___x_1945_ = lean_apply_2(v_inst_1938_, lean_box(0), v___x_1944_);
v___x_1946_ = lean_apply_4(v_toBind_1942_, lean_box(0), lean_box(0), v___x_1945_, v___f_1943_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1947_, v_inst_1948_, v_inst_1949_, v_a_1950_);
lean_dec(v_a_1950_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_1952_, lean_object* v_00_u03b1_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_1954_, v_inst_1955_, v_inst_1956_, v_a_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object* v_m_1959_, lean_object* v_00_u03b1_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(v_m_1959_, v_00_u03b1_1960_, v_inst_1961_, v_inst_1962_, v_inst_1963_, v_a_1964_);
lean_dec(v_a_1964_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_1966_){
_start:
{
lean_object* v___x_1968_; lean_object* v_producers_1969_; lean_object* v_consumers_1970_; uint8_t v_closed_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1996_; 
v___x_1968_ = lean_st_ref_get(v_a_1966_);
v_producers_1969_ = lean_ctor_get(v___x_1968_, 0);
v_consumers_1970_ = lean_ctor_get(v___x_1968_, 1);
v_closed_1971_ = lean_ctor_get_uint8(v___x_1968_, sizeof(void*)*2);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1973_ = v___x_1968_;
v_isShared_1974_ = v_isSharedCheck_1996_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_consumers_1970_);
lean_inc(v_producers_1969_);
lean_dec(v___x_1968_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1996_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1969_);
if (lean_obj_tag(v___x_1975_) == 1)
{
lean_object* v_val_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1994_; 
v_val_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1994_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_val_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1994_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_fst_1980_; lean_object* v_snd_1981_; lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___x_1985_; 
v_fst_1980_ = lean_ctor_get(v_val_1976_, 0);
lean_inc(v_fst_1980_);
v_snd_1981_ = lean_ctor_get(v_val_1976_, 1);
lean_inc(v_snd_1981_);
lean_dec(v_val_1976_);
v_fst_1982_ = lean_ctor_get(v_fst_1980_, 0);
lean_inc(v_fst_1982_);
v_snd_1983_ = lean_ctor_get(v_fst_1980_, 1);
lean_inc(v_snd_1983_);
lean_dec(v_fst_1980_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v_snd_1981_);
v___x_1985_ = v___x_1973_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_snd_1981_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_consumers_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*2, v_closed_1971_);
v___x_1985_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1986_ = lean_st_ref_set(v_a_1966_, v___x_1985_);
v___x_1987_ = 1;
v___x_1988_ = lean_box(v___x_1987_);
v___x_1989_ = lean_io_promise_resolve(v___x_1988_, v_snd_1983_);
lean_dec(v_snd_1983_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v_fst_1982_);
v___x_1991_ = v___x_1978_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_fst_1982_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v___x_1995_; 
lean_dec(v___x_1975_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_consumers_1970_);
v___x_1995_ = lean_box(0);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_1997_);
lean_dec(v_a_1997_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_a_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_2004_, v_a_2005_);
lean_dec(v_a_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_2009_){
_start:
{
lean_object* v___f_2011_; lean_object* v___x_2012_; 
v___f_2011_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_2012_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2009_, v___f_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_2016_, lean_object* v_ch_2017_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2017_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_2020_, lean_object* v_ch_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_2020_, v_ch_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_st_ref_get(v___y_2025_);
v___x_2028_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_2025_);
if (lean_obj_tag(v___x_2028_) == 1)
{
lean_object* v___x_2029_; 
lean_dec(v___x_2027_);
lean_dec_ref(v___f_2024_);
v___x_2029_ = lean_task_pure(v___x_2028_);
return v___x_2029_;
}
else
{
uint8_t v_closed_2030_; 
lean_dec(v___x_2028_);
v_closed_2030_ = lean_ctor_get_uint8(v___x_2027_, sizeof(void*)*2);
if (v_closed_2030_ == 0)
{
lean_object* v_producers_2031_; lean_object* v_consumers_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2047_; 
v_producers_2031_ = lean_ctor_get(v___x_2027_, 0);
v_consumers_2032_ = lean_ctor_get(v___x_2027_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2034_ = v___x_2027_;
v_isShared_2035_ = v_isSharedCheck_2047_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_consumers_2032_);
lean_inc(v_producers_2031_);
lean_dec(v___x_2027_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2047_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2036_ = lean_io_promise_new();
lean_inc(v___x_2036_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
v___x_2038_ = l_Std_Queue_enqueue___redArg(v___x_2037_, v_consumers_2032_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v___x_2038_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_producers_2031_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v___x_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2046_, sizeof(void*)*2, v_closed_2030_);
v___x_2040_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2041_ = lean_st_ref_set(v___y_2025_, v___x_2040_);
v___x_2042_ = 1;
v___x_2043_ = lean_io_promise_result_opt(v___x_2036_);
lean_dec(v___x_2036_);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_task_map(v___f_2024_, v___x_2043_, v___x_2044_, v___x_2042_);
return v___x_2045_;
}
}
}
else
{
lean_object* v___x_2048_; 
lean_dec(v___x_2027_);
lean_dec_ref(v___f_2024_);
v___x_2048_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2049_, v___y_2050_);
lean_dec(v___y_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2055_){
_start:
{
lean_object* v___f_2057_; lean_object* v___x_2058_; 
v___f_2057_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2058_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2055_, v___f_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2062_, lean_object* v_ch_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2066_, lean_object* v_ch_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2066_, v_ch_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2070_, lean_object* v_a_2071_){
_start:
{
uint8_t v___y_2073_; lean_object* v_producers_2077_; uint8_t v_closed_2078_; uint8_t v___x_2079_; 
v_producers_2077_ = lean_ctor_get(v_a_2071_, 0);
v_closed_2078_ = lean_ctor_get_uint8(v_a_2071_, sizeof(void*)*2);
v___x_2079_ = l_Std_Queue_isEmpty___redArg(v_producers_2077_);
if (v___x_2079_ == 0)
{
uint8_t v___x_2080_; 
v___x_2080_ = 1;
v___y_2073_ = v___x_2080_;
goto v___jp_2072_;
}
else
{
v___y_2073_ = v_closed_2078_;
goto v___jp_2072_;
}
v___jp_2072_:
{
lean_object* v_toPure_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_toPure_2074_ = lean_ctor_get(v_toApplicative_2070_, 1);
lean_inc(v_toPure_2074_);
lean_dec_ref(v_toApplicative_2070_);
v___x_2075_ = lean_box(v___y_2073_);
v___x_2076_ = lean_apply_2(v_toPure_2074_, lean_box(0), v___x_2075_);
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2081_, v_a_2082_);
lean_dec_ref(v_a_2082_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2084_, lean_object* v_inst_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_toApplicative_2087_; lean_object* v_toBind_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_toApplicative_2087_ = lean_ctor_get(v_inst_2084_, 0);
lean_inc_ref(v_toApplicative_2087_);
v_toBind_2088_ = lean_ctor_get(v_inst_2084_, 1);
lean_inc(v_toBind_2088_);
lean_dec_ref(v_inst_2084_);
v___f_2089_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2089_, 0, v_toApplicative_2087_);
lean_inc(v_a_2086_);
v___x_2090_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2090_, 0, lean_box(0));
lean_closure_set(v___x_2090_, 1, lean_box(0));
lean_closure_set(v___x_2090_, 2, v_a_2086_);
v___x_2091_ = lean_apply_2(v_inst_2085_, lean_box(0), v___x_2090_);
v___x_2092_ = lean_apply_4(v_toBind_2088_, lean_box(0), lean_box(0), v___x_2091_, v___f_2089_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(v_inst_2093_, v_inst_2094_, v_a_2095_);
lean_dec(v_a_2095_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2097_, lean_object* v_00_u03b1_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_toApplicative_2102_; lean_object* v_toBind_2103_; lean_object* v___f_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_toApplicative_2102_ = lean_ctor_get(v_inst_2099_, 0);
lean_inc_ref(v_toApplicative_2102_);
v_toBind_2103_ = lean_ctor_get(v_inst_2099_, 1);
lean_inc(v_toBind_2103_);
lean_dec_ref(v_inst_2099_);
v___f_2104_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2104_, 0, v_toApplicative_2102_);
lean_inc(v_a_2101_);
v___x_2105_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2105_, 0, lean_box(0));
lean_closure_set(v___x_2105_, 1, lean_box(0));
lean_closure_set(v___x_2105_, 2, v_a_2101_);
v___x_2106_ = lean_apply_2(v_inst_2100_, lean_box(0), v___x_2105_);
v___x_2107_ = lean_apply_4(v_toBind_2103_, lean_box(0), lean_box(0), v___x_2106_, v___f_2104_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object* v_m_2108_, lean_object* v_00_u03b1_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(v_m_2108_, v_00_u03b1_2109_, v_inst_2110_, v_inst_2111_, v_a_2112_);
lean_dec(v_a_2112_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2114_, lean_object* v___f_2115_, lean_object* v_x_2116_){
_start:
{
if (lean_obj_tag(v_x_2116_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v___f_2115_);
v_a_2118_ = lean_ctor_get(v_x_2116_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_x_2116_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2120_ = v_x_2116_;
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v_x_2116_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
}
else
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2140_; 
v_isSharedCheck_2140_ = !lean_is_exclusive(v_x_2116_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v_x_2116_, 0);
lean_dec(v_unused_2141_);
v___x_2128_ = v_x_2116_;
v_isShared_2129_ = v_isSharedCheck_2140_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v_x_2116_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2140_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2130_ = 1;
v___x_2131_ = lean_box(v___x_2130_);
v___x_2132_ = lean_io_promise_resolve(v___x_2131_, v_snd_2114_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2132_);
v___x_2134_ = v___x_2128_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
v___x_2136_ = lean_unsigned_to_nat(0u);
v___x_2137_ = 0;
v___x_2138_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2136_, v___x_2137_, v___x_2135_, v___f_2115_);
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2142_, lean_object* v___f_2143_, lean_object* v_x_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2142_, v___f_2143_, v_x_2144_);
lean_dec(v_snd_2142_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2147_, lean_object* v_x_2148_){
_start:
{
if (lean_obj_tag(v_x_2148_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2158_; 
v_a_2150_ = lean_ctor_get(v_x_2148_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_x_2148_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2152_ = v_x_2148_;
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v_x_2148_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2196_; 
v_a_2159_ = lean_ctor_get(v_x_2148_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_x_2148_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2161_ = v_x_2148_;
v_isShared_2162_ = v_isSharedCheck_2196_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v_x_2148_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2196_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_producers_2163_; lean_object* v_consumers_2164_; uint8_t v_closed_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2195_; 
v_producers_2163_ = lean_ctor_get(v_a_2159_, 0);
v_consumers_2164_ = lean_ctor_get(v_a_2159_, 1);
v_closed_2165_ = lean_ctor_get_uint8(v_a_2159_, sizeof(void*)*2);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_a_2159_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2167_ = v_a_2159_;
v_isShared_2168_ = v_isSharedCheck_2195_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_consumers_2164_);
lean_inc(v_producers_2163_);
lean_dec(v_a_2159_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2195_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2163_);
if (lean_obj_tag(v___x_2169_) == 1)
{
lean_object* v_val_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2193_; 
v_val_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2193_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_val_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2193_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_fst_2174_; lean_object* v_snd_2175_; lean_object* v_fst_2176_; lean_object* v_snd_2177_; lean_object* v___x_2179_; 
v_fst_2174_ = lean_ctor_get(v_val_2170_, 0);
lean_inc(v_fst_2174_);
v_snd_2175_ = lean_ctor_get(v_val_2170_, 1);
lean_inc(v_snd_2175_);
lean_dec(v_val_2170_);
v_fst_2176_ = lean_ctor_get(v_fst_2174_, 0);
lean_inc(v_fst_2176_);
v_snd_2177_ = lean_ctor_get(v_fst_2174_, 1);
lean_inc(v_snd_2177_);
lean_dec(v_fst_2174_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v_snd_2175_);
v___x_2179_ = v___x_2167_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_snd_2175_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_consumers_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, sizeof(void*)*2, v_closed_2165_);
v___x_2179_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; lean_object* v___f_2181_; lean_object* v___f_2182_; lean_object* v___x_2184_; 
v___x_2180_ = lean_st_ref_set(v_a_2147_, v___x_2179_);
v___f_2181_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2181_, 0, v_fst_2176_);
v___f_2182_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2182_, 0, v_snd_2177_);
lean_closure_set(v___f_2182_, 1, v___f_2181_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2180_);
v___x_2184_ = v___x_2161_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2180_);
v___x_2184_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2184_);
v___x_2186_ = v___x_2172_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; uint8_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = 0;
v___x_2189_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2187_, v___x_2188_, v___x_2186_, v___f_2182_);
return v___x_2189_;
}
}
}
}
}
else
{
lean_object* v___x_2194_; 
lean_dec(v___x_2169_);
lean_del_object(v___x_2167_);
lean_dec_ref(v_consumers_2164_);
lean_del_object(v___x_2161_);
v___x_2194_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2197_, lean_object* v_x_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2197_, v_x_2198_);
lean_dec(v_a_2197_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2201_){
_start:
{
lean_object* v___x_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; 
v___x_2203_ = lean_st_ref_get(v_a_2201_);
lean_inc(v_a_2201_);
v___f_2204_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2204_, 0, v_a_2201_);
v___x_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = 0;
v___x_2209_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2207_, v___x_2208_, v___x_2206_, v___f_2204_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2210_);
lean_dec(v_a_2210_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2217_, lean_object* v_a_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2217_, v_a_2218_);
lean_dec(v_a_2218_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2221_, lean_object* v___y_2222_, lean_object* v___f_2223_, lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2234_; 
lean_dec_ref(v___f_2223_);
lean_dec_ref(v_lose_2221_);
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
lean_object* v_a_2235_; uint8_t v___x_2236_; 
v_a_2235_ = lean_ctor_get(v_x_2224_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v_x_2224_);
v___x_2236_ = lean_unbox(v_a_2235_);
lean_dec(v_a_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; 
lean_dec_ref(v___f_2223_);
lean_inc(v___y_2222_);
v___x_2237_ = lean_apply_2(v_lose_2221_, v___y_2222_, lean_box(0));
return v___x_2237_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; lean_object* v___x_2241_; 
lean_dec_ref(v_lose_2221_);
v___x_2238_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2222_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = 0;
v___x_2241_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2239_, v___x_2240_, v___x_2238_, v___f_2223_);
return v___x_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2242_, lean_object* v___y_2243_, lean_object* v___f_2244_, lean_object* v_x_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2242_, v___y_2243_, v___f_2244_, v_x_2245_);
lean_dec(v___y_2243_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2248_, lean_object* v_lose_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_finished_2252_; lean_object* v_promise_2253_; lean_object* v___x_2254_; lean_object* v___f_2255_; lean_object* v___f_2256_; uint8_t v___y_2258_; uint8_t v___x_2268_; 
v_finished_2252_ = lean_ctor_get(v_w_2248_, 0);
lean_inc(v_finished_2252_);
v_promise_2253_ = lean_ctor_get(v_w_2248_, 1);
lean_inc(v_promise_2253_);
lean_dec_ref(v_w_2248_);
v___x_2254_ = lean_st_ref_take(v_finished_2252_);
v___f_2255_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2255_, 0, v_promise_2253_);
lean_inc(v___y_2250_);
v___f_2256_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2256_, 0, v_lose_2249_);
lean_closure_set(v___f_2256_, 1, v___y_2250_);
lean_closure_set(v___f_2256_, 2, v___f_2255_);
v___x_2268_ = lean_unbox(v___x_2254_);
lean_dec(v___x_2254_);
if (v___x_2268_ == 0)
{
uint8_t v___x_2269_; 
v___x_2269_ = 1;
v___y_2258_ = v___x_2269_;
goto v___jp_2257_;
}
else
{
uint8_t v___x_2270_; 
v___x_2270_ = 0;
v___y_2258_ = v___x_2270_;
goto v___jp_2257_;
}
v___jp_2257_:
{
uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; 
v___x_2259_ = 1;
v___x_2260_ = lean_box(v___x_2259_);
v___x_2261_ = lean_st_ref_set(v_finished_2252_, v___x_2260_);
lean_dec(v_finished_2252_);
v___x_2262_ = lean_box(v___y_2258_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = 0;
v___x_2267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2265_, v___x_2266_, v___x_2264_, v___f_2256_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2271_, lean_object* v_lose_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2271_, v_lose_2272_, v___y_2273_);
lean_dec(v___y_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2276_, lean_object* v_w_2277_, lean_object* v_lose_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2277_, v_lose_2278_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_w_2283_, lean_object* v_lose_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2282_, v_w_2283_, v_lose_2284_, v___y_2285_);
lean_dec(v___y_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2288_){
_start:
{
uint8_t v___y_2291_; 
if (lean_obj_tag(v_x_2288_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2303_; 
v_a_2295_ = lean_ctor_get(v_x_2288_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_x_2288_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2297_ = v_x_2288_;
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v_x_2288_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v_producers_2305_; uint8_t v_closed_2306_; uint8_t v___x_2307_; 
v_a_2304_ = lean_ctor_get(v_x_2288_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v_x_2288_);
v_producers_2305_ = lean_ctor_get(v_a_2304_, 0);
lean_inc_ref(v_producers_2305_);
v_closed_2306_ = lean_ctor_get_uint8(v_a_2304_, sizeof(void*)*2);
lean_dec(v_a_2304_);
v___x_2307_ = l_Std_Queue_isEmpty___redArg(v_producers_2305_);
lean_dec_ref(v_producers_2305_);
if (v___x_2307_ == 0)
{
uint8_t v___x_2308_; 
v___x_2308_ = 1;
v___y_2291_ = v___x_2308_;
goto v___jp_2290_;
}
else
{
v___y_2291_ = v_closed_2306_;
goto v___jp_2290_;
}
}
v___jp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(v___y_2291_);
v___x_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2312_, lean_object* v_waiter_2313_, lean_object* v_x_2314_){
_start:
{
if (lean_obj_tag(v_x_2314_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref(v_waiter_2313_);
v_a_2316_ = lean_ctor_get(v_x_2314_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_x_2314_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2318_ = v_x_2314_;
v_isShared_2319_ = v_isSharedCheck_2324_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v_x_2314_);
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
lean_object* v_a_2325_; uint8_t v___x_2326_; 
v_a_2325_ = lean_ctor_get(v_x_2314_, 0);
lean_inc(v_a_2325_);
lean_dec_ref(v_x_2314_);
v___x_2326_ = lean_unbox(v_a_2325_);
lean_dec(v_a_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v_producers_2328_; lean_object* v_consumers_2329_; uint8_t v_closed_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2341_; 
v___x_2327_ = lean_st_ref_take(v___y_2312_);
v_producers_2328_ = lean_ctor_get(v___x_2327_, 0);
v_consumers_2329_ = lean_ctor_get(v___x_2327_, 1);
v_closed_2330_ = lean_ctor_get_uint8(v___x_2327_, sizeof(void*)*2);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2332_ = v___x_2327_;
v_isShared_2333_ = v_isSharedCheck_2341_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_consumers_2329_);
lean_inc(v_producers_2328_);
lean_dec(v___x_2327_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2341_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_waiter_2313_);
v___x_2335_ = l_Std_Queue_enqueue___redArg(v___x_2334_, v_consumers_2329_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 1, v___x_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_producers_2328_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___x_2335_);
lean_ctor_set_uint8(v_reuseFailAlloc_2340_, sizeof(void*)*2, v_closed_2330_);
v___x_2337_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_st_ref_set(v___y_2312_, v___x_2337_);
v___x_2339_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_2339_;
}
}
}
else
{
lean_object* v_lose_2342_; lean_object* v___x_2343_; 
v_lose_2342_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2));
v___x_2343_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2313_, v_lose_2342_, v___y_2312_);
return v___x_2343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2344_, lean_object* v_waiter_2345_, lean_object* v_x_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2344_, v_waiter_2345_, v_x_2346_);
lean_dec(v___y_2344_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v___f_2349_, lean_object* v_waiter_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; 
v___x_2353_ = lean_st_ref_get(v___y_2351_);
v___x_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = 0;
v___x_2358_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2356_, v___x_2357_, v___x_2355_, v___f_2349_);
lean_inc(v___y_2351_);
v___f_2359_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2359_, 0, v___y_2351_);
lean_closure_set(v___f_2359_, 1, v_waiter_2350_);
v___x_2360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2356_, v___x_2357_, v___x_2358_, v___f_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v___f_2361_, lean_object* v_waiter_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v___f_2361_, v_waiter_2362_, v___y_2363_);
lean_dec(v___y_2363_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2366_, lean_object* v_ch_2367_, lean_object* v_waiter_2368_){
_start:
{
lean_object* v___f_2370_; lean_object* v___x_2371_; 
v___f_2370_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2370_, 0, v___f_2366_);
lean_closure_set(v___f_2370_, 1, v_waiter_2368_);
v___x_2371_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2367_, v___f_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2372_, lean_object* v_ch_2373_, lean_object* v_waiter_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2372_, v_ch_2373_, v_waiter_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2377_, lean_object* v___f_2378_, lean_object* v_x_2379_){
_start:
{
if (lean_obj_tag(v_x_2379_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v___f_2378_);
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
lean_object* v_a_2390_; uint8_t v___x_2391_; 
v_a_2390_ = lean_ctor_get(v_x_2379_, 0);
lean_inc(v_a_2390_);
lean_dec_ref(v_x_2379_);
v___x_2391_ = lean_unbox(v_a_2390_);
lean_dec(v_a_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2392_; 
lean_dec_ref(v___f_2378_);
v___x_2392_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2392_;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2393_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2377_);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = 0;
v___x_2396_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2394_, v___x_2395_, v___x_2393_, v___f_2378_);
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2397_, lean_object* v___f_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2397_, v___f_2398_, v_x_2399_);
lean_dec(v___y_2397_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2402_, lean_object* v___f_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; lean_object* v___f_2412_; lean_object* v___x_2413_; 
v___x_2406_ = lean_st_ref_get(v___y_2404_);
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = lean_unsigned_to_nat(0u);
v___x_2410_ = 0;
v___x_2411_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2409_, v___x_2410_, v___x_2408_, v___f_2402_);
lean_inc(v___y_2404_);
v___f_2412_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2412_, 0, v___y_2404_);
lean_closure_set(v___f_2412_, 1, v___f_2403_);
v___x_2413_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2409_, v___x_2410_, v___x_2411_, v___f_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2414_, lean_object* v___f_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2414_, v___f_2415_, v___y_2416_);
lean_dec(v___y_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2419_, uint8_t v_closed_2420_, lean_object* v___y_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v_producers_2419_);
v_a_2424_ = lean_ctor_get(v_x_2422_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_x_2422_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2426_ = v_x_2422_;
v_isShared_2427_ = v_isSharedCheck_2432_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v_x_2422_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2432_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2443_; 
v_a_2433_ = lean_ctor_get(v_x_2422_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2422_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2435_ = v_x_2422_;
v_isShared_2436_ = v_isSharedCheck_2443_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v_x_2422_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2443_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2437_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2437_, 0, v_producers_2419_);
lean_ctor_set(v___x_2437_, 1, v_a_2433_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*2, v_closed_2420_);
v___x_2438_ = lean_st_ref_set(v___y_2421_, v___x_2437_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2438_);
v___x_2440_ = v___x_2435_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
return v___x_2441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2444_, lean_object* v_closed_2445_, lean_object* v___y_2446_, lean_object* v_x_2447_, lean_object* v___y_2448_){
_start:
{
uint8_t v_closed_boxed_2449_; lean_object* v_res_2450_; 
v_closed_boxed_2449_ = lean_unbox(v_closed_2445_);
v_res_2450_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2444_, v_closed_boxed_2449_, v___y_2446_, v_x_2447_);
lean_dec(v___y_2446_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2451_, lean_object* v_x_2452_, lean_object* v_head_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2451_, v_x_2452_, v_head_2453_, v_x_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2457_, lean_object* v_x_2458_){
_start:
{
if (lean_obj_tag(v_x_2457_) == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_x_2458_);
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
return v___x_2461_;
}
else
{
lean_object* v_head_2462_; lean_object* v_tail_2463_; lean_object* v___f_2464_; lean_object* v_val_2466_; 
v_head_2462_ = lean_ctor_get(v_x_2457_, 0);
lean_inc_n(v_head_2462_, 2);
v_tail_2463_ = lean_ctor_get(v_x_2457_, 1);
lean_inc(v_tail_2463_);
lean_dec_ref(v_x_2457_);
v___f_2464_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2464_, 0, v_tail_2463_);
lean_closure_set(v___f_2464_, 1, v_x_2458_);
lean_closure_set(v___f_2464_, 2, v_head_2462_);
if (lean_obj_tag(v_head_2462_) == 0)
{
lean_object* v___x_2470_; 
lean_dec_ref(v_head_2462_);
v___x_2470_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_2466_ = v___x_2470_;
goto v___jp_2465_;
}
else
{
lean_object* v_finished_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2485_; 
v_finished_2471_ = lean_ctor_get(v_head_2462_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_head_2462_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2473_ = v_head_2462_;
v_isShared_2474_ = v_isSharedCheck_2485_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_finished_2471_);
lean_dec(v_head_2462_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2485_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v_finished_2475_; lean_object* v___x_2476_; lean_object* v___f_2477_; lean_object* v___x_2479_; 
v_finished_2475_ = lean_ctor_get(v_finished_2471_, 0);
lean_inc(v_finished_2475_);
lean_dec_ref(v_finished_2471_);
v___x_2476_ = lean_st_ref_get(v_finished_2475_);
lean_dec(v_finished_2475_);
v___f_2477_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2476_);
v___x_2479_ = v___x_2473_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2476_);
v___x_2479_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
v___x_2481_ = lean_unsigned_to_nat(0u);
v___x_2482_ = 0;
v___x_2483_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2481_, v___x_2482_, v___x_2480_, v___f_2477_);
v_val_2466_ = v___x_2483_;
goto v___jp_2465_;
}
}
}
v___jp_2465_:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = 0;
v___x_2469_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2467_, v___x_2468_, v_val_2466_, v___f_2464_);
return v___x_2469_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2486_, lean_object* v_x_2487_, lean_object* v_head_2488_, lean_object* v_x_2489_){
_start:
{
if (lean_obj_tag(v_x_2489_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2499_; 
lean_dec_ref(v_head_2488_);
lean_dec(v_x_2487_);
lean_dec(v_tail_2486_);
v_a_2491_ = lean_ctor_get(v_x_2489_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_x_2489_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2493_ = v_x_2489_;
v_isShared_2494_ = v_isSharedCheck_2499_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v_x_2489_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2499_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
return v___x_2497_;
}
}
}
else
{
lean_object* v_a_2500_; uint8_t v___x_2501_; 
v_a_2500_ = lean_ctor_get(v_x_2489_, 0);
lean_inc(v_a_2500_);
lean_dec_ref(v_x_2489_);
v___x_2501_ = lean_unbox(v_a_2500_);
lean_dec(v_a_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
lean_dec_ref(v_head_2488_);
v___x_2502_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2486_, v_x_2487_);
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_head_2488_);
lean_ctor_set(v___x_2503_, 1, v_x_2487_);
v___x_2504_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2486_, v___x_2503_);
return v___x_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2505_, lean_object* v_x_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2505_, v_x_2506_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v_eList_2509_, lean_object* v___x_2510_, lean_object* v___f_2511_, lean_object* v_x_2512_){
_start:
{
if (lean_obj_tag(v_x_2512_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2522_; 
lean_dec_ref(v___f_2511_);
lean_dec(v___x_2510_);
lean_dec(v_eList_2509_);
v_a_2514_ = lean_ctor_get(v_x_2512_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_x_2512_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2516_ = v_x_2512_;
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v_x_2512_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___x_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; 
v_a_2523_ = lean_ctor_get(v_x_2512_, 0);
lean_inc(v_a_2523_);
lean_dec_ref(v_x_2512_);
lean_inc(v___x_2510_);
v___x_2524_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2509_, v___x_2510_);
v___x_2525_ = lean_unsigned_to_nat(0u);
v___x_2526_ = 0;
v___x_2527_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2525_, v___x_2526_, v___x_2524_, v___f_2511_);
v___f_2528_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2528_, 0, v_a_2523_);
lean_closure_set(v___f_2528_, 1, v___x_2510_);
v___x_2529_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2525_, v___x_2526_, v___x_2527_, v___f_2528_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_eList_2530_, lean_object* v___x_2531_, lean_object* v___f_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v_eList_2530_, v___x_2531_, v___f_2532_, v_x_2533_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_eList_2539_; lean_object* v_dList_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; 
v_eList_2539_ = lean_ctor_get(v_q_2536_, 0);
lean_inc(v_eList_2539_);
v_dList_2540_ = lean_ctor_get(v_q_2536_, 1);
lean_inc(v_dList_2540_);
lean_dec_ref(v_q_2536_);
v___x_2541_ = lean_box(0);
v___x_2542_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2540_, v___x_2541_);
v___f_2543_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = 0;
v___x_2546_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2544_, v___x_2545_, v___x_2542_, v___f_2543_);
v___f_2547_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2547_, 0, v_eList_2539_);
lean_closure_set(v___f_2547_, 1, v___x_2541_);
lean_closure_set(v___f_2547_, 2, v___f_2543_);
v___x_2548_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2544_, v___x_2545_, v___x_2546_, v___f_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2549_, v___y_2550_);
lean_dec(v___y_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2553_, lean_object* v_x_2554_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
v_a_2556_ = lean_ctor_get(v_x_2554_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_x_2554_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2558_ = v_x_2554_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v_x_2554_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v_producers_2566_; lean_object* v_consumers_2567_; uint8_t v_closed_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; 
v_a_2565_ = lean_ctor_get(v_x_2554_, 0);
lean_inc(v_a_2565_);
lean_dec_ref(v_x_2554_);
v_producers_2566_ = lean_ctor_get(v_a_2565_, 0);
lean_inc_ref(v_producers_2566_);
v_consumers_2567_ = lean_ctor_get(v_a_2565_, 1);
lean_inc_ref(v_consumers_2567_);
v_closed_2568_ = lean_ctor_get_uint8(v_a_2565_, sizeof(void*)*2);
lean_dec(v_a_2565_);
v___x_2569_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2567_, v___y_2553_);
v___x_2570_ = lean_box(v_closed_2568_);
lean_inc(v___y_2553_);
v___f_2571_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2571_, 0, v_producers_2566_);
lean_closure_set(v___f_2571_, 1, v___x_2570_);
lean_closure_set(v___f_2571_, 2, v___y_2553_);
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = 0;
v___x_2574_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2572_, v___x_2573_, v___x_2569_, v___f_2571_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2575_, lean_object* v_x_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2575_, v_x_2576_);
lean_dec(v___y_2575_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; 
v___x_2581_ = lean_st_ref_get(v___y_2579_);
lean_inc(v___y_2579_);
v___f_2582_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2582_, 0, v___y_2579_);
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
v___x_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = 0;
v___x_2587_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2585_, v___x_2586_, v___x_2584_, v___f_2582_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2588_);
lean_dec(v___y_2588_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2596_){
_start:
{
lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___f_2597_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref_n(v_ch_2596_, 2);
v___f_2598_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2598_, 0, v___f_2597_);
lean_closure_set(v___f_2598_, 1, v_ch_2596_);
v___f_2599_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2600_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
v___x_2601_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2601_, 0, lean_box(0));
lean_closure_set(v___x_2601_, 1, lean_box(0));
lean_closure_set(v___x_2601_, 2, v_ch_2596_);
lean_closure_set(v___x_2601_, 3, v___f_2599_);
v___x_2602_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2602_, 0, lean_box(0));
lean_closure_set(v___x_2602_, 1, lean_box(0));
lean_closure_set(v___x_2602_, 2, v_ch_2596_);
lean_closure_set(v___x_2602_, 3, v___f_2600_);
v___x_2603_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___f_2598_);
lean_ctor_set(v___x_2603_, 2, v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2604_, lean_object* v_ch_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2607_, lean_object* v_q_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2608_, v___y_2609_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2612_, lean_object* v_q_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2612_, v_q_2613_, v___y_2614_);
lean_dec(v___y_2614_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2618_, v_x_2619_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2623_, lean_object* v_x_2624_, lean_object* v_x_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2623_, v_x_2624_, v_x_2625_, v___y_2626_);
lean_dec(v___y_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2629_, uint8_t v_b_2630_){
_start:
{
lean_object* v_promise_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v_promise_2632_ = lean_ctor_get(v_c_2629_, 0);
v___x_2633_ = lean_box(v_b_2630_);
v___x_2634_ = lean_io_promise_resolve(v___x_2633_, v_promise_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2635_, lean_object* v_b_2636_, lean_object* v_a_2637_){
_start:
{
uint8_t v_b_boxed_2638_; lean_object* v_res_2639_; 
v_b_boxed_2638_ = lean_unbox(v_b_2636_);
v_res_2639_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2635_, v_b_boxed_2638_);
lean_dec_ref(v_c_2635_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2640_, lean_object* v_c_2641_, uint8_t v_b_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2641_, v_b_2642_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2645_, lean_object* v_c_2646_, lean_object* v_b_2647_, lean_object* v_a_2648_){
_start:
{
uint8_t v_b_boxed_2649_; lean_object* v_res_2650_; 
v_b_boxed_2649_ = lean_unbox(v_b_2647_);
v_res_2650_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2645_, v_c_2646_, v_b_boxed_2649_);
lean_dec_ref(v_c_2646_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2651_){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_box(0);
v___x_2654_ = lean_st_mk_ref(v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2655_);
lean_dec(v_x_2655_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2658_, lean_object* v_f_2659_, lean_object* v_xs_2660_, lean_object* v_k_2661_, lean_object* v_acc_2662_){
_start:
{
uint8_t v___x_2664_; 
v___x_2664_ = lean_nat_dec_lt(v_k_2661_, v_n_2658_);
if (v___x_2664_ == 0)
{
lean_dec(v_k_2661_);
lean_dec_ref(v_f_2659_);
return v_acc_2662_;
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2665_ = lean_array_fget_borrowed(v_xs_2660_, v_k_2661_);
lean_inc_ref(v_f_2659_);
lean_inc(v___x_2665_);
v___x_2666_ = lean_apply_2(v_f_2659_, v___x_2665_, lean_box(0));
v___x_2667_ = lean_unsigned_to_nat(1u);
v___x_2668_ = lean_nat_add(v_k_2661_, v___x_2667_);
lean_dec(v_k_2661_);
v___x_2669_ = lean_array_push(v_acc_2662_, v___x_2666_);
v_k_2661_ = v___x_2668_;
v_acc_2662_ = v___x_2669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2671_, lean_object* v_f_2672_, lean_object* v_xs_2673_, lean_object* v_k_2674_, lean_object* v_acc_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2671_, v_f_2672_, v_xs_2673_, v_k_2674_, v_acc_2675_);
lean_dec_ref(v_xs_2673_);
lean_dec(v_n_2671_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2681_){
_start:
{
lean_object* v___f_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___f_2683_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2681_);
v___x_2684_ = l_Array_range(v_capacity_2681_);
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2687_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2681_, v___f_2683_, v___x_2684_, v___x_2685_, v___x_2686_);
lean_dec_ref(v___x_2684_);
v___x_2688_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2689_ = 0;
v___x_2690_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set(v___x_2690_, 1, v___x_2688_);
lean_ctor_set(v___x_2690_, 2, v_capacity_2681_);
lean_ctor_set(v___x_2690_, 3, v___x_2687_);
lean_ctor_set(v___x_2690_, 4, v___x_2685_);
lean_ctor_set(v___x_2690_, 5, v___x_2685_);
lean_ctor_set(v___x_2690_, 6, v___x_2685_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*7, v___x_2689_);
v___x_2691_ = l_Std_Mutex_new___redArg(v___x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2695_, lean_object* v_capacity_2696_, lean_object* v_hcap_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2696_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2700_, lean_object* v_capacity_2701_, lean_object* v_hcap_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2700_, v_capacity_2701_, v_hcap_2702_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2705_, lean_object* v_00_u03b2_2706_, lean_object* v_n_2707_, lean_object* v_f_2708_, lean_object* v_xs_2709_, lean_object* v_k_2710_, lean_object* v_h_2711_, lean_object* v_acc_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2707_, v_f_2708_, v_xs_2709_, v_k_2710_, v_acc_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2715_, lean_object* v_00_u03b2_2716_, lean_object* v_n_2717_, lean_object* v_f_2718_, lean_object* v_xs_2719_, lean_object* v_k_2720_, lean_object* v_h_2721_, lean_object* v_acc_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2715_, v_00_u03b2_2716_, v_n_2717_, v_f_2718_, v_xs_2719_, v_k_2720_, v_h_2721_, v_acc_2722_);
lean_dec_ref(v_xs_2719_);
lean_dec(v_n_2717_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2725_, lean_object* v_cap_2726_){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2727_ = lean_unsigned_to_nat(1u);
v___x_2728_ = lean_nat_add(v_idx_2725_, v___x_2727_);
v___x_2729_ = lean_nat_dec_eq(v___x_2728_, v_cap_2726_);
if (v___x_2729_ == 0)
{
return v___x_2728_;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v___x_2728_);
v___x_2730_ = lean_unsigned_to_nat(0u);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2731_, lean_object* v_cap_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2731_, v_cap_2732_);
lean_dec(v_cap_2732_);
lean_dec(v_idx_2731_);
return v_res_2733_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_st_2738_; lean_object* v___y_2739_; lean_object* v___x_2742_; lean_object* v_producers_2743_; lean_object* v_consumers_2744_; lean_object* v_capacity_2745_; lean_object* v_buf_2746_; lean_object* v_bufCount_2747_; lean_object* v_sendIdx_2748_; lean_object* v_recvIdx_2749_; uint8_t v_closed_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2776_; 
v___x_2742_ = lean_st_ref_get(v_a_2735_);
v_producers_2743_ = lean_ctor_get(v___x_2742_, 0);
v_consumers_2744_ = lean_ctor_get(v___x_2742_, 1);
v_capacity_2745_ = lean_ctor_get(v___x_2742_, 2);
v_buf_2746_ = lean_ctor_get(v___x_2742_, 3);
v_bufCount_2747_ = lean_ctor_get(v___x_2742_, 4);
v_sendIdx_2748_ = lean_ctor_get(v___x_2742_, 5);
v_recvIdx_2749_ = lean_ctor_get(v___x_2742_, 6);
v_closed_2750_ = lean_ctor_get_uint8(v___x_2742_, sizeof(void*)*7);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2752_ = v___x_2742_;
v_isShared_2753_ = v_isSharedCheck_2776_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_recvIdx_2749_);
lean_inc(v_sendIdx_2748_);
lean_inc(v_bufCount_2747_);
lean_inc(v_buf_2746_);
lean_inc(v_capacity_2745_);
lean_inc(v_consumers_2744_);
lean_inc(v_producers_2743_);
lean_dec(v___x_2742_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2776_;
goto v_resetjp_2751_;
}
v___jp_2737_:
{
lean_object* v___x_2740_; uint8_t v___x_2741_; 
v___x_2740_ = lean_st_ref_set(v___y_2739_, v_st_2738_);
v___x_2741_ = 1;
return v___x_2741_;
}
v_resetjp_2751_:
{
uint8_t v___x_2754_; 
v___x_2754_ = lean_nat_dec_eq(v_bufCount_2747_, v_capacity_2745_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___y_2761_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2755_ = lean_array_fget_borrowed(v_buf_2746_, v_sendIdx_2748_);
v___x_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_v_2734_);
v___x_2757_ = lean_st_ref_set(v___x_2755_, v___x_2756_);
v___x_2758_ = lean_unsigned_to_nat(1u);
v___x_2759_ = lean_nat_add(v_bufCount_2747_, v___x_2758_);
lean_dec(v_bufCount_2747_);
v___x_2772_ = lean_nat_add(v_sendIdx_2748_, v___x_2758_);
lean_dec(v_sendIdx_2748_);
v___x_2773_ = lean_nat_dec_eq(v___x_2772_, v_capacity_2745_);
if (v___x_2773_ == 0)
{
v___y_2761_ = v___x_2772_;
goto v___jp_2760_;
}
else
{
lean_object* v___x_2774_; 
lean_dec(v___x_2772_);
v___x_2774_ = lean_unsigned_to_nat(0u);
v___y_2761_ = v___x_2774_;
goto v___jp_2760_;
}
v___jp_2760_:
{
lean_object* v___x_2763_; 
lean_inc(v_recvIdx_2749_);
lean_inc(v___y_2761_);
lean_inc(v___x_2759_);
lean_inc_ref(v_buf_2746_);
lean_inc(v_capacity_2745_);
lean_inc_ref(v_consumers_2744_);
lean_inc_ref(v_producers_2743_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set(v___x_2752_, 5, v___y_2761_);
lean_ctor_set(v___x_2752_, 4, v___x_2759_);
v___x_2763_ = v___x_2752_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_producers_2743_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_consumers_2744_);
lean_ctor_set(v_reuseFailAlloc_2771_, 2, v_capacity_2745_);
lean_ctor_set(v_reuseFailAlloc_2771_, 3, v_buf_2746_);
lean_ctor_set(v_reuseFailAlloc_2771_, 4, v___x_2759_);
lean_ctor_set(v_reuseFailAlloc_2771_, 5, v___y_2761_);
lean_ctor_set(v_reuseFailAlloc_2771_, 6, v_recvIdx_2749_);
lean_ctor_set_uint8(v_reuseFailAlloc_2771_, sizeof(void*)*7, v_closed_2750_);
v___x_2763_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2744_);
if (lean_obj_tag(v___x_2764_) == 1)
{
lean_object* v_val_2765_; lean_object* v_fst_2766_; lean_object* v_snd_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec_ref(v___x_2763_);
v_val_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_val_2765_);
lean_dec_ref(v___x_2764_);
v_fst_2766_ = lean_ctor_get(v_val_2765_, 0);
lean_inc(v_fst_2766_);
v_snd_2767_ = lean_ctor_get(v_val_2765_, 1);
lean_inc(v_snd_2767_);
lean_dec(v_val_2765_);
v___x_2768_ = 1;
v___x_2769_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2766_, v___x_2768_);
lean_dec(v_fst_2766_);
v___x_2770_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2770_, 0, v_producers_2743_);
lean_ctor_set(v___x_2770_, 1, v_snd_2767_);
lean_ctor_set(v___x_2770_, 2, v_capacity_2745_);
lean_ctor_set(v___x_2770_, 3, v_buf_2746_);
lean_ctor_set(v___x_2770_, 4, v___x_2759_);
lean_ctor_set(v___x_2770_, 5, v___y_2761_);
lean_ctor_set(v___x_2770_, 6, v_recvIdx_2749_);
lean_ctor_set_uint8(v___x_2770_, sizeof(void*)*7, v_closed_2750_);
v_st_2738_ = v___x_2770_;
v___y_2739_ = v_a_2735_;
goto v___jp_2737_;
}
else
{
lean_dec(v___x_2764_);
lean_dec(v___y_2761_);
lean_dec(v___x_2759_);
lean_dec(v_recvIdx_2749_);
lean_dec_ref(v_buf_2746_);
lean_dec(v_capacity_2745_);
lean_dec_ref(v_producers_2743_);
v_st_2738_ = v___x_2763_;
v___y_2739_ = v_a_2735_;
goto v___jp_2737_;
}
}
}
}
else
{
uint8_t v___x_2775_; 
lean_del_object(v___x_2752_);
lean_dec(v_recvIdx_2749_);
lean_dec(v_sendIdx_2748_);
lean_dec(v_bufCount_2747_);
lean_dec_ref(v_buf_2746_);
lean_dec(v_capacity_2745_);
lean_dec_ref(v_consumers_2744_);
lean_dec_ref(v_producers_2743_);
lean_dec(v_v_2734_);
v___x_2775_ = 0;
return v___x_2775_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_res_2780_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2777_, v_a_2778_);
lean_dec(v_a_2778_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2782_, lean_object* v_v_2783_, lean_object* v_a_2784_){
_start:
{
uint8_t v___x_2786_; 
v___x_2786_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2783_, v_a_2784_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_v_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
uint8_t v_res_2791_; lean_object* v_r_2792_; 
v_res_2791_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2787_, v_v_2788_, v_a_2789_);
lean_dec(v_a_2789_);
v_r_2792_ = lean_box(v_res_2791_);
return v_r_2792_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; uint8_t v_closed_2797_; 
v___x_2796_ = lean_st_ref_get(v___y_2794_);
v_closed_2797_ = lean_ctor_get_uint8(v___x_2796_, sizeof(void*)*7);
lean_dec(v___x_2796_);
if (v_closed_2797_ == 0)
{
uint8_t v___x_2798_; 
v___x_2798_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2793_, v___y_2794_);
return v___x_2798_;
}
else
{
uint8_t v___x_2799_; 
lean_dec(v_v_2793_);
v___x_2799_ = 0;
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v_res_2803_; lean_object* v_r_2804_; 
v_res_2803_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2800_, v___y_2801_);
lean_dec(v___y_2801_);
v_r_2804_ = lean_box(v_res_2803_);
return v_r_2804_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2805_, lean_object* v_v_2806_){
_start:
{
lean_object* v___f_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v___f_2808_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2808_, 0, v_v_2806_);
v___x_2809_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2805_, v___f_2808_);
v___x_2810_ = lean_unbox(v___x_2809_);
lean_dec(v___x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2811_, lean_object* v_v_2812_, lean_object* v_a_2813_){
_start:
{
uint8_t v_res_2814_; lean_object* v_r_2815_; 
v_res_2814_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2811_, v_v_2812_);
v_r_2815_ = lean_box(v_res_2814_);
return v_r_2815_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2816_, lean_object* v_ch_2817_, lean_object* v_v_2818_){
_start:
{
uint8_t v___x_2820_; 
v___x_2820_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2817_, v_v_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_ch_2822_, lean_object* v_v_2823_, lean_object* v_a_2824_){
_start:
{
uint8_t v_res_2825_; lean_object* v_r_2826_; 
v_res_2825_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(v_00_u03b1_2821_, v_ch_2822_, v_v_2823_);
v_r_2826_ = lean_box(v_res_2825_);
return v_r_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object* v_v_2827_, lean_object* v___f_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; uint8_t v_closed_2832_; 
v___x_2831_ = lean_st_ref_get(v___y_2829_);
v_closed_2832_ = lean_ctor_get_uint8(v___x_2831_, sizeof(void*)*7);
lean_dec(v___x_2831_);
if (v_closed_2832_ == 0)
{
uint8_t v___x_2833_; 
v___x_2833_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2827_, v___y_2829_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_producers_2836_; lean_object* v_consumers_2837_; lean_object* v_capacity_2838_; lean_object* v_buf_2839_; lean_object* v_bufCount_2840_; lean_object* v_sendIdx_2841_; lean_object* v_recvIdx_2842_; uint8_t v_closed_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2855_; 
v___x_2834_ = lean_io_promise_new();
v___x_2835_ = lean_st_ref_take(v___y_2829_);
v_producers_2836_ = lean_ctor_get(v___x_2835_, 0);
v_consumers_2837_ = lean_ctor_get(v___x_2835_, 1);
v_capacity_2838_ = lean_ctor_get(v___x_2835_, 2);
v_buf_2839_ = lean_ctor_get(v___x_2835_, 3);
v_bufCount_2840_ = lean_ctor_get(v___x_2835_, 4);
v_sendIdx_2841_ = lean_ctor_get(v___x_2835_, 5);
v_recvIdx_2842_ = lean_ctor_get(v___x_2835_, 6);
v_closed_2843_ = lean_ctor_get_uint8(v___x_2835_, sizeof(void*)*7);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2845_ = v___x_2835_;
v_isShared_2846_ = v_isSharedCheck_2855_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_recvIdx_2842_);
lean_inc(v_sendIdx_2841_);
lean_inc(v_bufCount_2840_);
lean_inc(v_buf_2839_);
lean_inc(v_capacity_2838_);
lean_inc(v_consumers_2837_);
lean_inc(v_producers_2836_);
lean_dec(v___x_2835_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2855_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
lean_inc(v___x_2834_);
v___x_2847_ = l_Std_Queue_enqueue___redArg(v___x_2834_, v_producers_2836_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2847_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_consumers_2837_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_capacity_2838_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_buf_2839_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_bufCount_2840_);
lean_ctor_set(v_reuseFailAlloc_2854_, 5, v_sendIdx_2841_);
lean_ctor_set(v_reuseFailAlloc_2854_, 6, v_recvIdx_2842_);
lean_ctor_set_uint8(v_reuseFailAlloc_2854_, sizeof(void*)*7, v_closed_2843_);
v___x_2849_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2850_ = lean_st_ref_set(v___y_2829_, v___x_2849_);
v___x_2851_ = lean_io_promise_result_opt(v___x_2834_);
lean_dec(v___x_2834_);
v___x_2852_ = lean_unsigned_to_nat(0u);
v___x_2853_ = lean_io_bind_task(v___x_2851_, v___f_2828_, v___x_2852_, v___x_2833_);
return v___x_2853_;
}
}
}
else
{
lean_object* v___x_2856_; 
lean_dec_ref(v___f_2828_);
v___x_2856_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_2856_;
}
}
else
{
lean_object* v___x_2857_; 
lean_dec_ref(v___f_2828_);
lean_dec(v_v_2827_);
v___x_2857_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_2858_, lean_object* v___f_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2858_, v___f_2859_, v___y_2860_);
lean_dec(v___y_2860_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object* v_ch_2863_, lean_object* v_v_2864_, lean_object* v_res_2865_){
_start:
{
if (lean_obj_tag(v_res_2865_) == 0)
{
lean_dec(v_v_2864_);
lean_dec_ref(v_ch_2863_);
goto v___jp_2867_;
}
else
{
lean_object* v_val_2869_; uint8_t v___x_2870_; 
v_val_2869_ = lean_ctor_get(v_res_2865_, 0);
v___x_2870_ = lean_unbox(v_val_2869_);
if (v___x_2870_ == 0)
{
lean_dec(v_v_2864_);
lean_dec_ref(v_ch_2863_);
goto v___jp_2867_;
}
else
{
lean_object* v___x_2871_; 
v___x_2871_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2863_, v_v_2864_);
return v___x_2871_;
}
}
v___jp_2867_:
{
lean_object* v___x_2868_; 
v___x_2868_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_2872_, lean_object* v_v_2873_, lean_object* v_res_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2872_, v_v_2873_, v_res_2874_);
lean_dec(v_res_2874_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object* v_ch_2877_, lean_object* v_v_2878_){
_start:
{
lean_object* v___f_2880_; lean_object* v___f_2881_; lean_object* v___x_2882_; 
lean_inc(v_v_2878_);
lean_inc_ref(v_ch_2877_);
v___f_2880_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2880_, 0, v_ch_2877_);
lean_closure_set(v___f_2880_, 1, v_v_2878_);
v___f_2881_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2881_, 0, v_v_2878_);
lean_closure_set(v___f_2881_, 1, v___f_2880_);
v___x_2882_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2877_, v___f_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object* v_ch_2883_, lean_object* v_v_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2883_, v_v_2884_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object* v_00_u03b1_2887_, lean_object* v_ch_2888_, lean_object* v_v_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2888_, v_v_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object* v_00_u03b1_2892_, lean_object* v_ch_2893_, lean_object* v_v_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(v_00_u03b1_2892_, v_ch_2893_, v_v_2894_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_2897_, lean_object* v_as_2898_, size_t v_sz_2899_, size_t v_i_2900_, lean_object* v_b_2901_){
_start:
{
uint8_t v___x_2903_; 
v___x_2903_ = lean_usize_dec_lt(v_i_2900_, v_sz_2899_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v_b_2901_);
return v___x_2904_;
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; size_t v___x_2908_; size_t v___x_2909_; 
v_a_2905_ = lean_array_uget_borrowed(v_as_2898_, v_i_2900_);
v___x_2906_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_2905_, v___x_2897_);
v___x_2907_ = lean_box(0);
v___x_2908_ = ((size_t)1ULL);
v___x_2909_ = lean_usize_add(v_i_2900_, v___x_2908_);
v_i_2900_ = v___x_2909_;
v_b_2901_ = v___x_2907_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_2911_, lean_object* v_as_2912_, lean_object* v_sz_2913_, lean_object* v_i_2914_, lean_object* v_b_2915_, lean_object* v___y_2916_){
_start:
{
uint8_t v___x_1136__boxed_2917_; size_t v_sz_boxed_2918_; size_t v_i_boxed_2919_; lean_object* v_res_2920_; 
v___x_1136__boxed_2917_ = lean_unbox(v___x_2911_);
v_sz_boxed_2918_ = lean_unbox_usize(v_sz_2913_);
lean_dec(v_sz_2913_);
v_i_boxed_2919_ = lean_unbox_usize(v_i_2914_);
lean_dec(v_i_2914_);
v_res_2920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1136__boxed_2917_, v_as_2912_, v_sz_boxed_2918_, v_i_boxed_2919_, v_b_2915_);
lean_dec_ref(v_as_2912_);
return v_res_2920_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Std_Queue_empty(lean_box(0));
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; uint8_t v_closed_2925_; 
v___x_2924_ = lean_st_ref_get(v___y_2922_);
v_closed_2925_ = lean_ctor_get_uint8(v___x_2924_, sizeof(void*)*7);
if (v_closed_2925_ == 0)
{
lean_object* v_producers_2926_; lean_object* v_consumers_2927_; lean_object* v_capacity_2928_; lean_object* v_buf_2929_; lean_object* v_bufCount_2930_; lean_object* v_sendIdx_2931_; lean_object* v_recvIdx_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2955_; 
v_producers_2926_ = lean_ctor_get(v___x_2924_, 0);
v_consumers_2927_ = lean_ctor_get(v___x_2924_, 1);
v_capacity_2928_ = lean_ctor_get(v___x_2924_, 2);
v_buf_2929_ = lean_ctor_get(v___x_2924_, 3);
v_bufCount_2930_ = lean_ctor_get(v___x_2924_, 4);
v_sendIdx_2931_ = lean_ctor_get(v___x_2924_, 5);
v_recvIdx_2932_ = lean_ctor_get(v___x_2924_, 6);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2934_ = v___x_2924_;
v_isShared_2935_ = v_isSharedCheck_2955_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_recvIdx_2932_);
lean_inc(v_sendIdx_2931_);
lean_inc(v_bufCount_2930_);
lean_inc(v_buf_2929_);
lean_inc(v_capacity_2928_);
lean_inc(v_consumers_2927_);
lean_inc(v_producers_2926_);
lean_dec(v___x_2924_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2955_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; size_t v_sz_2938_; size_t v___x_2939_; lean_object* v___x_2940_; 
v___x_2936_ = l_Std_Queue_toArray___redArg(v_consumers_2927_);
v___x_2937_ = lean_box(0);
v_sz_2938_ = lean_array_size(v___x_2936_);
v___x_2939_ = ((size_t)0ULL);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_2925_, v___x_2936_, v_sz_2938_, v___x_2939_, v___x_2937_);
lean_dec_ref(v___x_2936_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2953_; 
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; 
v_unused_2954_ = lean_ctor_get(v___x_2940_, 0);
lean_dec(v_unused_2954_);
v___x_2942_ = v___x_2940_;
v_isShared_2943_ = v_isSharedCheck_2953_;
goto v_resetjp_2941_;
}
else
{
lean_dec(v___x_2940_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2953_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; uint8_t v___x_2945_; lean_object* v___x_2947_; 
v___x_2944_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0);
v___x_2945_ = 1;
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 1, v___x_2944_);
v___x_2947_ = v___x_2934_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_producers_2926_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v_capacity_2928_);
lean_ctor_set(v_reuseFailAlloc_2952_, 3, v_buf_2929_);
lean_ctor_set(v_reuseFailAlloc_2952_, 4, v_bufCount_2930_);
lean_ctor_set(v_reuseFailAlloc_2952_, 5, v_sendIdx_2931_);
lean_ctor_set(v_reuseFailAlloc_2952_, 6, v_recvIdx_2932_);
v___x_2947_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
lean_ctor_set_uint8(v___x_2947_, sizeof(void*)*7, v___x_2945_);
v___x_2948_ = lean_st_ref_set(v___y_2922_, v___x_2947_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2937_);
v___x_2950_ = v___x_2942_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2937_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_del_object(v___x_2934_);
lean_dec(v_recvIdx_2932_);
lean_dec(v_sendIdx_2931_);
lean_dec(v_bufCount_2930_);
lean_dec_ref(v_buf_2929_);
lean_dec(v_capacity_2928_);
lean_dec_ref(v_producers_2926_);
return v___x_2940_;
}
}
}
else
{
uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_dec(v___x_2924_);
v___x_2956_ = 1;
v___x_2957_ = lean_box(v___x_2956_);
v___x_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
return v___x_2958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_2959_);
lean_dec(v___y_2959_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_2963_){
_start:
{
lean_object* v___f_2965_; lean_object* v___x_2966_; 
v___f_2965_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_2966_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_2963_, v___f_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2967_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_2970_, lean_object* v_ch_2971_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_2974_, lean_object* v_ch_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_2974_, v_ch_2975_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_2978_, uint8_t v___x_2979_, lean_object* v_as_2980_, size_t v_sz_2981_, size_t v_i_2982_, lean_object* v_b_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_2979_, v_as_2980_, v_sz_2981_, v_i_2982_, v_b_2983_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_2987_, lean_object* v___x_2988_, lean_object* v_as_2989_, lean_object* v_sz_2990_, lean_object* v_i_2991_, lean_object* v_b_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
uint8_t v___x_1234__boxed_2995_; size_t v_sz_boxed_2996_; size_t v_i_boxed_2997_; lean_object* v_res_2998_; 
v___x_1234__boxed_2995_ = lean_unbox(v___x_2988_);
v_sz_boxed_2996_ = lean_unbox_usize(v_sz_2990_);
lean_dec(v_sz_2990_);
v_i_boxed_2997_ = lean_unbox_usize(v_i_2991_);
lean_dec(v_i_2991_);
v_res_2998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_2987_, v___x_1234__boxed_2995_, v_as_2989_, v_sz_boxed_2996_, v_i_boxed_2997_, v_b_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v_as_2989_);
return v_res_2998_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; uint8_t v_closed_3002_; 
v___x_3001_ = lean_st_ref_get(v___y_2999_);
v_closed_3002_ = lean_ctor_get_uint8(v___x_3001_, sizeof(void*)*7);
lean_dec(v___x_3001_);
return v_closed_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
uint8_t v_res_3005_; lean_object* v_r_3006_; 
v_res_3005_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_3003_);
lean_dec(v___y_3003_);
v_r_3006_ = lean_box(v_res_3005_);
return v_r_3006_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_3008_){
_start:
{
lean_object* v___f_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___f_3010_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_3011_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3008_, v___f_3010_);
v___x_3012_ = lean_unbox(v___x_3011_);
lean_dec(v___x_3011_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_3013_, lean_object* v_a_3014_){
_start:
{
uint8_t v_res_3015_; lean_object* v_r_3016_; 
v_res_3015_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3013_);
v_r_3016_ = lean_box(v_res_3015_);
return v_r_3016_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_3017_, lean_object* v_ch_3018_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_3021_, lean_object* v_ch_3022_, lean_object* v_a_3023_){
_start:
{
uint8_t v_res_3024_; lean_object* v_r_3025_; 
v_res_3024_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_3021_, v_ch_3022_);
v_r_3025_ = lean_box(v_res_3024_);
return v_r_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_toPure_3029_; lean_object* v___x_3030_; 
v_toPure_3029_ = lean_ctor_get(v_toApplicative_3026_, 1);
lean_inc(v_toPure_3029_);
lean_dec_ref(v_toApplicative_3026_);
v___x_3030_ = lean_apply_2(v_toPure_3029_, lean_box(0), v_a_3027_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_3031_, lean_object* v_toBind_3032_, lean_object* v___f_3033_, lean_object* v_____r_3034_, lean_object* v_st_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_inc(v___y_3036_);
v___x_3037_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_3037_, 0, lean_box(0));
lean_closure_set(v___x_3037_, 1, lean_box(0));
lean_closure_set(v___x_3037_, 2, v___y_3036_);
lean_closure_set(v___x_3037_, 3, v_st_3035_);
v___x_3038_ = lean_apply_2(v_inst_3031_, lean_box(0), v___x_3037_);
v___x_3039_ = lean_apply_4(v_toBind_3032_, lean_box(0), lean_box(0), v___x_3038_, v___f_3033_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_3040_, lean_object* v_toBind_3041_, lean_object* v___f_3042_, lean_object* v_____r_3043_, lean_object* v_st_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v_res_3046_; 
v_res_3046_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3040_, v_toBind_3041_, v___f_3042_, v_____r_3043_, v_st_3044_, v___y_3045_);
lean_dec(v___y_3045_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_3047_, lean_object* v_consumers_3048_, lean_object* v_capacity_3049_, lean_object* v_buf_3050_, lean_object* v___x_3051_, lean_object* v_sendIdx_3052_, lean_object* v___y_3053_, uint8_t v_closed_3054_, lean_object* v___f_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3058_, 0, v_snd_3047_);
lean_ctor_set(v___x_3058_, 1, v_consumers_3048_);
lean_ctor_set(v___x_3058_, 2, v_capacity_3049_);
lean_ctor_set(v___x_3058_, 3, v_buf_3050_);
lean_ctor_set(v___x_3058_, 4, v___x_3051_);
lean_ctor_set(v___x_3058_, 5, v_sendIdx_3052_);
lean_ctor_set(v___x_3058_, 6, v___y_3053_);
lean_ctor_set_uint8(v___x_3058_, sizeof(void*)*7, v_closed_3054_);
v___x_3059_ = lean_box(0);
lean_inc(v_a_3056_);
v___x_3060_ = lean_apply_3(v___f_3055_, v___x_3059_, v___x_3058_, v_a_3056_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3061_, lean_object* v_consumers_3062_, lean_object* v_capacity_3063_, lean_object* v_buf_3064_, lean_object* v___x_3065_, lean_object* v_sendIdx_3066_, lean_object* v___y_3067_, lean_object* v_closed_3068_, lean_object* v___f_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
uint8_t v_closed_boxed_3072_; lean_object* v_res_3073_; 
v_closed_boxed_3072_ = lean_unbox(v_closed_3068_);
v_res_3073_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3061_, v_consumers_3062_, v_capacity_3063_, v_buf_3064_, v___x_3065_, v_sendIdx_3066_, v___y_3067_, v_closed_boxed_3072_, v___f_3069_, v_a_3070_, v_a_3071_);
lean_dec(v_a_3070_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3074_, lean_object* v_inst_3075_, lean_object* v_toBind_3076_, lean_object* v_bufCount_3077_, lean_object* v_producers_3078_, lean_object* v_consumers_3079_, lean_object* v_capacity_3080_, lean_object* v_buf_3081_, lean_object* v_sendIdx_3082_, uint8_t v_closed_3083_, lean_object* v_a_3084_, uint8_t v___x_3085_, lean_object* v_inst_3086_, lean_object* v_recvIdx_3087_, lean_object* v___x_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v___f_3090_; lean_object* v___f_3091_; lean_object* v___y_3093_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___f_3090_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3090_, 0, v_toApplicative_3074_);
lean_closure_set(v___f_3090_, 1, v_a_3089_);
lean_inc_ref(v___f_3090_);
lean_inc(v_toBind_3076_);
lean_inc(v_inst_3075_);
v___f_3091_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3091_, 0, v_inst_3075_);
lean_closure_set(v___f_3091_, 1, v_toBind_3076_);
lean_closure_set(v___f_3091_, 2, v___f_3090_);
v___x_3109_ = lean_unsigned_to_nat(1u);
v___x_3110_ = lean_nat_add(v_recvIdx_3087_, v___x_3109_);
v___x_3111_ = lean_nat_dec_eq(v___x_3110_, v_capacity_3080_);
if (v___x_3111_ == 0)
{
lean_dec(v___x_3088_);
v___y_3093_ = v___x_3110_;
goto v___jp_3092_;
}
else
{
lean_dec(v___x_3110_);
v___y_3093_ = v___x_3088_;
goto v___jp_3092_;
}
v___jp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3094_ = lean_unsigned_to_nat(1u);
v___x_3095_ = lean_nat_sub(v_bufCount_3077_, v___x_3094_);
lean_inc(v___y_3093_);
lean_inc(v_sendIdx_3082_);
lean_inc(v___x_3095_);
lean_inc_ref(v_buf_3081_);
lean_inc(v_capacity_3080_);
lean_inc_ref(v_consumers_3079_);
lean_inc_ref(v_producers_3078_);
v___x_3096_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3096_, 0, v_producers_3078_);
lean_ctor_set(v___x_3096_, 1, v_consumers_3079_);
lean_ctor_set(v___x_3096_, 2, v_capacity_3080_);
lean_ctor_set(v___x_3096_, 3, v_buf_3081_);
lean_ctor_set(v___x_3096_, 4, v___x_3095_);
lean_ctor_set(v___x_3096_, 5, v_sendIdx_3082_);
lean_ctor_set(v___x_3096_, 6, v___y_3093_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*7, v_closed_3083_);
v___x_3097_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3078_);
if (lean_obj_tag(v___x_3097_) == 1)
{
lean_object* v_val_3098_; lean_object* v_fst_3099_; lean_object* v_snd_3100_; lean_object* v___x_3101_; lean_object* v___f_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_dec_ref(v___x_3096_);
lean_dec_ref(v___f_3090_);
lean_dec(v_inst_3075_);
v_val_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_val_3098_);
lean_dec_ref(v___x_3097_);
v_fst_3099_ = lean_ctor_get(v_val_3098_, 0);
lean_inc(v_fst_3099_);
v_snd_3100_ = lean_ctor_get(v_val_3098_, 1);
lean_inc(v_snd_3100_);
lean_dec(v_val_3098_);
v___x_3101_ = lean_box(v_closed_3083_);
lean_inc(v_a_3084_);
v___f_3102_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3102_, 0, v_snd_3100_);
lean_closure_set(v___f_3102_, 1, v_consumers_3079_);
lean_closure_set(v___f_3102_, 2, v_capacity_3080_);
lean_closure_set(v___f_3102_, 3, v_buf_3081_);
lean_closure_set(v___f_3102_, 4, v___x_3095_);
lean_closure_set(v___f_3102_, 5, v_sendIdx_3082_);
lean_closure_set(v___f_3102_, 6, v___y_3093_);
lean_closure_set(v___f_3102_, 7, v___x_3101_);
lean_closure_set(v___f_3102_, 8, v___f_3091_);
lean_closure_set(v___f_3102_, 9, v_a_3084_);
v___x_3103_ = lean_box(v___x_3085_);
v___x_3104_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3104_, 0, lean_box(0));
lean_closure_set(v___x_3104_, 1, v___x_3103_);
lean_closure_set(v___x_3104_, 2, v_fst_3099_);
v___x_3105_ = lean_apply_2(v_inst_3086_, lean_box(0), v___x_3104_);
v___x_3106_ = lean_apply_4(v_toBind_3076_, lean_box(0), lean_box(0), v___x_3105_, v___f_3102_);
return v___x_3106_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_dec(v___x_3097_);
lean_dec(v___x_3095_);
lean_dec(v___y_3093_);
lean_dec_ref(v___f_3091_);
lean_dec(v_inst_3086_);
lean_dec(v_sendIdx_3082_);
lean_dec_ref(v_buf_3081_);
lean_dec(v_capacity_3080_);
lean_dec_ref(v_consumers_3079_);
v___x_3107_ = lean_box(0);
v___x_3108_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3075_, v_toBind_3076_, v___f_3090_, v___x_3107_, v___x_3096_, v_a_3084_);
return v___x_3108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3112_, lean_object* v_inst_3113_, lean_object* v_toBind_3114_, lean_object* v_bufCount_3115_, lean_object* v_producers_3116_, lean_object* v_consumers_3117_, lean_object* v_capacity_3118_, lean_object* v_buf_3119_, lean_object* v_sendIdx_3120_, lean_object* v_closed_3121_, lean_object* v_a_3122_, lean_object* v___x_3123_, lean_object* v_inst_3124_, lean_object* v_recvIdx_3125_, lean_object* v___x_3126_, lean_object* v_a_3127_){
_start:
{
uint8_t v_closed_boxed_3128_; uint8_t v___x_679__boxed_3129_; lean_object* v_res_3130_; 
v_closed_boxed_3128_ = lean_unbox(v_closed_3121_);
v___x_679__boxed_3129_ = lean_unbox(v___x_3123_);
v_res_3130_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3112_, v_inst_3113_, v_toBind_3114_, v_bufCount_3115_, v_producers_3116_, v_consumers_3117_, v_capacity_3118_, v_buf_3119_, v_sendIdx_3120_, v_closed_boxed_3128_, v_a_3122_, v___x_679__boxed_3129_, v_inst_3124_, v_recvIdx_3125_, v___x_3126_, v_a_3127_);
lean_dec(v_recvIdx_3125_);
lean_dec(v_a_3122_);
lean_dec(v_bufCount_3115_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3131_, lean_object* v_inst_3132_, lean_object* v_toBind_3133_, lean_object* v_a_3134_, lean_object* v_inst_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_producers_3137_; lean_object* v_consumers_3138_; lean_object* v_capacity_3139_; lean_object* v_buf_3140_; lean_object* v_bufCount_3141_; lean_object* v_sendIdx_3142_; lean_object* v_recvIdx_3143_; uint8_t v_closed_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v_producers_3137_ = lean_ctor_get(v_a_3136_, 0);
lean_inc_ref(v_producers_3137_);
v_consumers_3138_ = lean_ctor_get(v_a_3136_, 1);
lean_inc_ref(v_consumers_3138_);
v_capacity_3139_ = lean_ctor_get(v_a_3136_, 2);
lean_inc(v_capacity_3139_);
v_buf_3140_ = lean_ctor_get(v_a_3136_, 3);
lean_inc_ref(v_buf_3140_);
v_bufCount_3141_ = lean_ctor_get(v_a_3136_, 4);
lean_inc(v_bufCount_3141_);
v_sendIdx_3142_ = lean_ctor_get(v_a_3136_, 5);
lean_inc(v_sendIdx_3142_);
v_recvIdx_3143_ = lean_ctor_get(v_a_3136_, 6);
lean_inc(v_recvIdx_3143_);
v_closed_3144_ = lean_ctor_get_uint8(v_a_3136_, sizeof(void*)*7);
lean_dec_ref(v_a_3136_);
v___x_3145_ = lean_unsigned_to_nat(0u);
v___x_3146_ = lean_nat_dec_eq(v_bufCount_3141_, v___x_3145_);
if (v___x_3146_ == 0)
{
uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___f_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3147_ = 1;
v___x_3148_ = lean_box(v_closed_3144_);
v___x_3149_ = lean_box(v___x_3147_);
lean_inc(v_recvIdx_3143_);
lean_inc(v_a_3134_);
lean_inc_ref(v_buf_3140_);
lean_inc(v_toBind_3133_);
lean_inc(v_inst_3132_);
v___f_3150_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3150_, 0, v_toApplicative_3131_);
lean_closure_set(v___f_3150_, 1, v_inst_3132_);
lean_closure_set(v___f_3150_, 2, v_toBind_3133_);
lean_closure_set(v___f_3150_, 3, v_bufCount_3141_);
lean_closure_set(v___f_3150_, 4, v_producers_3137_);
lean_closure_set(v___f_3150_, 5, v_consumers_3138_);
lean_closure_set(v___f_3150_, 6, v_capacity_3139_);
lean_closure_set(v___f_3150_, 7, v_buf_3140_);
lean_closure_set(v___f_3150_, 8, v_sendIdx_3142_);
lean_closure_set(v___f_3150_, 9, v___x_3148_);
lean_closure_set(v___f_3150_, 10, v_a_3134_);
lean_closure_set(v___f_3150_, 11, v___x_3149_);
lean_closure_set(v___f_3150_, 12, v_inst_3135_);
lean_closure_set(v___f_3150_, 13, v_recvIdx_3143_);
lean_closure_set(v___f_3150_, 14, v___x_3145_);
v___x_3151_ = lean_array_fget(v_buf_3140_, v_recvIdx_3143_);
lean_dec(v_recvIdx_3143_);
lean_dec_ref(v_buf_3140_);
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3153_, 0, lean_box(0));
lean_closure_set(v___x_3153_, 1, lean_box(0));
lean_closure_set(v___x_3153_, 2, v___x_3151_);
lean_closure_set(v___x_3153_, 3, v___x_3152_);
v___x_3154_ = lean_apply_2(v_inst_3132_, lean_box(0), v___x_3153_);
v___x_3155_ = lean_apply_4(v_toBind_3133_, lean_box(0), lean_box(0), v___x_3154_, v___f_3150_);
return v___x_3155_;
}
else
{
lean_object* v_toPure_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_dec(v_recvIdx_3143_);
lean_dec(v_sendIdx_3142_);
lean_dec(v_bufCount_3141_);
lean_dec_ref(v_buf_3140_);
lean_dec(v_capacity_3139_);
lean_dec_ref(v_consumers_3138_);
lean_dec_ref(v_producers_3137_);
lean_dec(v_inst_3135_);
lean_dec(v_toBind_3133_);
lean_dec(v_inst_3132_);
v_toPure_3156_ = lean_ctor_get(v_toApplicative_3131_, 1);
lean_inc(v_toPure_3156_);
lean_dec_ref(v_toApplicative_3131_);
v___x_3157_ = lean_box(0);
v___x_3158_ = lean_apply_2(v_toPure_3156_, lean_box(0), v___x_3157_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3159_, lean_object* v_inst_3160_, lean_object* v_toBind_3161_, lean_object* v_a_3162_, lean_object* v_inst_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3159_, v_inst_3160_, v_toBind_3161_, v_a_3162_, v_inst_3163_, v_a_3164_);
lean_dec(v_a_3162_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v_toApplicative_3170_; lean_object* v_toBind_3171_; lean_object* v___f_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v_toApplicative_3170_ = lean_ctor_get(v_inst_3166_, 0);
lean_inc_ref(v_toApplicative_3170_);
v_toBind_3171_ = lean_ctor_get(v_inst_3166_, 1);
lean_inc_n(v_toBind_3171_, 2);
lean_dec_ref(v_inst_3166_);
lean_inc_n(v_a_3169_, 2);
lean_inc(v_inst_3167_);
v___f_3172_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3172_, 0, v_toApplicative_3170_);
lean_closure_set(v___f_3172_, 1, v_inst_3167_);
lean_closure_set(v___f_3172_, 2, v_toBind_3171_);
lean_closure_set(v___f_3172_, 3, v_a_3169_);
lean_closure_set(v___f_3172_, 4, v_inst_3168_);
v___x_3173_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3173_, 0, lean_box(0));
lean_closure_set(v___x_3173_, 1, lean_box(0));
lean_closure_set(v___x_3173_, 2, v_a_3169_);
v___x_3174_ = lean_apply_2(v_inst_3167_, lean_box(0), v___x_3173_);
v___x_3175_ = lean_apply_4(v_toBind_3171_, lean_box(0), lean_box(0), v___x_3174_, v___f_3172_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3176_, v_inst_3177_, v_inst_3178_, v_a_3179_);
lean_dec(v_a_3179_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3181_, lean_object* v_00_u03b1_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3183_, v_inst_3184_, v_inst_3185_, v_a_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3188_, lean_object* v_00_u03b1_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3188_, v_00_u03b1_3189_, v_inst_3190_, v_inst_3191_, v_inst_3192_, v_a_3193_);
lean_dec(v_a_3193_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3195_){
_start:
{
lean_object* v___x_3197_; lean_object* v_producers_3198_; lean_object* v_consumers_3199_; lean_object* v_capacity_3200_; lean_object* v_buf_3201_; lean_object* v_bufCount_3202_; lean_object* v_sendIdx_3203_; lean_object* v_recvIdx_3204_; uint8_t v_closed_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3237_; 
v___x_3197_ = lean_st_ref_get(v_a_3195_);
v_producers_3198_ = lean_ctor_get(v___x_3197_, 0);
v_consumers_3199_ = lean_ctor_get(v___x_3197_, 1);
v_capacity_3200_ = lean_ctor_get(v___x_3197_, 2);
v_buf_3201_ = lean_ctor_get(v___x_3197_, 3);
v_bufCount_3202_ = lean_ctor_get(v___x_3197_, 4);
v_sendIdx_3203_ = lean_ctor_get(v___x_3197_, 5);
v_recvIdx_3204_ = lean_ctor_get(v___x_3197_, 6);
v_closed_3205_ = lean_ctor_get_uint8(v___x_3197_, sizeof(void*)*7);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3207_ = v___x_3197_;
v_isShared_3208_ = v_isSharedCheck_3237_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_recvIdx_3204_);
lean_inc(v_sendIdx_3203_);
lean_inc(v_bufCount_3202_);
lean_inc(v_buf_3201_);
lean_inc(v_capacity_3200_);
lean_inc(v_consumers_3199_);
lean_inc(v_producers_3198_);
lean_dec(v___x_3197_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3237_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; uint8_t v___x_3210_; 
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_nat_dec_eq(v_bufCount_3202_, v___x_3209_);
if (v___x_3210_ == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v_st_3215_; lean_object* v___y_3216_; uint8_t v___x_3218_; lean_object* v___y_3220_; lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3211_ = lean_array_fget_borrowed(v_buf_3201_, v_recvIdx_3204_);
v___x_3212_ = lean_box(0);
v___x_3213_ = lean_st_ref_swap(v___x_3211_, v___x_3212_);
v___x_3218_ = 1;
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3234_ = lean_nat_add(v_recvIdx_3204_, v___x_3233_);
lean_dec(v_recvIdx_3204_);
v___x_3235_ = lean_nat_dec_eq(v___x_3234_, v_capacity_3200_);
if (v___x_3235_ == 0)
{
v___y_3220_ = v___x_3234_;
goto v___jp_3219_;
}
else
{
lean_dec(v___x_3234_);
v___y_3220_ = v___x_3209_;
goto v___jp_3219_;
}
v___jp_3214_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_st_ref_set(v___y_3216_, v_st_3215_);
return v___x_3213_;
}
v___jp_3219_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3221_ = lean_unsigned_to_nat(1u);
v___x_3222_ = lean_nat_sub(v_bufCount_3202_, v___x_3221_);
lean_dec(v_bufCount_3202_);
lean_inc(v___y_3220_);
lean_inc(v_sendIdx_3203_);
lean_inc(v___x_3222_);
lean_inc_ref(v_buf_3201_);
lean_inc(v_capacity_3200_);
lean_inc_ref(v_consumers_3199_);
lean_inc_ref(v_producers_3198_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 6, v___y_3220_);
lean_ctor_set(v___x_3207_, 4, v___x_3222_);
v___x_3224_ = v___x_3207_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_producers_3198_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_consumers_3199_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_capacity_3200_);
lean_ctor_set(v_reuseFailAlloc_3232_, 3, v_buf_3201_);
lean_ctor_set(v_reuseFailAlloc_3232_, 4, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3232_, 5, v_sendIdx_3203_);
lean_ctor_set(v_reuseFailAlloc_3232_, 6, v___y_3220_);
lean_ctor_set_uint8(v_reuseFailAlloc_3232_, sizeof(void*)*7, v_closed_3205_);
v___x_3224_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3198_);
if (lean_obj_tag(v___x_3225_) == 1)
{
lean_object* v_val_3226_; lean_object* v_fst_3227_; lean_object* v_snd_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec_ref(v___x_3224_);
v_val_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_val_3226_);
lean_dec_ref(v___x_3225_);
v_fst_3227_ = lean_ctor_get(v_val_3226_, 0);
lean_inc(v_fst_3227_);
v_snd_3228_ = lean_ctor_get(v_val_3226_, 1);
lean_inc(v_snd_3228_);
lean_dec(v_val_3226_);
v___x_3229_ = lean_box(v___x_3218_);
v___x_3230_ = lean_io_promise_resolve(v___x_3229_, v_fst_3227_);
lean_dec(v_fst_3227_);
v___x_3231_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3231_, 0, v_snd_3228_);
lean_ctor_set(v___x_3231_, 1, v_consumers_3199_);
lean_ctor_set(v___x_3231_, 2, v_capacity_3200_);
lean_ctor_set(v___x_3231_, 3, v_buf_3201_);
lean_ctor_set(v___x_3231_, 4, v___x_3222_);
lean_ctor_set(v___x_3231_, 5, v_sendIdx_3203_);
lean_ctor_set(v___x_3231_, 6, v___y_3220_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*7, v_closed_3205_);
v_st_3215_ = v___x_3231_;
v___y_3216_ = v_a_3195_;
goto v___jp_3214_;
}
else
{
lean_dec(v___x_3225_);
lean_dec(v___x_3222_);
lean_dec(v___y_3220_);
lean_dec(v_sendIdx_3203_);
lean_dec_ref(v_buf_3201_);
lean_dec(v_capacity_3200_);
lean_dec_ref(v_consumers_3199_);
v_st_3215_ = v___x_3224_;
v___y_3216_ = v_a_3195_;
goto v___jp_3214_;
}
}
}
}
else
{
lean_object* v___x_3236_; 
lean_del_object(v___x_3207_);
lean_dec(v_recvIdx_3204_);
lean_dec(v_sendIdx_3203_);
lean_dec(v_bufCount_3202_);
lean_dec_ref(v_buf_3201_);
lean_dec(v_capacity_3200_);
lean_dec_ref(v_consumers_3199_);
lean_dec_ref(v_producers_3198_);
v___x_3236_ = lean_box(0);
return v___x_3236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3238_);
lean_dec(v_a_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v___x_3244_; 
v___x_3244_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3242_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3245_, lean_object* v_a_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3245_, v_a_3246_);
lean_dec(v_a_3246_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3250_){
_start:
{
lean_object* v___f_3252_; lean_object* v___x_3253_; 
v___f_3252_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3253_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3250_, v___f_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3257_, lean_object* v_ch_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3261_, lean_object* v_ch_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3261_, v_ch_3262_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; 
v___x_3268_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3266_);
if (lean_obj_tag(v___x_3268_) == 1)
{
lean_object* v___x_3269_; 
lean_dec_ref(v___f_3265_);
v___x_3269_ = lean_task_pure(v___x_3268_);
return v___x_3269_;
}
else
{
lean_object* v___x_3270_; uint8_t v_closed_3271_; 
lean_dec(v___x_3268_);
v___x_3270_ = lean_st_ref_get(v___y_3266_);
v_closed_3271_ = lean_ctor_get_uint8(v___x_3270_, sizeof(void*)*7);
lean_dec(v___x_3270_);
if (v_closed_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v_producers_3274_; lean_object* v_consumers_3275_; lean_object* v_capacity_3276_; lean_object* v_buf_3277_; lean_object* v_bufCount_3278_; lean_object* v_sendIdx_3279_; lean_object* v_recvIdx_3280_; uint8_t v_closed_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3295_; 
v___x_3272_ = lean_io_promise_new();
v___x_3273_ = lean_st_ref_take(v___y_3266_);
v_producers_3274_ = lean_ctor_get(v___x_3273_, 0);
v_consumers_3275_ = lean_ctor_get(v___x_3273_, 1);
v_capacity_3276_ = lean_ctor_get(v___x_3273_, 2);
v_buf_3277_ = lean_ctor_get(v___x_3273_, 3);
v_bufCount_3278_ = lean_ctor_get(v___x_3273_, 4);
v_sendIdx_3279_ = lean_ctor_get(v___x_3273_, 5);
v_recvIdx_3280_ = lean_ctor_get(v___x_3273_, 6);
v_closed_3281_ = lean_ctor_get_uint8(v___x_3273_, sizeof(void*)*7);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3283_ = v___x_3273_;
v_isShared_3284_ = v_isSharedCheck_3295_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_recvIdx_3280_);
lean_inc(v_sendIdx_3279_);
lean_inc(v_bufCount_3278_);
lean_inc(v_buf_3277_);
lean_inc(v_capacity_3276_);
lean_inc(v_consumers_3275_);
lean_inc(v_producers_3274_);
lean_dec(v___x_3273_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3295_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3285_ = lean_box(0);
lean_inc(v___x_3272_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3272_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_Std_Queue_enqueue___redArg(v___x_3286_, v_consumers_3275_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v___x_3287_);
v___x_3289_ = v___x_3283_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_producers_3274_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v___x_3287_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_capacity_3276_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v_buf_3277_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v_bufCount_3278_);
lean_ctor_set(v_reuseFailAlloc_3294_, 5, v_sendIdx_3279_);
lean_ctor_set(v_reuseFailAlloc_3294_, 6, v_recvIdx_3280_);
lean_ctor_set_uint8(v_reuseFailAlloc_3294_, sizeof(void*)*7, v_closed_3281_);
v___x_3289_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3290_ = lean_st_ref_set(v___y_3266_, v___x_3289_);
v___x_3291_ = lean_io_promise_result_opt(v___x_3272_);
lean_dec(v___x_3272_);
v___x_3292_ = lean_unsigned_to_nat(0u);
v___x_3293_ = lean_io_bind_task(v___x_3291_, v___f_3265_, v___x_3292_, v_closed_3271_);
return v___x_3293_;
}
}
}
else
{
lean_object* v___x_3296_; 
lean_dec_ref(v___f_3265_);
v___x_3296_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3297_, v___y_3298_);
lean_dec(v___y_3298_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3301_, lean_object* v_res_3302_){
_start:
{
if (lean_obj_tag(v_res_3302_) == 0)
{
lean_dec_ref(v_ch_3301_);
goto v___jp_3304_;
}
else
{
lean_object* v_val_3306_; uint8_t v___x_3307_; 
v_val_3306_ = lean_ctor_get(v_res_3302_, 0);
v___x_3307_ = lean_unbox(v_val_3306_);
if (v___x_3307_ == 0)
{
lean_dec_ref(v_ch_3301_);
goto v___jp_3304_;
}
else
{
lean_object* v___x_3308_; 
v___x_3308_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3301_);
return v___x_3308_;
}
}
v___jp_3304_:
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3309_, lean_object* v_res_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3309_, v_res_3310_);
lean_dec(v_res_3310_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3313_){
_start:
{
lean_object* v___f_3315_; lean_object* v___f_3316_; lean_object* v___x_3317_; 
lean_inc_ref(v_ch_3313_);
v___f_3315_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3315_, 0, v_ch_3313_);
v___f_3316_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3316_, 0, v___f_3315_);
v___x_3317_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3313_, v___f_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3318_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3321_, lean_object* v_ch_3322_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3325_, lean_object* v_ch_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3325_, v_ch_3326_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3329_, lean_object* v_a_3330_){
_start:
{
uint8_t v___y_3332_; lean_object* v_bufCount_3336_; uint8_t v_closed_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v_bufCount_3336_ = lean_ctor_get(v_a_3330_, 4);
v_closed_3337_ = lean_ctor_get_uint8(v_a_3330_, sizeof(void*)*7);
v___x_3338_ = lean_unsigned_to_nat(0u);
v___x_3339_ = lean_nat_dec_eq(v_bufCount_3336_, v___x_3338_);
if (v___x_3339_ == 0)
{
uint8_t v___x_3340_; 
v___x_3340_ = 1;
v___y_3332_ = v___x_3340_;
goto v___jp_3331_;
}
else
{
v___y_3332_ = v_closed_3337_;
goto v___jp_3331_;
}
v___jp_3331_:
{
lean_object* v_toPure_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_toPure_3333_ = lean_ctor_get(v_toApplicative_3329_, 1);
lean_inc(v_toPure_3333_);
lean_dec_ref(v_toApplicative_3329_);
v___x_3334_ = lean_box(v___y_3332_);
v___x_3335_ = lean_apply_2(v_toPure_3333_, lean_box(0), v___x_3334_);
return v___x_3335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3341_, v_a_3342_);
lean_dec_ref(v_a_3342_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v_toApplicative_3347_; lean_object* v_toBind_3348_; lean_object* v___f_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_toApplicative_3347_ = lean_ctor_get(v_inst_3344_, 0);
lean_inc_ref(v_toApplicative_3347_);
v_toBind_3348_ = lean_ctor_get(v_inst_3344_, 1);
lean_inc(v_toBind_3348_);
lean_dec_ref(v_inst_3344_);
v___f_3349_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3349_, 0, v_toApplicative_3347_);
lean_inc(v_a_3346_);
v___x_3350_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3350_, 0, lean_box(0));
lean_closure_set(v___x_3350_, 1, lean_box(0));
lean_closure_set(v___x_3350_, 2, v_a_3346_);
v___x_3351_ = lean_apply_2(v_inst_3345_, lean_box(0), v___x_3350_);
v___x_3352_ = lean_apply_4(v_toBind_3348_, lean_box(0), lean_box(0), v___x_3351_, v___f_3349_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3353_, lean_object* v_inst_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3353_, v_inst_3354_, v_a_3355_);
lean_dec(v_a_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3357_, lean_object* v_00_u03b1_3358_, lean_object* v_inst_3359_, lean_object* v_inst_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_toApplicative_3362_; lean_object* v_toBind_3363_; lean_object* v___f_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_toApplicative_3362_ = lean_ctor_get(v_inst_3359_, 0);
lean_inc_ref(v_toApplicative_3362_);
v_toBind_3363_ = lean_ctor_get(v_inst_3359_, 1);
lean_inc(v_toBind_3363_);
lean_dec_ref(v_inst_3359_);
v___f_3364_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3364_, 0, v_toApplicative_3362_);
lean_inc(v_a_3361_);
v___x_3365_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3365_, 0, lean_box(0));
lean_closure_set(v___x_3365_, 1, lean_box(0));
lean_closure_set(v___x_3365_, 2, v_a_3361_);
v___x_3366_ = lean_apply_2(v_inst_3360_, lean_box(0), v___x_3365_);
v___x_3367_ = lean_apply_4(v_toBind_3363_, lean_box(0), lean_box(0), v___x_3366_, v___f_3364_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3368_, lean_object* v_00_u03b1_3369_, lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3368_, v_00_u03b1_3369_, v_inst_3370_, v_inst_3371_, v_a_3372_);
lean_dec(v_a_3372_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; lean_object* v_producers_3377_; lean_object* v_consumers_3378_; lean_object* v_capacity_3379_; lean_object* v_buf_3380_; lean_object* v_bufCount_3381_; lean_object* v_sendIdx_3382_; lean_object* v_recvIdx_3383_; uint8_t v_closed_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3418_; 
v___x_3376_ = lean_st_ref_get(v_a_3374_);
v_producers_3377_ = lean_ctor_get(v___x_3376_, 0);
v_consumers_3378_ = lean_ctor_get(v___x_3376_, 1);
v_capacity_3379_ = lean_ctor_get(v___x_3376_, 2);
v_buf_3380_ = lean_ctor_get(v___x_3376_, 3);
v_bufCount_3381_ = lean_ctor_get(v___x_3376_, 4);
v_sendIdx_3382_ = lean_ctor_get(v___x_3376_, 5);
v_recvIdx_3383_ = lean_ctor_get(v___x_3376_, 6);
v_closed_3384_ = lean_ctor_get_uint8(v___x_3376_, sizeof(void*)*7);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3386_ = v___x_3376_;
v_isShared_3387_ = v_isSharedCheck_3418_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_recvIdx_3383_);
lean_inc(v_sendIdx_3382_);
lean_inc(v_bufCount_3381_);
lean_inc(v_buf_3380_);
lean_inc(v_capacity_3379_);
lean_inc(v_consumers_3378_);
lean_inc(v_producers_3377_);
lean_dec(v___x_3376_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3418_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3388_ = lean_unsigned_to_nat(0u);
v___x_3389_ = lean_nat_dec_eq(v_bufCount_3381_, v___x_3388_);
if (v___x_3389_ == 0)
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v_st_3394_; lean_object* v___y_3395_; uint8_t v___x_3398_; lean_object* v___y_3400_; lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v___x_3390_ = lean_array_fget_borrowed(v_buf_3380_, v_recvIdx_3383_);
v___x_3391_ = lean_box(0);
v___x_3392_ = lean_st_ref_swap(v___x_3390_, v___x_3391_);
v___x_3398_ = 1;
v___x_3413_ = lean_unsigned_to_nat(1u);
v___x_3414_ = lean_nat_add(v_recvIdx_3383_, v___x_3413_);
lean_dec(v_recvIdx_3383_);
v___x_3415_ = lean_nat_dec_eq(v___x_3414_, v_capacity_3379_);
if (v___x_3415_ == 0)
{
v___y_3400_ = v___x_3414_;
goto v___jp_3399_;
}
else
{
lean_dec(v___x_3414_);
v___y_3400_ = v___x_3388_;
goto v___jp_3399_;
}
v___jp_3393_:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = lean_st_ref_set(v___y_3395_, v_st_3394_);
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3392_);
return v___x_3397_;
}
v___jp_3399_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3401_ = lean_unsigned_to_nat(1u);
v___x_3402_ = lean_nat_sub(v_bufCount_3381_, v___x_3401_);
lean_dec(v_bufCount_3381_);
lean_inc(v___y_3400_);
lean_inc(v_sendIdx_3382_);
lean_inc(v___x_3402_);
lean_inc_ref(v_buf_3380_);
lean_inc(v_capacity_3379_);
lean_inc_ref(v_consumers_3378_);
lean_inc_ref(v_producers_3377_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 6, v___y_3400_);
lean_ctor_set(v___x_3386_, 4, v___x_3402_);
v___x_3404_ = v___x_3386_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_producers_3377_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_consumers_3378_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_capacity_3379_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_buf_3380_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3412_, 5, v_sendIdx_3382_);
lean_ctor_set(v_reuseFailAlloc_3412_, 6, v___y_3400_);
lean_ctor_set_uint8(v_reuseFailAlloc_3412_, sizeof(void*)*7, v_closed_3384_);
v___x_3404_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3377_);
if (lean_obj_tag(v___x_3405_) == 1)
{
lean_object* v_val_3406_; lean_object* v_fst_3407_; lean_object* v_snd_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_dec_ref(v___x_3404_);
v_val_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_val_3406_);
lean_dec_ref(v___x_3405_);
v_fst_3407_ = lean_ctor_get(v_val_3406_, 0);
lean_inc(v_fst_3407_);
v_snd_3408_ = lean_ctor_get(v_val_3406_, 1);
lean_inc(v_snd_3408_);
lean_dec(v_val_3406_);
v___x_3409_ = lean_box(v___x_3398_);
v___x_3410_ = lean_io_promise_resolve(v___x_3409_, v_fst_3407_);
lean_dec(v_fst_3407_);
v___x_3411_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3411_, 0, v_snd_3408_);
lean_ctor_set(v___x_3411_, 1, v_consumers_3378_);
lean_ctor_set(v___x_3411_, 2, v_capacity_3379_);
lean_ctor_set(v___x_3411_, 3, v_buf_3380_);
lean_ctor_set(v___x_3411_, 4, v___x_3402_);
lean_ctor_set(v___x_3411_, 5, v_sendIdx_3382_);
lean_ctor_set(v___x_3411_, 6, v___y_3400_);
lean_ctor_set_uint8(v___x_3411_, sizeof(void*)*7, v_closed_3384_);
v_st_3394_ = v___x_3411_;
v___y_3395_ = v_a_3374_;
goto v___jp_3393_;
}
else
{
lean_dec(v___x_3405_);
lean_dec(v___x_3402_);
lean_dec(v___y_3400_);
lean_dec(v_sendIdx_3382_);
lean_dec_ref(v_buf_3380_);
lean_dec(v_capacity_3379_);
lean_dec_ref(v_consumers_3378_);
v_st_3394_ = v___x_3404_;
v___y_3395_ = v_a_3374_;
goto v___jp_3393_;
}
}
}
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_del_object(v___x_3386_);
lean_dec(v_recvIdx_3383_);
lean_dec(v_sendIdx_3382_);
lean_dec(v_bufCount_3381_);
lean_dec_ref(v_buf_3380_);
lean_dec(v_capacity_3379_);
lean_dec_ref(v_consumers_3378_);
lean_dec_ref(v_producers_3377_);
v___x_3416_ = lean_box(0);
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
return v___x_3417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3419_);
lean_dec(v_a_3419_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3423_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3426_, lean_object* v_a_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3426_, v_a_3427_);
lean_dec(v_a_3427_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3430_, lean_object* v_lose_3431_){
_start:
{
lean_object* v_finished_3433_; lean_object* v_promise_3434_; lean_object* v___x_3435_; uint8_t v___y_3437_; uint8_t v___x_3445_; 
v_finished_3433_ = lean_ctor_get(v_w_3430_, 0);
v_promise_3434_ = lean_ctor_get(v_w_3430_, 1);
v___x_3435_ = lean_st_ref_take(v_finished_3433_);
v___x_3445_ = lean_unbox(v___x_3435_);
lean_dec(v___x_3435_);
if (v___x_3445_ == 0)
{
uint8_t v___x_3446_; 
v___x_3446_ = 1;
v___y_3437_ = v___x_3446_;
goto v___jp_3436_;
}
else
{
uint8_t v___x_3447_; 
v___x_3447_ = 0;
v___y_3437_ = v___x_3447_;
goto v___jp_3436_;
}
v___jp_3436_:
{
uint8_t v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = 1;
v___x_3439_ = lean_box(v___x_3438_);
v___x_3440_ = lean_st_ref_set(v_finished_3433_, v___x_3439_);
if (v___y_3437_ == 0)
{
lean_object* v___x_3441_; 
v___x_3441_ = lean_apply_1(v_lose_3431_, lean_box(0));
return v___x_3441_;
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec_ref(v_lose_3431_);
v___x_3442_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0));
v___x_3443_ = lean_io_promise_resolve(v___x_3442_, v_promise_3434_);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
return v___x_3444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3448_, lean_object* v_lose_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3448_, v_lose_3449_);
lean_dec_ref(v_w_3448_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3452_, lean_object* v_w_3453_, lean_object* v_lose_3454_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3453_, v_lose_3454_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3457_, lean_object* v_w_3458_, lean_object* v_lose_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3457_, v_w_3458_, v_lose_3459_);
lean_dec_ref(v_w_3458_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3462_, lean_object* v_lose_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_finished_3466_; lean_object* v_promise_3467_; lean_object* v___x_3468_; uint8_t v___y_3470_; uint8_t v___x_3486_; 
v_finished_3466_ = lean_ctor_get(v_w_3462_, 0);
v_promise_3467_ = lean_ctor_get(v_w_3462_, 1);
v___x_3468_ = lean_st_ref_take(v_finished_3466_);
v___x_3486_ = lean_unbox(v___x_3468_);
lean_dec(v___x_3468_);
if (v___x_3486_ == 0)
{
uint8_t v___x_3487_; 
v___x_3487_ = 1;
v___y_3470_ = v___x_3487_;
goto v___jp_3469_;
}
else
{
uint8_t v___x_3488_; 
v___x_3488_ = 0;
v___y_3470_ = v___x_3488_;
goto v___jp_3469_;
}
v___jp_3469_:
{
uint8_t v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = 1;
v___x_3472_ = lean_box(v___x_3471_);
v___x_3473_ = lean_st_ref_set(v_finished_3466_, v___x_3472_);
if (v___y_3470_ == 0)
{
lean_object* v___x_3474_; 
lean_inc(v___y_3464_);
v___x_3474_ = lean_apply_2(v_lose_3463_, v___y_3464_, lean_box(0));
return v___x_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3485_; 
lean_dec_ref(v_lose_3463_);
v___x_3475_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3464_);
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3485_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3485_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_a_3476_);
v___x_3481_ = lean_io_promise_resolve(v___x_3480_, v_promise_3467_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3481_);
v___x_3483_ = v___x_3478_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3489_, lean_object* v_lose_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3489_, v_lose_3490_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec_ref(v_w_3489_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3494_, lean_object* v_w_3495_, lean_object* v_lose_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3495_, v_lose_3496_, v___y_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3500_, lean_object* v_w_3501_, lean_object* v_lose_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3500_, v_w_3501_, v_lose_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v_w_3501_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3506_, lean_object* v_k_3507_){
_start:
{
lean_object* v_ref_3509_; lean_object* v_mutex_3510_; lean_object* v___x_3511_; lean_object* v_r_3512_; 
v_ref_3509_ = lean_ctor_get(v_mutex_3506_, 0);
lean_inc(v_ref_3509_);
v_mutex_3510_ = lean_ctor_get(v_mutex_3506_, 1);
lean_inc(v_mutex_3510_);
lean_dec_ref(v_mutex_3506_);
v___x_3511_ = lean_io_basemutex_lock(v_mutex_3510_);
v_r_3512_ = lean_apply_2(v_k_3507_, v_ref_3509_, lean_box(0));
if (lean_obj_tag(v_r_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3521_; 
v_a_3513_ = lean_ctor_get(v_r_3512_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_r_3512_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3515_ = v_r_3512_;
v_isShared_3516_ = v_isSharedCheck_3521_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v_r_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3521_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3517_ = lean_io_basemutex_unlock(v_mutex_3510_);
lean_dec(v_mutex_3510_);
if (v_isShared_3516_ == 0)
{
v___x_3519_ = v___x_3515_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3513_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3530_; 
v_a_3522_ = lean_ctor_get(v_r_3512_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_r_3512_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3524_ = v_r_3512_;
v_isShared_3525_ = v_isSharedCheck_3530_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v_r_3512_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3530_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3526_ = lean_io_basemutex_unlock(v_mutex_3510_);
lean_dec(v_mutex_3510_);
if (v_isShared_3525_ == 0)
{
v___x_3528_ = v___x_3524_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3522_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3531_, lean_object* v_k_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3531_, v_k_3532_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3535_, lean_object* v_00_u03b2_3536_, lean_object* v_mutex_3537_, lean_object* v_k_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3537_, v_k_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3541_, lean_object* v_00_u03b2_3542_, lean_object* v_mutex_3543_, lean_object* v_k_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3541_, v_00_u03b2_3542_, v_mutex_3543_, v_k_3544_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3547_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3550_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; lean_object* v_producers_3557_; lean_object* v_consumers_3558_; lean_object* v_capacity_3559_; lean_object* v_buf_3560_; lean_object* v_bufCount_3561_; lean_object* v_sendIdx_3562_; lean_object* v_recvIdx_3563_; uint8_t v_closed_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3586_; 
v___x_3556_ = lean_st_ref_get(v___y_3554_);
v_producers_3557_ = lean_ctor_get(v___x_3556_, 0);
v_consumers_3558_ = lean_ctor_get(v___x_3556_, 1);
v_capacity_3559_ = lean_ctor_get(v___x_3556_, 2);
v_buf_3560_ = lean_ctor_get(v___x_3556_, 3);
v_bufCount_3561_ = lean_ctor_get(v___x_3556_, 4);
v_sendIdx_3562_ = lean_ctor_get(v___x_3556_, 5);
v_recvIdx_3563_ = lean_ctor_get(v___x_3556_, 6);
v_closed_3564_ = lean_ctor_get_uint8(v___x_3556_, sizeof(void*)*7);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3566_ = v___x_3556_;
v_isShared_3567_ = v_isSharedCheck_3586_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_recvIdx_3563_);
lean_inc(v_sendIdx_3562_);
lean_inc(v_bufCount_3561_);
lean_inc(v_buf_3560_);
lean_inc(v_capacity_3559_);
lean_inc(v_consumers_3558_);
lean_inc(v_producers_3557_);
lean_dec(v___x_3556_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3586_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3558_);
if (lean_obj_tag(v___x_3568_) == 1)
{
lean_object* v_val_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3583_; 
v_val_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3583_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_val_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3583_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v_fst_3573_; lean_object* v_snd_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
v_fst_3573_ = lean_ctor_get(v_val_3569_, 0);
lean_inc(v_fst_3573_);
v_snd_3574_ = lean_ctor_get(v_val_3569_, 1);
lean_inc(v_snd_3574_);
lean_dec(v_val_3569_);
v___x_3575_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3573_, v_____do__lift_3553_);
lean_dec(v_fst_3573_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 1, v_snd_3574_);
v___x_3577_ = v___x_3566_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_producers_3557_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_snd_3574_);
lean_ctor_set(v_reuseFailAlloc_3582_, 2, v_capacity_3559_);
lean_ctor_set(v_reuseFailAlloc_3582_, 3, v_buf_3560_);
lean_ctor_set(v_reuseFailAlloc_3582_, 4, v_bufCount_3561_);
lean_ctor_set(v_reuseFailAlloc_3582_, 5, v_sendIdx_3562_);
lean_ctor_set(v_reuseFailAlloc_3582_, 6, v_recvIdx_3563_);
lean_ctor_set_uint8(v_reuseFailAlloc_3582_, sizeof(void*)*7, v_closed_3564_);
v___x_3577_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3578_ = lean_st_ref_set(v___y_3554_, v___x_3577_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set_tag(v___x_3571_, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3578_);
v___x_3580_ = v___x_3571_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
lean_dec(v___x_3568_);
lean_del_object(v___x_3566_);
lean_dec(v_recvIdx_3563_);
lean_dec(v_sendIdx_3562_);
lean_dec(v_bufCount_3561_);
lean_dec_ref(v_buf_3560_);
lean_dec(v_capacity_3559_);
lean_dec_ref(v_producers_3557_);
v___x_3584_ = lean_box(0);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
uint8_t v_____do__lift_3921__boxed_3590_; lean_object* v_res_3591_; 
v_____do__lift_3921__boxed_3590_ = lean_unbox(v_____do__lift_3587_);
v_res_3591_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3921__boxed_3590_, v___y_3588_);
lean_dec(v___y_3588_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3592_, lean_object* v___f_3593_, uint8_t v_____do__lift_3594_, lean_object* v___y_3595_){
_start:
{
if (v_____do__lift_3594_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v_producers_3599_; lean_object* v_consumers_3600_; lean_object* v_capacity_3601_; lean_object* v_buf_3602_; lean_object* v_bufCount_3603_; lean_object* v_sendIdx_3604_; lean_object* v_recvIdx_3605_; uint8_t v_closed_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3620_; 
v___x_3597_ = lean_io_promise_new();
v___x_3598_ = lean_st_ref_take(v___y_3595_);
v_producers_3599_ = lean_ctor_get(v___x_3598_, 0);
v_consumers_3600_ = lean_ctor_get(v___x_3598_, 1);
v_capacity_3601_ = lean_ctor_get(v___x_3598_, 2);
v_buf_3602_ = lean_ctor_get(v___x_3598_, 3);
v_bufCount_3603_ = lean_ctor_get(v___x_3598_, 4);
v_sendIdx_3604_ = lean_ctor_get(v___x_3598_, 5);
v_recvIdx_3605_ = lean_ctor_get(v___x_3598_, 6);
v_closed_3606_ = lean_ctor_get_uint8(v___x_3598_, sizeof(void*)*7);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3608_ = v___x_3598_;
v_isShared_3609_ = v_isSharedCheck_3620_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_recvIdx_3605_);
lean_inc(v_sendIdx_3604_);
lean_inc(v_bufCount_3603_);
lean_inc(v_buf_3602_);
lean_inc(v_capacity_3601_);
lean_inc(v_consumers_3600_);
lean_inc(v_producers_3599_);
lean_dec(v___x_3598_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3620_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3610_, 0, v_waiter_3592_);
lean_inc(v___x_3597_);
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3597_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = l_Std_Queue_enqueue___redArg(v___x_3611_, v_consumers_3600_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 1, v___x_3612_);
v___x_3614_ = v___x_3608_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_producers_3599_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_capacity_3601_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_buf_3602_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_bufCount_3603_);
lean_ctor_set(v_reuseFailAlloc_3619_, 5, v_sendIdx_3604_);
lean_ctor_set(v_reuseFailAlloc_3619_, 6, v_recvIdx_3605_);
lean_ctor_set_uint8(v_reuseFailAlloc_3619_, sizeof(void*)*7, v_closed_3606_);
v___x_3614_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3615_ = lean_st_ref_set(v___y_3595_, v___x_3614_);
v___x_3616_ = lean_io_promise_result_opt(v___x_3597_);
lean_dec(v___x_3597_);
v___x_3617_ = lean_unsigned_to_nat(0u);
v___x_3618_ = l_EIO_chainTask___redArg(v___x_3616_, v___f_3593_, v___x_3617_, v_____do__lift_3594_);
return v___x_3618_;
}
}
}
else
{
lean_object* v___x_3621_; lean_object* v_lose_3622_; lean_object* v___x_3623_; 
lean_dec_ref(v___f_3593_);
v___x_3621_ = lean_box(v_____do__lift_3594_);
v_lose_3622_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3622_, 0, v___x_3621_);
v___x_3623_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3592_, v_lose_3622_, v___y_3595_);
lean_dec_ref(v_waiter_3592_);
return v___x_3623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3624_, lean_object* v___f_3625_, lean_object* v_____do__lift_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
uint8_t v_____do__lift_3977__boxed_3629_; lean_object* v_res_3630_; 
v_____do__lift_3977__boxed_3629_ = lean_unbox(v_____do__lift_3626_);
v_res_3630_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3624_, v___f_3625_, v_____do__lift_3977__boxed_3629_, v___y_3627_);
lean_dec(v___y_3627_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; lean_object* v_bufCount_3635_; uint8_t v_closed_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3634_ = lean_st_ref_get(v___y_3632_);
v_bufCount_3635_ = lean_ctor_get(v___x_3634_, 4);
lean_inc(v_bufCount_3635_);
v_closed_3636_ = lean_ctor_get_uint8(v___x_3634_, sizeof(void*)*7);
lean_dec(v___x_3634_);
v___x_3637_ = lean_unsigned_to_nat(0u);
v___x_3638_ = lean_nat_dec_eq(v_bufCount_3635_, v___x_3637_);
lean_dec(v_bufCount_3635_);
if (v___x_3638_ == 0)
{
uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = 1;
v___x_3640_ = lean_box(v___x_3639_);
lean_inc(v___y_3632_);
v___x_3641_ = lean_apply_3(v___f_3631_, v___x_3640_, v___y_3632_, lean_box(0));
return v___x_3641_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = lean_box(v_closed_3636_);
lean_inc(v___y_3632_);
v___x_3643_ = lean_apply_3(v___f_3631_, v___x_3642_, v___y_3632_, lean_box(0));
return v___x_3643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3644_, v___y_3645_);
lean_dec(v___y_3645_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3650_, lean_object* v_ch_3651_, lean_object* v_x_3652_){
_start:
{
if (lean_obj_tag(v_x_3652_) == 0)
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec_ref(v_ch_3651_);
lean_dec_ref(v_waiter_3650_);
v___x_3654_ = lean_box(0);
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
else
{
lean_object* v_val_3656_; uint8_t v___x_3657_; 
v_val_3656_ = lean_ctor_get(v_x_3652_, 0);
v___x_3657_ = lean_unbox(v_val_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___f_3658_; lean_object* v___x_3659_; 
lean_dec_ref(v_ch_3651_);
v___f_3658_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3659_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3650_, v___f_3658_);
lean_dec_ref(v_waiter_3650_);
return v___x_3659_;
}
else
{
lean_object* v___x_3660_; 
v___x_3660_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3651_, v_waiter_3650_);
return v___x_3660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3661_, lean_object* v_ch_3662_, lean_object* v_x_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3661_, v_ch_3662_, v_x_3663_);
lean_dec(v_x_3663_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3666_, lean_object* v_waiter_3667_){
_start:
{
lean_object* v___f_3669_; lean_object* v___f_3670_; lean_object* v___f_3671_; lean_object* v___x_3672_; 
lean_inc_ref(v_ch_3666_);
lean_inc_ref(v_waiter_3667_);
v___f_3669_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3669_, 0, v_waiter_3667_);
lean_closure_set(v___f_3669_, 1, v_ch_3666_);
v___f_3670_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3670_, 0, v_waiter_3667_);
lean_closure_set(v___f_3670_, 1, v___f_3669_);
v___f_3671_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3671_, 0, v___f_3670_);
v___x_3672_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3666_, v___f_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3673_, lean_object* v_waiter_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3673_, v_waiter_3674_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3677_, lean_object* v_ch_3678_, lean_object* v_waiter_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3678_, v_waiter_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_ch_3683_, lean_object* v_waiter_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3682_, v_ch_3683_, v_waiter_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3687_, lean_object* v_x_3688_){
_start:
{
if (lean_obj_tag(v_x_3688_) == 0)
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v_x_3687_);
v_a_3690_ = lean_ctor_get(v_x_3688_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_x_3688_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3692_ = v_x_3688_;
v_isShared_3693_ = v_isSharedCheck_3698_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v_x_3688_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3698_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
return v___x_3696_;
}
}
}
else
{
lean_object* v___x_3699_; 
lean_dec_ref(v_x_3688_);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v_x_3687_);
return v___x_3699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3700_, v_x_3701_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3704_, uint8_t v___x_3705_, lean_object* v___f_3706_, lean_object* v_____r_3707_, lean_object* v_st_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3711_ = lean_st_ref_set(v___y_3709_, v_st_3708_);
v___x_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
v___x_3714_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3704_, v___x_3705_, v___x_3713_, v___f_3706_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3715_, lean_object* v___x_3716_, lean_object* v___f_3717_, lean_object* v_____r_3718_, lean_object* v_st_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
uint8_t v___x_6388__boxed_3722_; lean_object* v_res_3723_; 
v___x_6388__boxed_3722_ = lean_unbox(v___x_3716_);
v_res_3723_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3715_, v___x_6388__boxed_3722_, v___f_3717_, v_____r_3718_, v_st_3719_, v___y_3720_);
lean_dec(v___y_3720_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3724_, lean_object* v_consumers_3725_, lean_object* v_capacity_3726_, lean_object* v_buf_3727_, lean_object* v___x_3728_, lean_object* v_sendIdx_3729_, lean_object* v___y_3730_, uint8_t v_closed_3731_, lean_object* v___f_3732_, lean_object* v_a_3733_, lean_object* v_x_3734_){
_start:
{
if (lean_obj_tag(v_x_3734_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3744_; 
lean_dec_ref(v___f_3732_);
lean_dec(v___y_3730_);
lean_dec(v_sendIdx_3729_);
lean_dec(v___x_3728_);
lean_dec_ref(v_buf_3727_);
lean_dec(v_capacity_3726_);
lean_dec_ref(v_consumers_3725_);
lean_dec_ref(v_snd_3724_);
v_a_3736_ = lean_ctor_get(v_x_3734_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_x_3734_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3738_ = v_x_3734_;
v_isShared_3739_ = v_isSharedCheck_3744_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v_x_3734_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3744_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3742_; 
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
return v___x_3742_;
}
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
lean_dec_ref(v_x_3734_);
v___x_3745_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3745_, 0, v_snd_3724_);
lean_ctor_set(v___x_3745_, 1, v_consumers_3725_);
lean_ctor_set(v___x_3745_, 2, v_capacity_3726_);
lean_ctor_set(v___x_3745_, 3, v_buf_3727_);
lean_ctor_set(v___x_3745_, 4, v___x_3728_);
lean_ctor_set(v___x_3745_, 5, v_sendIdx_3729_);
lean_ctor_set(v___x_3745_, 6, v___y_3730_);
lean_ctor_set_uint8(v___x_3745_, sizeof(void*)*7, v_closed_3731_);
v___x_3746_ = lean_box(0);
lean_inc(v_a_3733_);
v___x_3747_ = lean_apply_4(v___f_3732_, v___x_3746_, v___x_3745_, v_a_3733_, lean_box(0));
return v___x_3747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3748_, lean_object* v_consumers_3749_, lean_object* v_capacity_3750_, lean_object* v_buf_3751_, lean_object* v___x_3752_, lean_object* v_sendIdx_3753_, lean_object* v___y_3754_, lean_object* v_closed_3755_, lean_object* v___f_3756_, lean_object* v_a_3757_, lean_object* v_x_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v_closed_boxed_3760_; lean_object* v_res_3761_; 
v_closed_boxed_3760_ = lean_unbox(v_closed_3755_);
v_res_3761_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3748_, v_consumers_3749_, v_capacity_3750_, v_buf_3751_, v___x_3752_, v_sendIdx_3753_, v___y_3754_, v_closed_boxed_3760_, v___f_3756_, v_a_3757_, v_x_3758_);
lean_dec(v_a_3757_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3762_, uint8_t v___x_3763_, lean_object* v_bufCount_3764_, lean_object* v_producers_3765_, lean_object* v_consumers_3766_, lean_object* v_capacity_3767_, lean_object* v_buf_3768_, lean_object* v_sendIdx_3769_, uint8_t v_closed_3770_, uint8_t v___x_3771_, lean_object* v_a_3772_, lean_object* v_recvIdx_3773_, lean_object* v_x_3774_){
_start:
{
if (lean_obj_tag(v_x_3774_) == 0)
{
lean_object* v___x_3776_; 
lean_dec(v_sendIdx_3769_);
lean_dec_ref(v_buf_3768_);
lean_dec(v_capacity_3767_);
lean_dec_ref(v_consumers_3766_);
lean_dec_ref(v_producers_3765_);
lean_dec(v___x_3762_);
v___x_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3776_, 0, v_x_3774_);
return v___x_3776_;
}
else
{
lean_object* v___f_3777_; lean_object* v___x_3778_; lean_object* v___f_3779_; lean_object* v___y_3781_; lean_object* v___x_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; 
v___f_3777_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3777_, 0, v_x_3774_);
v___x_3778_ = lean_box(v___x_3763_);
lean_inc_ref(v___f_3777_);
lean_inc(v___x_3762_);
v___f_3779_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3779_, 0, v___x_3762_);
lean_closure_set(v___f_3779_, 1, v___x_3778_);
lean_closure_set(v___f_3779_, 2, v___f_3777_);
v___x_3804_ = lean_unsigned_to_nat(1u);
v___x_3805_ = lean_nat_add(v_recvIdx_3773_, v___x_3804_);
v___x_3806_ = lean_nat_dec_eq(v___x_3805_, v_capacity_3767_);
if (v___x_3806_ == 0)
{
v___y_3781_ = v___x_3805_;
goto v___jp_3780_;
}
else
{
lean_dec(v___x_3805_);
lean_inc(v___x_3762_);
v___y_3781_ = v___x_3762_;
goto v___jp_3780_;
}
v___jp_3780_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = lean_nat_sub(v_bufCount_3764_, v___x_3782_);
lean_inc(v___y_3781_);
lean_inc(v_sendIdx_3769_);
lean_inc(v___x_3783_);
lean_inc_ref(v_buf_3768_);
lean_inc(v_capacity_3767_);
lean_inc_ref(v_consumers_3766_);
lean_inc_ref(v_producers_3765_);
v___x_3784_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3784_, 0, v_producers_3765_);
lean_ctor_set(v___x_3784_, 1, v_consumers_3766_);
lean_ctor_set(v___x_3784_, 2, v_capacity_3767_);
lean_ctor_set(v___x_3784_, 3, v_buf_3768_);
lean_ctor_set(v___x_3784_, 4, v___x_3783_);
lean_ctor_set(v___x_3784_, 5, v_sendIdx_3769_);
lean_ctor_set(v___x_3784_, 6, v___y_3781_);
lean_ctor_set_uint8(v___x_3784_, sizeof(void*)*7, v_closed_3770_);
v___x_3785_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3765_);
if (lean_obj_tag(v___x_3785_) == 1)
{
lean_object* v_val_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v___x_3784_);
lean_dec_ref(v___f_3777_);
v_val_3786_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3788_ = v___x_3785_;
v_isShared_3789_ = v_isSharedCheck_3801_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_val_3786_);
lean_dec(v___x_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3801_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v_fst_3790_; lean_object* v_snd_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___f_3795_; lean_object* v___x_3797_; 
v_fst_3790_ = lean_ctor_get(v_val_3786_, 0);
lean_inc(v_fst_3790_);
v_snd_3791_ = lean_ctor_get(v_val_3786_, 1);
lean_inc(v_snd_3791_);
lean_dec(v_val_3786_);
v___x_3792_ = lean_box(v___x_3771_);
v___x_3793_ = lean_io_promise_resolve(v___x_3792_, v_fst_3790_);
lean_dec(v_fst_3790_);
v___x_3794_ = lean_box(v_closed_3770_);
lean_inc(v_a_3772_);
v___f_3795_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3795_, 0, v_snd_3791_);
lean_closure_set(v___f_3795_, 1, v_consumers_3766_);
lean_closure_set(v___f_3795_, 2, v_capacity_3767_);
lean_closure_set(v___f_3795_, 3, v_buf_3768_);
lean_closure_set(v___f_3795_, 4, v___x_3783_);
lean_closure_set(v___f_3795_, 5, v_sendIdx_3769_);
lean_closure_set(v___f_3795_, 6, v___y_3781_);
lean_closure_set(v___f_3795_, 7, v___x_3794_);
lean_closure_set(v___f_3795_, 8, v___f_3779_);
lean_closure_set(v___f_3795_, 9, v_a_3772_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 0, v___x_3793_);
v___x_3797_ = v___x_3788_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3793_);
v___x_3797_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
v___x_3799_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3762_, v___x_3763_, v___x_3798_, v___f_3795_);
return v___x_3799_;
}
}
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_dec(v___x_3785_);
lean_dec(v___x_3783_);
lean_dec(v___y_3781_);
lean_dec_ref(v___f_3779_);
lean_dec(v_sendIdx_3769_);
lean_dec_ref(v_buf_3768_);
lean_dec(v_capacity_3767_);
lean_dec_ref(v_consumers_3766_);
v___x_3802_ = lean_box(0);
v___x_3803_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3762_, v___x_3763_, v___f_3777_, v___x_3802_, v___x_3784_, v_a_3772_);
return v___x_3803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3807_, lean_object* v___x_3808_, lean_object* v_bufCount_3809_, lean_object* v_producers_3810_, lean_object* v_consumers_3811_, lean_object* v_capacity_3812_, lean_object* v_buf_3813_, lean_object* v_sendIdx_3814_, lean_object* v_closed_3815_, lean_object* v___x_3816_, lean_object* v_a_3817_, lean_object* v_recvIdx_3818_, lean_object* v_x_3819_, lean_object* v___y_3820_){
_start:
{
uint8_t v___x_6457__boxed_3821_; uint8_t v_closed_boxed_3822_; uint8_t v___x_6458__boxed_3823_; lean_object* v_res_3824_; 
v___x_6457__boxed_3821_ = lean_unbox(v___x_3808_);
v_closed_boxed_3822_ = lean_unbox(v_closed_3815_);
v___x_6458__boxed_3823_ = lean_unbox(v___x_3816_);
v_res_3824_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3807_, v___x_6457__boxed_3821_, v_bufCount_3809_, v_producers_3810_, v_consumers_3811_, v_capacity_3812_, v_buf_3813_, v_sendIdx_3814_, v_closed_boxed_3822_, v___x_6458__boxed_3823_, v_a_3817_, v_recvIdx_3818_, v_x_3819_);
lean_dec(v_recvIdx_3818_);
lean_dec(v_a_3817_);
lean_dec(v_bufCount_3809_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3825_, lean_object* v_x_3826_){
_start:
{
if (lean_obj_tag(v_x_3826_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3836_; 
v_a_3828_ = lean_ctor_get(v_x_3826_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_x_3826_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3830_ = v_x_3826_;
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v_x_3826_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3836_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
return v___x_3834_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3865_; 
v_a_3837_ = lean_ctor_get(v_x_3826_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_x_3826_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3839_ = v_x_3826_;
v_isShared_3840_ = v_isSharedCheck_3865_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v_x_3826_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3865_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_producers_3841_; lean_object* v_consumers_3842_; lean_object* v_capacity_3843_; lean_object* v_buf_3844_; lean_object* v_bufCount_3845_; lean_object* v_sendIdx_3846_; lean_object* v_recvIdx_3847_; uint8_t v_closed_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; 
v_producers_3841_ = lean_ctor_get(v_a_3837_, 0);
lean_inc_ref(v_producers_3841_);
v_consumers_3842_ = lean_ctor_get(v_a_3837_, 1);
lean_inc_ref(v_consumers_3842_);
v_capacity_3843_ = lean_ctor_get(v_a_3837_, 2);
lean_inc(v_capacity_3843_);
v_buf_3844_ = lean_ctor_get(v_a_3837_, 3);
lean_inc_ref(v_buf_3844_);
v_bufCount_3845_ = lean_ctor_get(v_a_3837_, 4);
lean_inc(v_bufCount_3845_);
v_sendIdx_3846_ = lean_ctor_get(v_a_3837_, 5);
lean_inc(v_sendIdx_3846_);
v_recvIdx_3847_ = lean_ctor_get(v_a_3837_, 6);
lean_inc(v_recvIdx_3847_);
v_closed_3848_ = lean_ctor_get_uint8(v_a_3837_, sizeof(void*)*7);
lean_dec(v_a_3837_);
v___x_3849_ = lean_unsigned_to_nat(0u);
v___x_3850_ = lean_nat_dec_eq(v_bufCount_3845_, v___x_3849_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___f_3858_; lean_object* v___x_3860_; 
v___x_3851_ = lean_array_fget_borrowed(v_buf_3844_, v_recvIdx_3847_);
v___x_3852_ = lean_box(0);
v___x_3853_ = lean_st_ref_swap(v___x_3851_, v___x_3852_);
v___x_3854_ = 1;
v___x_3855_ = lean_box(v___x_3850_);
v___x_3856_ = lean_box(v_closed_3848_);
v___x_3857_ = lean_box(v___x_3854_);
lean_inc(v_a_3825_);
v___f_3858_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_3858_, 0, v___x_3849_);
lean_closure_set(v___f_3858_, 1, v___x_3855_);
lean_closure_set(v___f_3858_, 2, v_bufCount_3845_);
lean_closure_set(v___f_3858_, 3, v_producers_3841_);
lean_closure_set(v___f_3858_, 4, v_consumers_3842_);
lean_closure_set(v___f_3858_, 5, v_capacity_3843_);
lean_closure_set(v___f_3858_, 6, v_buf_3844_);
lean_closure_set(v___f_3858_, 7, v_sendIdx_3846_);
lean_closure_set(v___f_3858_, 8, v___x_3856_);
lean_closure_set(v___f_3858_, 9, v___x_3857_);
lean_closure_set(v___f_3858_, 10, v_a_3825_);
lean_closure_set(v___f_3858_, 11, v_recvIdx_3847_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3853_);
v___x_3860_ = v___x_3839_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3853_);
v___x_3860_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
v___x_3862_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3849_, v___x_3850_, v___x_3861_, v___f_3858_);
return v___x_3862_;
}
}
else
{
lean_object* v___x_3864_; 
lean_dec(v_recvIdx_3847_);
lean_dec(v_sendIdx_3846_);
lean_dec(v_bufCount_3845_);
lean_dec_ref(v_buf_3844_);
lean_dec(v_capacity_3843_);
lean_dec_ref(v_consumers_3842_);
lean_dec_ref(v_producers_3841_);
lean_del_object(v___x_3839_);
v___x_3864_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_3864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_3866_, lean_object* v_x_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3866_, v_x_3867_);
lean_dec(v_a_3866_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_3870_){
_start:
{
lean_object* v___x_3872_; lean_object* v___f_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; lean_object* v___x_3878_; 
v___x_3872_ = lean_st_ref_get(v_a_3870_);
lean_inc(v_a_3870_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3873_, 0, v_a_3870_);
v___x_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3872_);
v___x_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
v___x_3876_ = lean_unsigned_to_nat(0u);
v___x_3877_ = 0;
v___x_3878_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3876_, v___x_3877_, v___x_3875_, v___f_3873_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3879_);
lean_dec(v_a_3879_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_3886_, lean_object* v_a_3887_, lean_object* v___y_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_3886_, v_a_3887_);
lean_dec(v_a_3887_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_3890_, lean_object* v_x_3891_){
_start:
{
lean_object* v_val_3894_; lean_object* v___x_3896_; 
v___x_3896_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3890_, v_x_3891_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set_tag(v___x_3899_, 1);
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
v_val_3894_ = v___x_3902_;
goto v___jp_3893_;
}
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
v_a_3905_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3896_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3896_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set_tag(v___x_3907_, 0);
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
v_val_3894_ = v___x_3910_;
goto v___jp_3893_;
}
}
}
v___jp_3893_:
{
lean_object* v___x_3895_; 
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v_val_3894_);
return v___x_3895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_3913_, lean_object* v_x_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_3913_, v_x_3914_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v_x_3917_){
_start:
{
uint8_t v___y_3920_; 
if (lean_obj_tag(v_x_3917_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3932_; 
v_a_3924_ = lean_ctor_get(v_x_3917_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_x_3917_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3926_ = v_x_3917_;
v_isShared_3927_ = v_isSharedCheck_3932_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v_x_3917_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3932_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3930_; 
v___x_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
return v___x_3930_;
}
}
}
else
{
lean_object* v_a_3933_; lean_object* v_bufCount_3934_; uint8_t v_closed_3935_; lean_object* v___x_3936_; uint8_t v___x_3937_; 
v_a_3933_ = lean_ctor_get(v_x_3917_, 0);
lean_inc(v_a_3933_);
lean_dec_ref(v_x_3917_);
v_bufCount_3934_ = lean_ctor_get(v_a_3933_, 4);
lean_inc(v_bufCount_3934_);
v_closed_3935_ = lean_ctor_get_uint8(v_a_3933_, sizeof(void*)*7);
lean_dec(v_a_3933_);
v___x_3936_ = lean_unsigned_to_nat(0u);
v___x_3937_ = lean_nat_dec_eq(v_bufCount_3934_, v___x_3936_);
lean_dec(v_bufCount_3934_);
if (v___x_3937_ == 0)
{
uint8_t v___x_3938_; 
v___x_3938_ = 1;
v___y_3920_ = v___x_3938_;
goto v___jp_3919_;
}
else
{
v___y_3920_ = v_closed_3935_;
goto v___jp_3919_;
}
}
v___jp_3919_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = lean_box(v___y_3920_);
v___x_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
return v___x_3923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v_x_3939_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___y_3942_, lean_object* v___f_3943_, lean_object* v_x_3944_){
_start:
{
if (lean_obj_tag(v_x_3944_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v___f_3943_);
v_a_3946_ = lean_ctor_get(v_x_3944_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_x_3944_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3948_ = v_x_3944_;
v_isShared_3949_ = v_isSharedCheck_3954_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v_x_3944_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3954_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
return v___x_3952_;
}
}
}
else
{
lean_object* v_a_3955_; uint8_t v___x_3956_; 
v_a_3955_ = lean_ctor_get(v_x_3944_, 0);
lean_inc(v_a_3955_);
lean_dec_ref(v_x_3944_);
v___x_3956_ = lean_unbox(v_a_3955_);
lean_dec(v_a_3955_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; 
lean_dec_ref(v___f_3943_);
v___x_3957_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; lean_object* v___x_3961_; 
v___x_3958_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_3942_);
v___x_3959_ = lean_unsigned_to_nat(0u);
v___x_3960_ = 0;
v___x_3961_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3959_, v___x_3960_, v___x_3958_, v___f_3943_);
return v___x_3961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___y_3962_, lean_object* v___f_3963_, lean_object* v_x_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___y_3962_, v___f_3963_, v_x_3964_);
lean_dec(v___y_3962_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_3967_, lean_object* v___f_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; uint8_t v___x_3975_; lean_object* v___x_3976_; lean_object* v___f_3977_; lean_object* v___x_3978_; 
v___x_3971_ = lean_st_ref_get(v___y_3969_);
v___x_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
v___x_3974_ = lean_unsigned_to_nat(0u);
v___x_3975_ = 0;
v___x_3976_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3974_, v___x_3975_, v___x_3973_, v___f_3967_);
lean_inc(v___y_3969_);
v___f_3977_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3977_, 0, v___y_3969_);
lean_closure_set(v___f_3977_, 1, v___f_3968_);
v___x_3978_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3974_, v___x_3975_, v___x_3976_, v___f_3977_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_3979_, lean_object* v___f_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_3979_, v___f_3980_, v___y_3981_);
lean_dec(v___y_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_3984_, lean_object* v_capacity_3985_, lean_object* v_buf_3986_, lean_object* v_bufCount_3987_, lean_object* v_sendIdx_3988_, lean_object* v_recvIdx_3989_, uint8_t v_closed_3990_, lean_object* v___y_3991_, lean_object* v_x_3992_){
_start:
{
if (lean_obj_tag(v_x_3992_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4002_; 
lean_dec(v_recvIdx_3989_);
lean_dec(v_sendIdx_3988_);
lean_dec(v_bufCount_3987_);
lean_dec_ref(v_buf_3986_);
lean_dec(v_capacity_3985_);
lean_dec_ref(v_producers_3984_);
v_a_3994_ = lean_ctor_get(v_x_3992_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_x_3992_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3996_ = v_x_3992_;
v_isShared_3997_ = v_isSharedCheck_4002_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v_x_3992_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4002_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4013_; 
v_a_4003_ = lean_ctor_get(v_x_3992_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_x_3992_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4005_ = v_x_3992_;
v_isShared_4006_ = v_isSharedCheck_4013_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v_x_3992_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4013_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4010_; 
v___x_4007_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_4007_, 0, v_producers_3984_);
lean_ctor_set(v___x_4007_, 1, v_a_4003_);
lean_ctor_set(v___x_4007_, 2, v_capacity_3985_);
lean_ctor_set(v___x_4007_, 3, v_buf_3986_);
lean_ctor_set(v___x_4007_, 4, v_bufCount_3987_);
lean_ctor_set(v___x_4007_, 5, v_sendIdx_3988_);
lean_ctor_set(v___x_4007_, 6, v_recvIdx_3989_);
lean_ctor_set_uint8(v___x_4007_, sizeof(void*)*7, v_closed_3990_);
v___x_4008_ = lean_st_ref_set(v___y_3991_, v___x_4007_);
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 0, v___x_4008_);
v___x_4010_ = v___x_4005_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4008_);
v___x_4010_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_4014_, lean_object* v_capacity_4015_, lean_object* v_buf_4016_, lean_object* v_bufCount_4017_, lean_object* v_sendIdx_4018_, lean_object* v_recvIdx_4019_, lean_object* v_closed_4020_, lean_object* v___y_4021_, lean_object* v_x_4022_, lean_object* v___y_4023_){
_start:
{
uint8_t v_closed_boxed_4024_; lean_object* v_res_4025_; 
v_closed_boxed_4024_ = lean_unbox(v_closed_4020_);
v_res_4025_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_4014_, v_capacity_4015_, v_buf_4016_, v_bufCount_4017_, v_sendIdx_4018_, v_recvIdx_4019_, v_closed_boxed_4024_, v___y_4021_, v_x_4022_);
lean_dec(v___y_4021_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_4026_, lean_object* v_x_4027_, lean_object* v_head_4028_, lean_object* v_x_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_4026_, v_x_4027_, v_head_4028_, v_x_4029_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_4032_, lean_object* v_x_4033_){
_start:
{
if (lean_obj_tag(v_x_4032_) == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4035_, 0, v_x_4033_);
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
return v___x_4036_;
}
else
{
lean_object* v_head_4037_; lean_object* v_tail_4038_; lean_object* v_waiter_4039_; lean_object* v___f_4040_; lean_object* v_val_4042_; 
v_head_4037_ = lean_ctor_get(v_x_4032_, 0);
lean_inc(v_head_4037_);
v_tail_4038_ = lean_ctor_get(v_x_4032_, 1);
lean_inc(v_tail_4038_);
lean_dec_ref(v_x_4032_);
v_waiter_4039_ = lean_ctor_get(v_head_4037_, 1);
lean_inc(v_waiter_4039_);
v___f_4040_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4040_, 0, v_tail_4038_);
lean_closure_set(v___f_4040_, 1, v_x_4033_);
lean_closure_set(v___f_4040_, 2, v_head_4037_);
if (lean_obj_tag(v_waiter_4039_) == 0)
{
lean_object* v___x_4046_; 
v___x_4046_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v_val_4042_ = v___x_4046_;
goto v___jp_4041_;
}
else
{
lean_object* v_val_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4061_; 
v_val_4047_ = lean_ctor_get(v_waiter_4039_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_waiter_4039_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4049_ = v_waiter_4039_;
v_isShared_4050_ = v_isSharedCheck_4061_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_val_4047_);
lean_dec(v_waiter_4039_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4061_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_finished_4051_; lean_object* v___x_4052_; lean_object* v___f_4053_; lean_object* v___x_4055_; 
v_finished_4051_ = lean_ctor_get(v_val_4047_, 0);
lean_inc(v_finished_4051_);
lean_dec(v_val_4047_);
v___x_4052_ = lean_st_ref_get(v_finished_4051_);
lean_dec(v_finished_4051_);
v___f_4053_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4052_);
v___x_4055_ = v___x_4049_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4052_);
v___x_4055_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; lean_object* v___x_4059_; 
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
v___x_4057_ = lean_unsigned_to_nat(0u);
v___x_4058_ = 0;
v___x_4059_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4057_, v___x_4058_, v___x_4056_, v___f_4053_);
v_val_4042_ = v___x_4059_;
goto v___jp_4041_;
}
}
}
v___jp_4041_:
{
lean_object* v___x_4043_; uint8_t v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = lean_unsigned_to_nat(0u);
v___x_4044_ = 0;
v___x_4045_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4043_, v___x_4044_, v_val_4042_, v___f_4040_);
return v___x_4045_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_4062_, lean_object* v_x_4063_, lean_object* v_head_4064_, lean_object* v_x_4065_){
_start:
{
if (lean_obj_tag(v_x_4065_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4075_; 
lean_dec_ref(v_head_4064_);
lean_dec(v_x_4063_);
lean_dec(v_tail_4062_);
v_a_4067_ = lean_ctor_get(v_x_4065_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_x_4065_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4069_ = v_x_4065_;
v_isShared_4070_ = v_isSharedCheck_4075_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v_x_4065_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4075_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
}
}
else
{
lean_object* v_a_4076_; uint8_t v___x_4077_; 
v_a_4076_ = lean_ctor_get(v_x_4065_, 0);
lean_inc(v_a_4076_);
lean_dec_ref(v_x_4065_);
v___x_4077_ = lean_unbox(v_a_4076_);
lean_dec(v_a_4076_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
lean_dec_ref(v_head_4064_);
v___x_4078_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4062_, v_x_4063_);
return v___x_4078_;
}
else
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4079_, 0, v_head_4064_);
lean_ctor_set(v___x_4079_, 1, v_x_4063_);
v___x_4080_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4062_, v___x_4079_);
return v___x_4080_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4081_, lean_object* v_x_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4081_, v_x_4082_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4085_){
_start:
{
if (lean_obj_tag(v_x_4085_) == 0)
{
lean_object* v___x_4087_; 
v___x_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4087_, 0, v_x_4085_);
return v___x_4087_;
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4097_; 
v_a_4088_ = lean_ctor_get(v_x_4085_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_x_4085_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4090_ = v_x_4085_;
v_isShared_4091_ = v_isSharedCheck_4097_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v_x_4085_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4097_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4092_; lean_object* v___x_4094_; 
v___x_4092_ = l_List_reverse___redArg(v_a_4088_);
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4092_);
v___x_4094_ = v___x_4090_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4092_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4098_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4101_, lean_object* v___x_4102_, lean_object* v_x_4103_){
_start:
{
if (lean_obj_tag(v_x_4103_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4113_; 
lean_dec(v___x_4102_);
lean_dec(v_a_4101_);
v_a_4105_ = lean_ctor_get(v_x_4103_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_x_4103_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4107_ = v_x_4103_;
v_isShared_4108_ = v_isSharedCheck_4113_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v_x_4103_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4113_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
return v___x_4111_;
}
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4130_; 
v_a_4114_ = lean_ctor_get(v_x_4103_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_x_4103_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4116_ = v_x_4103_;
v_isShared_4117_ = v_isSharedCheck_4130_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v_x_4103_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4130_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
uint8_t v___x_4118_; 
v___x_4118_ = l_List_isEmpty___redArg(v_a_4101_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4119_; lean_object* v___x_4121_; 
lean_dec(v___x_4102_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v_a_4114_);
lean_ctor_set(v___x_4119_, 1, v_a_4101_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4119_);
v___x_4121_ = v___x_4116_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4119_);
v___x_4121_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
lean_object* v___x_4122_; 
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
return v___x_4122_;
}
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4127_; 
lean_dec(v_a_4101_);
v___x_4124_ = l_List_reverse___redArg(v_a_4114_);
v___x_4125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4102_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4125_);
v___x_4127_ = v___x_4116_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
lean_object* v___x_4128_; 
v___x_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
return v___x_4128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4131_, lean_object* v___x_4132_, lean_object* v_x_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4131_, v___x_4132_, v_x_4133_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_eList_4136_, lean_object* v___x_4137_, lean_object* v___f_4138_, lean_object* v_x_4139_){
_start:
{
if (lean_obj_tag(v_x_4139_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4149_; 
lean_dec_ref(v___f_4138_);
lean_dec(v___x_4137_);
lean_dec(v_eList_4136_);
v_a_4141_ = lean_ctor_get(v_x_4139_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v_x_4139_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4143_ = v_x_4139_;
v_isShared_4144_ = v_isSharedCheck_4149_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v_x_4139_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4149_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
lean_object* v___x_4147_; 
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
return v___x_4147_;
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; lean_object* v___x_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; 
v_a_4150_ = lean_ctor_get(v_x_4139_, 0);
lean_inc(v_a_4150_);
lean_dec_ref(v_x_4139_);
lean_inc(v___x_4137_);
v___x_4151_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4136_, v___x_4137_);
v___x_4152_ = lean_unsigned_to_nat(0u);
v___x_4153_ = 0;
v___x_4154_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4152_, v___x_4153_, v___x_4151_, v___f_4138_);
v___f_4155_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4155_, 0, v_a_4150_);
lean_closure_set(v___f_4155_, 1, v___x_4137_);
v___x_4156_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4152_, v___x_4153_, v___x_4154_, v___f_4155_);
return v___x_4156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_eList_4157_, lean_object* v___x_4158_, lean_object* v___f_4159_, lean_object* v_x_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v_eList_4157_, v___x_4158_, v___f_4159_, v_x_4160_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_eList_4167_; lean_object* v_dList_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___f_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___f_4175_; lean_object* v___x_4176_; 
v_eList_4167_ = lean_ctor_get(v_q_4164_, 0);
lean_inc(v_eList_4167_);
v_dList_4168_ = lean_ctor_get(v_q_4164_, 1);
lean_inc(v_dList_4168_);
lean_dec_ref(v_q_4164_);
v___x_4169_ = lean_box(0);
v___x_4170_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4168_, v___x_4169_);
v___f_4171_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4172_ = lean_unsigned_to_nat(0u);
v___x_4173_ = 0;
v___x_4174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4172_, v___x_4173_, v___x_4170_, v___f_4171_);
v___f_4175_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4175_, 0, v_eList_4167_);
lean_closure_set(v___f_4175_, 1, v___x_4169_);
lean_closure_set(v___f_4175_, 2, v___f_4171_);
v___x_4176_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4172_, v___x_4173_, v___x_4174_, v___f_4175_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4177_, v___y_4178_);
lean_dec(v___y_4178_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4181_, lean_object* v_x_4182_){
_start:
{
if (lean_obj_tag(v_x_4182_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4192_; 
v_a_4184_ = lean_ctor_get(v_x_4182_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v_x_4182_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4186_ = v_x_4182_;
v_isShared_4187_ = v_isSharedCheck_4192_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v_x_4182_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4192_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4190_; 
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v_producers_4194_; lean_object* v_consumers_4195_; lean_object* v_capacity_4196_; lean_object* v_buf_4197_; lean_object* v_bufCount_4198_; lean_object* v_sendIdx_4199_; lean_object* v_recvIdx_4200_; uint8_t v_closed_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___f_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; lean_object* v___x_4207_; 
v_a_4193_ = lean_ctor_get(v_x_4182_, 0);
lean_inc(v_a_4193_);
lean_dec_ref(v_x_4182_);
v_producers_4194_ = lean_ctor_get(v_a_4193_, 0);
lean_inc_ref(v_producers_4194_);
v_consumers_4195_ = lean_ctor_get(v_a_4193_, 1);
lean_inc_ref(v_consumers_4195_);
v_capacity_4196_ = lean_ctor_get(v_a_4193_, 2);
lean_inc(v_capacity_4196_);
v_buf_4197_ = lean_ctor_get(v_a_4193_, 3);
lean_inc_ref(v_buf_4197_);
v_bufCount_4198_ = lean_ctor_get(v_a_4193_, 4);
lean_inc(v_bufCount_4198_);
v_sendIdx_4199_ = lean_ctor_get(v_a_4193_, 5);
lean_inc(v_sendIdx_4199_);
v_recvIdx_4200_ = lean_ctor_get(v_a_4193_, 6);
lean_inc(v_recvIdx_4200_);
v_closed_4201_ = lean_ctor_get_uint8(v_a_4193_, sizeof(void*)*7);
lean_dec(v_a_4193_);
v___x_4202_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4195_, v___y_4181_);
v___x_4203_ = lean_box(v_closed_4201_);
lean_inc(v___y_4181_);
v___f_4204_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4204_, 0, v_producers_4194_);
lean_closure_set(v___f_4204_, 1, v_capacity_4196_);
lean_closure_set(v___f_4204_, 2, v_buf_4197_);
lean_closure_set(v___f_4204_, 3, v_bufCount_4198_);
lean_closure_set(v___f_4204_, 4, v_sendIdx_4199_);
lean_closure_set(v___f_4204_, 5, v_recvIdx_4200_);
lean_closure_set(v___f_4204_, 6, v___x_4203_);
lean_closure_set(v___f_4204_, 7, v___y_4181_);
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = 0;
v___x_4207_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4205_, v___x_4206_, v___x_4202_, v___f_4204_);
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4208_, lean_object* v_x_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4208_, v_x_4209_);
lean_dec(v___y_4208_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4212_){
_start:
{
lean_object* v___x_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; lean_object* v___x_4220_; 
v___x_4214_ = lean_st_ref_get(v___y_4212_);
lean_inc(v___y_4212_);
v___f_4215_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4215_, 0, v___y_4212_);
v___x_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4214_);
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4216_);
v___x_4218_ = lean_unsigned_to_nat(0u);
v___x_4219_ = 0;
v___x_4220_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4218_, v___x_4219_, v___x_4217_, v___f_4215_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4221_);
lean_dec(v___y_4221_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4229_){
_start:
{
lean_object* v___f_4230_; lean_object* v___f_4231_; lean_object* v___f_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_inc_ref_n(v_ch_4229_, 2);
v___f_4230_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4230_, 0, v_ch_4229_);
v___f_4231_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___f_4232_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2));
v___x_4233_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4233_, 0, lean_box(0));
lean_closure_set(v___x_4233_, 1, lean_box(0));
lean_closure_set(v___x_4233_, 2, v_ch_4229_);
lean_closure_set(v___x_4233_, 3, v___f_4231_);
v___x_4234_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4234_, 0, lean_box(0));
lean_closure_set(v___x_4234_, 1, lean_box(0));
lean_closure_set(v___x_4234_, 2, v_ch_4229_);
lean_closure_set(v___x_4234_, 3, v___f_4232_);
v___x_4235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4233_);
lean_ctor_set(v___x_4235_, 1, v___f_4230_);
lean_ctor_set(v___x_4235_, 2, v___x_4234_);
return v___x_4235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4236_, lean_object* v_ch_4237_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4239_, lean_object* v_q_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4240_, v___y_4241_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4244_, lean_object* v_q_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4244_, v_q_4245_, v___y_4246_);
lean_dec(v___y_4246_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4249_, lean_object* v_x_4250_, lean_object* v_x_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4250_, v_x_4251_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4255_, lean_object* v_x_4256_, lean_object* v_x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4255_, v_x_4256_, v_x_4257_, v___y_4258_);
lean_dec(v___y_4258_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg(lean_object* v_x_4261_){
_start:
{
switch(lean_obj_tag(v_x_4261_))
{
case 0:
{
lean_object* v___x_4262_; 
v___x_4262_ = lean_unsigned_to_nat(0u);
return v___x_4262_;
}
case 1:
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_unsigned_to_nat(1u);
return v___x_4263_;
}
default: 
{
lean_object* v___x_4264_; 
v___x_4264_ = lean_unsigned_to_nat(2u);
return v___x_4264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(lean_object* v_x_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4265_);
lean_dec_ref(v_x_4265_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx(lean_object* v_00_u03b1_4267_, lean_object* v_x_4268_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_4268_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___boxed(lean_object* v_00_u03b1_4270_, lean_object* v_x_4271_){
_start:
{
lean_object* v_res_4272_; 
v_res_4272_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_4270_, v_x_4271_);
lean_dec_ref(v_x_4271_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4273_, lean_object* v_k_4274_){
_start:
{
lean_object* v_ch_4275_; lean_object* v___x_4276_; 
v_ch_4275_ = lean_ctor_get(v_t_4273_, 0);
lean_inc_ref(v_ch_4275_);
lean_dec_ref(v_t_4273_);
v___x_4276_ = lean_apply_1(v_k_4274_, v_ch_4275_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4277_, lean_object* v_motive_4278_, lean_object* v_ctorIdx_4279_, lean_object* v_t_4280_, lean_object* v_h_4281_, lean_object* v_k_4282_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4280_, v_k_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4284_, lean_object* v_motive_4285_, lean_object* v_ctorIdx_4286_, lean_object* v_t_4287_, lean_object* v_h_4288_, lean_object* v_k_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4284_, v_motive_4285_, v_ctorIdx_4286_, v_t_4287_, v_h_4288_, v_k_4289_);
lean_dec(v_ctorIdx_4286_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4291_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4292_){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4291_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4294_, lean_object* v_motive_4295_, lean_object* v_t_4296_, lean_object* v_h_4297_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4298_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4296_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4300_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4300_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4303_, lean_object* v_motive_4304_, lean_object* v_t_4305_, lean_object* v_h_4306_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4307_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4305_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4307_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4309_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4310_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4309_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4312_, lean_object* v_motive_4313_, lean_object* v_t_4314_, lean_object* v_h_4315_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4316_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4314_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4318_){
_start:
{
if (lean_obj_tag(v_capacity_4318_) == 0)
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4320_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
return v___x_4321_;
}
else
{
lean_object* v_val_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4339_; 
v_val_4322_ = lean_ctor_get(v_capacity_4318_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_capacity_4318_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4324_ = v_capacity_4318_;
v_isShared_4325_ = v_isSharedCheck_4339_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_val_4322_);
lean_dec(v_capacity_4318_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4339_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v_zero_4326_; uint8_t v_isZero_4327_; 
v_zero_4326_ = lean_unsigned_to_nat(0u);
v_isZero_4327_ = lean_nat_dec_eq(v_val_4322_, v_zero_4326_);
if (v_isZero_4327_ == 1)
{
lean_object* v___x_4328_; lean_object* v___x_4330_; 
lean_dec(v_val_4322_);
v___x_4328_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v___x_4328_);
v___x_4330_ = v___x_4324_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
else
{
lean_object* v_one_4332_; lean_object* v_n_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4337_; 
v_one_4332_ = lean_unsigned_to_nat(1u);
v_n_4333_ = lean_nat_sub(v_val_4322_, v_one_4332_);
lean_dec(v_val_4322_);
v___x_4334_ = lean_nat_add(v_n_4333_, v_one_4332_);
lean_dec(v_n_4333_);
v___x_4335_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4334_);
if (v_isShared_4325_ == 0)
{
lean_ctor_set_tag(v___x_4324_, 2);
lean_ctor_set(v___x_4324_, 0, v___x_4335_);
v___x_4337_ = v___x_4324_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Std_CloseableChannel_new___redArg(v_capacity_4340_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4343_, lean_object* v_capacity_4344_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l_Std_CloseableChannel_new___redArg(v_capacity_4344_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4347_, lean_object* v_capacity_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Std_CloseableChannel_new(v_00_u03b1_4347_, v_capacity_4348_);
return v_res_4350_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4351_, lean_object* v_v_4352_){
_start:
{
switch(lean_obj_tag(v_ch_4351_))
{
case 0:
{
lean_object* v_ch_4354_; uint8_t v___x_4355_; 
v_ch_4354_ = lean_ctor_get(v_ch_4351_, 0);
lean_inc_ref(v_ch_4354_);
lean_dec_ref(v_ch_4351_);
v___x_4355_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4354_, v_v_4352_);
return v___x_4355_;
}
case 1:
{
lean_object* v_ch_4356_; uint8_t v___x_4357_; 
v_ch_4356_ = lean_ctor_get(v_ch_4351_, 0);
lean_inc_ref(v_ch_4356_);
lean_dec_ref(v_ch_4351_);
v___x_4357_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4356_, v_v_4352_);
return v___x_4357_;
}
default: 
{
lean_object* v_ch_4358_; uint8_t v___x_4359_; 
v_ch_4358_ = lean_ctor_get(v_ch_4351_, 0);
lean_inc_ref(v_ch_4358_);
lean_dec_ref(v_ch_4351_);
v___x_4359_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4358_, v_v_4352_);
return v___x_4359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4360_, lean_object* v_v_4361_, lean_object* v_a_4362_){
_start:
{
uint8_t v_res_4363_; lean_object* v_r_4364_; 
v_res_4363_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4360_, v_v_4361_);
v_r_4364_ = lean_box(v_res_4363_);
return v_r_4364_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4365_, lean_object* v_ch_4366_, lean_object* v_v_4367_){
_start:
{
uint8_t v___x_4369_; 
v___x_4369_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4366_, v_v_4367_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4370_, lean_object* v_ch_4371_, lean_object* v_v_4372_, lean_object* v_a_4373_){
_start:
{
uint8_t v_res_4374_; lean_object* v_r_4375_; 
v_res_4374_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4370_, v_ch_4371_, v_v_4372_);
v_r_4375_ = lean_box(v_res_4374_);
return v_r_4375_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4376_, lean_object* v_v_4377_){
_start:
{
switch(lean_obj_tag(v_ch_4376_))
{
case 0:
{
lean_object* v_ch_4379_; lean_object* v___x_4380_; 
v_ch_4379_ = lean_ctor_get(v_ch_4376_, 0);
lean_inc_ref(v_ch_4379_);
lean_dec_ref(v_ch_4376_);
v___x_4380_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4379_, v_v_4377_);
return v___x_4380_;
}
case 1:
{
lean_object* v_ch_4381_; lean_object* v___x_4382_; 
v_ch_4381_ = lean_ctor_get(v_ch_4376_, 0);
lean_inc_ref(v_ch_4381_);
lean_dec_ref(v_ch_4376_);
v___x_4382_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4381_, v_v_4377_);
return v___x_4382_;
}
default: 
{
lean_object* v_ch_4383_; lean_object* v___x_4384_; 
v_ch_4383_ = lean_ctor_get(v_ch_4376_, 0);
lean_inc_ref(v_ch_4383_);
lean_dec_ref(v_ch_4376_);
v___x_4384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4383_, v_v_4377_);
return v___x_4384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4385_, lean_object* v_v_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Std_CloseableChannel_send___redArg(v_ch_4385_, v_v_4386_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4389_, lean_object* v_ch_4390_, lean_object* v_v_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_Std_CloseableChannel_send___redArg(v_ch_4390_, v_v_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4394_, lean_object* v_ch_4395_, lean_object* v_v_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Std_CloseableChannel_send(v_00_u03b1_4394_, v_ch_4395_, v_v_4396_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4399_){
_start:
{
switch(lean_obj_tag(v_ch_4399_))
{
case 0:
{
lean_object* v_ch_4401_; lean_object* v___x_4402_; 
v_ch_4401_ = lean_ctor_get(v_ch_4399_, 0);
lean_inc_ref(v_ch_4401_);
lean_dec_ref(v_ch_4399_);
v___x_4402_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4401_);
return v___x_4402_;
}
case 1:
{
lean_object* v_ch_4403_; lean_object* v___x_4404_; 
v_ch_4403_ = lean_ctor_get(v_ch_4399_, 0);
lean_inc_ref(v_ch_4403_);
lean_dec_ref(v_ch_4399_);
v___x_4404_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4403_);
return v___x_4404_;
}
default: 
{
lean_object* v_ch_4405_; lean_object* v___x_4406_; 
v_ch_4405_ = lean_ctor_get(v_ch_4399_, 0);
lean_inc_ref(v_ch_4405_);
lean_dec_ref(v_ch_4399_);
v___x_4406_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4405_);
return v___x_4406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Std_CloseableChannel_close___redArg(v_ch_4407_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4410_, lean_object* v_ch_4411_){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = l_Std_CloseableChannel_close___redArg(v_ch_4411_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4414_, lean_object* v_ch_4415_, lean_object* v_a_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l_Std_CloseableChannel_close(v_00_u03b1_4414_, v_ch_4415_);
return v_res_4417_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4418_){
_start:
{
switch(lean_obj_tag(v_ch_4418_))
{
case 0:
{
lean_object* v_ch_4420_; uint8_t v___x_4421_; 
v_ch_4420_ = lean_ctor_get(v_ch_4418_, 0);
lean_inc_ref(v_ch_4420_);
lean_dec_ref(v_ch_4418_);
v___x_4421_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4420_);
return v___x_4421_;
}
case 1:
{
lean_object* v_ch_4422_; uint8_t v___x_4423_; 
v_ch_4422_ = lean_ctor_get(v_ch_4418_, 0);
lean_inc_ref(v_ch_4422_);
lean_dec_ref(v_ch_4418_);
v___x_4423_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4422_);
return v___x_4423_;
}
default: 
{
lean_object* v_ch_4424_; uint8_t v___x_4425_; 
v_ch_4424_ = lean_ctor_get(v_ch_4418_, 0);
lean_inc_ref(v_ch_4424_);
lean_dec_ref(v_ch_4418_);
v___x_4425_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4424_);
return v___x_4425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4426_, lean_object* v_a_4427_){
_start:
{
uint8_t v_res_4428_; lean_object* v_r_4429_; 
v_res_4428_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4426_);
v_r_4429_ = lean_box(v_res_4428_);
return v_r_4429_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4430_, lean_object* v_ch_4431_){
_start:
{
uint8_t v___x_4433_; 
v___x_4433_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4431_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4434_, lean_object* v_ch_4435_, lean_object* v_a_4436_){
_start:
{
uint8_t v_res_4437_; lean_object* v_r_4438_; 
v_res_4437_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4434_, v_ch_4435_);
v_r_4438_ = lean_box(v_res_4437_);
return v_r_4438_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4439_){
_start:
{
switch(lean_obj_tag(v_ch_4439_))
{
case 0:
{
lean_object* v_ch_4441_; lean_object* v___x_4442_; 
v_ch_4441_ = lean_ctor_get(v_ch_4439_, 0);
lean_inc_ref(v_ch_4441_);
lean_dec_ref(v_ch_4439_);
v___x_4442_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4441_);
return v___x_4442_;
}
case 1:
{
lean_object* v_ch_4443_; lean_object* v___x_4444_; 
v_ch_4443_ = lean_ctor_get(v_ch_4439_, 0);
lean_inc_ref(v_ch_4443_);
lean_dec_ref(v_ch_4439_);
v___x_4444_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4443_);
return v___x_4444_;
}
default: 
{
lean_object* v_ch_4445_; lean_object* v___x_4446_; 
v_ch_4445_ = lean_ctor_get(v_ch_4439_, 0);
lean_inc_ref(v_ch_4445_);
lean_dec_ref(v_ch_4439_);
v___x_4446_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4445_);
return v___x_4446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4447_, lean_object* v_a_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4447_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4450_, lean_object* v_ch_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4454_, lean_object* v_ch_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4454_, v_ch_4455_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4458_){
_start:
{
switch(lean_obj_tag(v_ch_4458_))
{
case 0:
{
lean_object* v_ch_4460_; lean_object* v___x_4461_; 
v_ch_4460_ = lean_ctor_get(v_ch_4458_, 0);
lean_inc_ref(v_ch_4460_);
lean_dec_ref(v_ch_4458_);
v___x_4461_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4460_);
return v___x_4461_;
}
case 1:
{
lean_object* v_ch_4462_; lean_object* v___x_4463_; 
v_ch_4462_ = lean_ctor_get(v_ch_4458_, 0);
lean_inc_ref(v_ch_4462_);
lean_dec_ref(v_ch_4458_);
v___x_4463_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4462_);
return v___x_4463_;
}
default: 
{
lean_object* v_ch_4464_; lean_object* v___x_4465_; 
v_ch_4464_ = lean_ctor_get(v_ch_4458_, 0);
lean_inc_ref(v_ch_4464_);
lean_dec_ref(v_ch_4458_);
v___x_4465_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4464_);
return v___x_4465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4466_, lean_object* v_a_4467_){
_start:
{
lean_object* v_res_4468_; 
v_res_4468_ = l_Std_CloseableChannel_recv___redArg(v_ch_4466_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4469_, lean_object* v_ch_4470_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Std_CloseableChannel_recv___redArg(v_ch_4470_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4473_, lean_object* v_ch_4474_, lean_object* v_a_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l_Std_CloseableChannel_recv(v_00_u03b1_4473_, v_ch_4474_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4477_){
_start:
{
switch(lean_obj_tag(v_ch_4477_))
{
case 0:
{
lean_object* v_ch_4478_; lean_object* v___x_4479_; 
v_ch_4478_ = lean_ctor_get(v_ch_4477_, 0);
lean_inc_ref(v_ch_4478_);
lean_dec_ref(v_ch_4477_);
v___x_4479_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4478_);
return v___x_4479_;
}
case 1:
{
lean_object* v_ch_4480_; lean_object* v___x_4481_; 
v_ch_4480_ = lean_ctor_get(v_ch_4477_, 0);
lean_inc_ref(v_ch_4480_);
lean_dec_ref(v_ch_4477_);
v___x_4481_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4480_);
return v___x_4481_;
}
default: 
{
lean_object* v_ch_4482_; lean_object* v___x_4483_; 
v_ch_4482_ = lean_ctor_get(v_ch_4477_, 0);
lean_inc_ref(v_ch_4482_);
lean_dec_ref(v_ch_4477_);
v___x_4483_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4482_);
return v___x_4483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4484_, lean_object* v_ch_4485_){
_start:
{
lean_object* v___x_4486_; 
v___x_4486_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4485_);
return v___x_4486_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = lean_box(0);
v___x_4488_ = lean_task_pure(v___x_4487_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4489_, lean_object* v_ch_4490_, lean_object* v_prio_4491_, lean_object* v_x_4492_){
_start:
{
if (lean_obj_tag(v_x_4492_) == 0)
{
lean_object* v___x_4494_; 
lean_dec(v_prio_4491_);
lean_dec_ref(v_ch_4490_);
lean_dec_ref(v_f_4489_);
v___x_4494_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4494_;
}
else
{
lean_object* v_val_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v_val_4495_ = lean_ctor_get(v_x_4492_, 0);
lean_inc(v_val_4495_);
lean_dec_ref(v_x_4492_);
lean_inc_ref(v_f_4489_);
v___x_4496_ = lean_apply_2(v_f_4489_, v_val_4495_, lean_box(0));
v___x_4497_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4489_, v_ch_4490_, v_prio_4491_);
return v___x_4497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4498_, lean_object* v_ch_4499_, lean_object* v_prio_4500_, lean_object* v_x_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4498_, v_ch_4499_, v_prio_4500_, v_x_4501_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4504_, lean_object* v_ch_4505_, lean_object* v_prio_4506_){
_start:
{
lean_object* v___x_4508_; lean_object* v___f_4509_; uint8_t v___x_4510_; lean_object* v___x_4511_; 
lean_inc_ref(v_ch_4505_);
v___x_4508_ = l_Std_CloseableChannel_recv___redArg(v_ch_4505_);
lean_inc(v_prio_4506_);
v___f_4509_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4509_, 0, v_f_4504_);
lean_closure_set(v___f_4509_, 1, v_ch_4505_);
lean_closure_set(v___f_4509_, 2, v_prio_4506_);
v___x_4510_ = 0;
v___x_4511_ = lean_io_bind_task(v___x_4508_, v___f_4509_, v_prio_4506_, v___x_4510_);
return v___x_4511_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4512_, lean_object* v_ch_4513_, lean_object* v_prio_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4512_, v_ch_4513_, v_prio_4514_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4517_, lean_object* v_f_4518_, lean_object* v_ch_4519_, lean_object* v_prio_4520_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4518_, v_ch_4519_, v_prio_4520_);
return v___x_4522_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4523_, lean_object* v_f_4524_, lean_object* v_ch_4525_, lean_object* v_prio_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4523_, v_f_4524_, v_ch_4525_, v_prio_4526_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(lean_object* v_x_4529_){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = lean_box(0);
v___x_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4532_, 0, v___x_4531_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed(lean_object* v_x_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(v_x_4533_);
lean_dec_ref(v_x_4533_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4541_, lean_object* v_inst_4542_){
_start:
{
lean_object* v___x_4543_; 
v___x_4543_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4544_, lean_object* v_inst_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4544_, v_inst_4545_);
lean_dec(v_inst_4545_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_4547_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4548_, 0, v_a_4547_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_4549_, lean_object* v_x_4550_){
_start:
{
if (lean_obj_tag(v_x_4550_) == 0)
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4560_; 
lean_dec_ref(v___f_4549_);
v_a_4552_ = lean_ctor_get(v_x_4550_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v_x_4550_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4554_ = v_x_4550_;
v_isShared_4555_ = v_isSharedCheck_4560_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v_x_4550_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4560_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
lean_object* v___x_4558_; 
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
return v___x_4558_;
}
}
}
else
{
lean_object* v_a_4561_; 
v_a_4561_ = lean_ctor_get(v_x_4550_, 0);
lean_inc(v_a_4561_);
lean_dec_ref(v_x_4550_);
if (lean_obj_tag(v_a_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4570_; 
lean_dec_ref(v___f_4549_);
v_a_4562_ = lean_ctor_get(v_a_4561_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v_a_4561_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4564_ = v_a_4561_;
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v_a_4561_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
lean_object* v___x_4568_; 
v___x_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4567_);
return v___x_4568_;
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4572_; uint8_t v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v_a_4571_ = lean_ctor_get(v_a_4561_, 0);
lean_inc(v_a_4571_);
lean_dec_ref(v_a_4561_);
v___x_4572_ = lean_unsigned_to_nat(0u);
v___x_4573_ = 0;
v___x_4574_ = lean_task_map(v___f_4549_, v_a_4571_, v___x_4572_, v___x_4573_);
v___x_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4574_);
return v___x_4575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_4576_, lean_object* v_x_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(v___f_4576_, v_x_4577_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_4580_, lean_object* v_receiver_4581_){
_start:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; uint8_t v___x_4588_; lean_object* v___x_4589_; 
v___x_4583_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4581_);
v___x_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
v___x_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
v___x_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
v___x_4587_ = lean_unsigned_to_nat(0u);
v___x_4588_ = 0;
v___x_4589_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4587_, v___x_4588_, v___x_4586_, v___f_4580_);
return v___x_4589_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_4590_, lean_object* v_receiver_4591_, lean_object* v___y_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(v___f_4590_, v_receiver_4591_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4599_, lean_object* v_inst_4600_){
_start:
{
lean_object* v___f_4601_; 
v___f_4601_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2));
return v___f_4601_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4602_, lean_object* v_inst_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4602_, v_inst_4603_);
lean_dec(v_inst_4603_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_4606_, lean_object* v_x_4607_){
_start:
{
if (lean_obj_tag(v_x_4607_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4617_; 
lean_dec_ref(v___f_4606_);
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
lean_object* v_a_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v_a_4618_ = lean_ctor_get(v_x_4607_, 0);
lean_inc(v_a_4618_);
lean_dec_ref(v_x_4607_);
v___x_4619_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0));
v___x_4620_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4620_, 0, lean_box(0));
lean_closure_set(v___x_4620_, 1, lean_box(0));
lean_closure_set(v___x_4620_, 2, lean_box(0));
lean_closure_set(v___x_4620_, 3, v___x_4619_);
lean_closure_set(v___x_4620_, 4, v___f_4606_);
v___x_4621_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4621_, 0, lean_box(0));
lean_closure_set(v___x_4621_, 1, lean_box(0));
lean_closure_set(v___x_4621_, 2, lean_box(0));
lean_closure_set(v___x_4621_, 3, v___x_4620_);
v___x_4622_ = lean_unsigned_to_nat(0u);
v___x_4623_ = 0;
v___x_4624_ = lean_task_map(v___x_4621_, v_a_4618_, v___x_4622_, v___x_4623_);
v___x_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4624_);
return v___x_4625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_4626_, lean_object* v_x_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(v___f_4626_, v_x_4627_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_4630_, lean_object* v_receiver_4631_, lean_object* v_x_4632_){
_start:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; lean_object* v___x_4639_; 
v___x_4634_ = l_Std_CloseableChannel_send___redArg(v_receiver_4631_, v_x_4632_);
v___x_4635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
v___x_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4635_);
v___x_4637_ = lean_unsigned_to_nat(0u);
v___x_4638_ = 0;
v___x_4639_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4637_, v___x_4638_, v___x_4636_, v___f_4630_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_4640_, lean_object* v_receiver_4641_, lean_object* v_x_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(v___f_4640_, v_receiver_4641_, v_x_4642_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(lean_object* v_x_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v_x_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(v_x_4648_);
lean_dec_ref(v_x_4648_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(lean_object* v___f_4651_, lean_object* v_socket_4652_, lean_object* v_x_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v___x_4656_; 
v___x_4656_ = lean_apply_3(v___f_4651_, v_socket_4652_, v___y_4654_, lean_box(0));
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v___f_4657_, lean_object* v_socket_4658_, lean_object* v_x_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(v___f_4657_, v_socket_4658_, v_x_4659_, v___y_4660_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_4663_, lean_object* v___x_4664_, lean_object* v_socket_4665_, lean_object* v_data_4666_){
_start:
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4668_ = lean_unsigned_to_nat(0u);
v___x_4669_ = lean_array_get_size(v_data_4666_);
v___x_4670_ = lean_box(0);
v___x_4671_ = lean_nat_dec_lt(v___x_4668_, v___x_4669_);
if (v___x_4671_ == 0)
{
lean_object* v___x_4672_; 
lean_dec_ref(v_data_4666_);
lean_dec_ref(v_socket_4665_);
lean_dec_ref(v___x_4664_);
lean_dec_ref(v___f_4663_);
v___x_4672_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4672_;
}
else
{
lean_object* v___f_4673_; uint8_t v___x_4674_; 
v___f_4673_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4673_, 0, v___f_4663_);
lean_closure_set(v___f_4673_, 1, v_socket_4665_);
v___x_4674_ = lean_nat_dec_le(v___x_4669_, v___x_4669_);
if (v___x_4674_ == 0)
{
if (v___x_4671_ == 0)
{
lean_object* v___x_4675_; 
lean_dec_ref(v___f_4673_);
lean_dec_ref(v_data_4666_);
lean_dec_ref(v___x_4664_);
v___x_4675_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1));
return v___x_4675_;
}
else
{
size_t v___x_4676_; size_t v___x_4677_; lean_object* v___x_753__overap_4678_; lean_object* v___x_4679_; 
v___x_4676_ = ((size_t)0ULL);
v___x_4677_ = lean_usize_of_nat(v___x_4669_);
v___x_753__overap_4678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4664_, v___f_4673_, v_data_4666_, v___x_4676_, v___x_4677_, v___x_4670_);
v___x_4679_ = lean_apply_1(v___x_753__overap_4678_, lean_box(0));
return v___x_4679_;
}
}
else
{
size_t v___x_4680_; size_t v___x_4681_; lean_object* v___x_756__overap_4682_; lean_object* v___x_4683_; 
v___x_4680_ = ((size_t)0ULL);
v___x_4681_ = lean_usize_of_nat(v___x_4669_);
v___x_756__overap_4682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4664_, v___f_4673_, v_data_4666_, v___x_4680_, v___x_4681_, v___x_4670_);
v___x_4683_ = lean_apply_1(v___x_756__overap_4682_, lean_box(0));
return v___x_4683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_4684_, lean_object* v___x_4685_, lean_object* v_socket_4686_, lean_object* v_data_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(v___f_4684_, v___x_4685_, v_socket_4686_, v_data_4687_);
return v_res_4689_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_4695_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_4696_; lean_object* v___f_4697_; lean_object* v___f_4698_; 
v___x_4696_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_4697_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___f_4698_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4698_, 0, v___f_4697_);
lean_closure_set(v___f_4698_, 1, v___x_4696_);
return v___f_4698_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___f_4699_; lean_object* v___f_4700_; lean_object* v___f_4701_; lean_object* v___x_4702_; 
v___f_4699_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_4700_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4);
v___f_4701_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1));
v___x_4702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4702_, 0, v___f_4701_);
lean_ctor_set(v___x_4702_, 1, v___f_4700_);
lean_ctor_set(v___x_4702_, 2, v___f_4699_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4703_, lean_object* v_inst_4704_){
_start:
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4706_, lean_object* v_inst_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4706_, v_inst_4707_);
lean_dec(v_inst_4707_);
return v_res_4708_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4709_){
_start:
{
lean_inc_ref(v_ch_4709_);
return v_ch_4709_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_Std_CloseableChannel_sync___redArg(v_ch_4710_);
lean_dec_ref(v_ch_4710_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4712_, lean_object* v_ch_4713_){
_start:
{
lean_inc_ref(v_ch_4713_);
return v_ch_4713_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4714_, lean_object* v_ch_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Std_CloseableChannel_sync(v_00_u03b1_4714_, v_ch_4715_);
lean_dec_ref(v_ch_4715_);
return v_res_4716_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4717_){
_start:
{
lean_object* v___x_4719_; 
v___x_4719_ = l_Std_CloseableChannel_new___redArg(v_capacity_4717_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4720_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4723_, lean_object* v_capacity_4724_){
_start:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Std_CloseableChannel_new___redArg(v_capacity_4724_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4727_, lean_object* v_capacity_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4727_, v_capacity_4728_);
return v_res_4730_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4731_, lean_object* v_v_4732_){
_start:
{
uint8_t v___x_4734_; 
v___x_4734_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4731_, v_v_4732_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4735_, lean_object* v_v_4736_, lean_object* v_a_4737_){
_start:
{
uint8_t v_res_4738_; lean_object* v_r_4739_; 
v_res_4738_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4735_, v_v_4736_);
v_r_4739_ = lean_box(v_res_4738_);
return v_r_4739_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4740_, lean_object* v_ch_4741_, lean_object* v_v_4742_){
_start:
{
uint8_t v___x_4744_; 
v___x_4744_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4741_, v_v_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4745_, lean_object* v_ch_4746_, lean_object* v_v_4747_, lean_object* v_a_4748_){
_start:
{
uint8_t v_res_4749_; lean_object* v_r_4750_; 
v_res_4749_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4745_, v_ch_4746_, v_v_4747_);
v_r_4750_ = lean_box(v_res_4749_);
return v_r_4750_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4751_, lean_object* v_v_4752_){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = l_Std_CloseableChannel_send___redArg(v_ch_4751_, v_v_4752_);
v___x_4755_ = lean_io_wait(v___x_4754_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4755_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4755_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
lean_ctor_set_tag(v___x_4758_, 1);
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
v_a_4764_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4755_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4755_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
lean_ctor_set_tag(v___x_4766_, 0);
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_4772_, lean_object* v_v_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4772_, v_v_4773_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_4776_, lean_object* v_ch_4777_, lean_object* v_v_4778_){
_start:
{
lean_object* v___x_4780_; 
v___x_4780_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4777_, v_v_4778_);
return v___x_4780_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_4781_, lean_object* v_ch_4782_, lean_object* v_v_4783_, lean_object* v_a_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_4781_, v_ch_4782_, v_v_4783_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_4786_){
_start:
{
lean_object* v___x_4788_; 
v___x_4788_ = l_Std_CloseableChannel_close___redArg(v_ch_4786_);
return v___x_4788_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_4789_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_4792_, lean_object* v_ch_4793_){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Std_CloseableChannel_close___redArg(v_ch_4793_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_4796_, lean_object* v_ch_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_4796_, v_ch_4797_);
return v_res_4799_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_4800_){
_start:
{
uint8_t v___x_4802_; 
v___x_4802_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4800_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_4803_, lean_object* v_a_4804_){
_start:
{
uint8_t v_res_4805_; lean_object* v_r_4806_; 
v_res_4805_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_4803_);
v_r_4806_ = lean_box(v_res_4805_);
return v_r_4806_;
}
}
LEAN_EXPORT uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_4807_, lean_object* v_ch_4808_){
_start:
{
uint8_t v___x_4810_; 
v___x_4810_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4808_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_4811_, lean_object* v_ch_4812_, lean_object* v_a_4813_){
_start:
{
uint8_t v_res_4814_; lean_object* v_r_4815_; 
v_res_4814_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_4811_, v_ch_4812_);
v_r_4815_ = lean_box(v_res_4814_);
return v_r_4815_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_4816_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4816_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_4819_, lean_object* v_a_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_4819_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_4822_, lean_object* v_ch_4823_){
_start:
{
lean_object* v___x_4825_; 
v___x_4825_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4823_);
return v___x_4825_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_4826_, lean_object* v_ch_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_4826_, v_ch_4827_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_4830_){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4832_ = l_Std_CloseableChannel_recv___redArg(v_ch_4830_);
v___x_4833_ = lean_io_wait(v___x_4832_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_4834_, lean_object* v_a_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4834_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_4837_, lean_object* v_ch_4838_){
_start:
{
lean_object* v___x_4840_; 
v___x_4840_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_4838_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_4841_, lean_object* v_ch_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_4841_, v_ch_4842_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_4845_, lean_object* v_b_4846_, lean_object* v_f_4847_, lean_object* v_toBind_4848_, lean_object* v___f_4849_, lean_object* v_____do__lift_4850_){
_start:
{
if (lean_obj_tag(v_____do__lift_4850_) == 0)
{
lean_object* v___x_4851_; 
lean_dec(v___f_4849_);
lean_dec(v_toBind_4848_);
lean_dec(v_f_4847_);
v___x_4851_ = lean_apply_2(v_toPure_4845_, lean_box(0), v_b_4846_);
return v___x_4851_;
}
else
{
lean_object* v_val_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
lean_dec(v_toPure_4845_);
v_val_4852_ = lean_ctor_get(v_____do__lift_4850_, 0);
lean_inc(v_val_4852_);
lean_dec_ref(v_____do__lift_4850_);
v___x_4853_ = lean_apply_2(v_f_4847_, v_val_4852_, v_b_4846_);
v___x_4854_ = lean_apply_4(v_toBind_4848_, lean_box(0), lean_box(0), v___x_4853_, v___f_4849_);
return v___x_4854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_4855_, lean_object* v_inst_4856_, lean_object* v_ch_4857_, lean_object* v_f_4858_, lean_object* v_b_4859_){
_start:
{
lean_object* v_toApplicative_4860_; lean_object* v_toBind_4861_; lean_object* v_toPure_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___f_4865_; lean_object* v___f_4866_; lean_object* v___x_4867_; 
v_toApplicative_4860_ = lean_ctor_get(v_inst_4855_, 0);
v_toBind_4861_ = lean_ctor_get(v_inst_4855_, 1);
lean_inc_n(v_toBind_4861_, 2);
v_toPure_4862_ = lean_ctor_get(v_toApplicative_4860_, 1);
lean_inc_n(v_toPure_4862_, 2);
lean_inc_ref(v_ch_4857_);
v___x_4863_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_4863_, 0, lean_box(0));
lean_closure_set(v___x_4863_, 1, v_ch_4857_);
lean_inc(v_inst_4856_);
v___x_4864_ = lean_apply_2(v_inst_4856_, lean_box(0), v___x_4863_);
lean_inc(v_f_4858_);
v___f_4865_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4865_, 0, v_toPure_4862_);
lean_closure_set(v___f_4865_, 1, v_inst_4855_);
lean_closure_set(v___f_4865_, 2, v_inst_4856_);
lean_closure_set(v___f_4865_, 3, v_ch_4857_);
lean_closure_set(v___f_4865_, 4, v_f_4858_);
v___f_4866_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_4866_, 0, v_toPure_4862_);
lean_closure_set(v___f_4866_, 1, v_b_4859_);
lean_closure_set(v___f_4866_, 2, v_f_4858_);
lean_closure_set(v___f_4866_, 3, v_toBind_4861_);
lean_closure_set(v___f_4866_, 4, v___f_4865_);
v___x_4867_ = lean_apply_4(v_toBind_4861_, lean_box(0), lean_box(0), v___x_4864_, v___f_4866_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_4868_, lean_object* v_inst_4869_, lean_object* v_inst_4870_, lean_object* v_ch_4871_, lean_object* v_f_4872_, lean_object* v_____do__lift_4873_){
_start:
{
if (lean_obj_tag(v_____do__lift_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4875_; 
lean_dec(v_f_4872_);
lean_dec_ref(v_ch_4871_);
lean_dec(v_inst_4870_);
lean_dec_ref(v_inst_4869_);
v_a_4874_ = lean_ctor_get(v_____do__lift_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref(v_____do__lift_4873_);
v___x_4875_ = lean_apply_2(v_toPure_4868_, lean_box(0), v_a_4874_);
return v___x_4875_;
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4877_; 
lean_dec(v_toPure_4868_);
v_a_4876_ = lean_ctor_get(v_____do__lift_4873_, 0);
lean_inc(v_a_4876_);
lean_dec_ref(v_____do__lift_4873_);
v___x_4877_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4869_, v_inst_4870_, v_ch_4871_, v_f_4872_, v_a_4876_);
return v___x_4877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_4878_, lean_object* v_00_u03b1_4879_, lean_object* v_00_u03b2_4880_, lean_object* v_inst_4881_, lean_object* v_inst_4882_, lean_object* v_ch_4883_, lean_object* v_f_4884_, lean_object* v_b_4885_){
_start:
{
lean_object* v___x_4886_; 
v___x_4886_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4881_, v_inst_4882_, v_ch_4883_, v_f_4884_, v_b_4885_);
return v___x_4886_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_4887_, lean_object* v_inst_4888_, lean_object* v_ch_4889_, lean_object* v_b_4890_, lean_object* v_f_4891_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4887_, v_inst_4888_, v_ch_4889_, v_f_4891_, v_b_4890_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_4893_, lean_object* v_00_u03b1_4894_, lean_object* v_inst_4895_, lean_object* v_inst_4896_, lean_object* v_00_u03b2_4897_, lean_object* v_ch_4898_, lean_object* v_b_4899_, lean_object* v_f_4900_){
_start:
{
lean_object* v___x_4901_; 
v___x_4901_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4895_, v_inst_4896_, v_ch_4898_, v_f_4900_, v_b_4899_);
return v___x_4901_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_4902_, lean_object* v_inst_4903_, lean_object* v_00_u03b2_4904_, lean_object* v_ch_4905_, lean_object* v_b_4906_, lean_object* v_f_4907_){
_start:
{
lean_object* v___x_4908_; 
v___x_4908_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_4902_, v_inst_4903_, v_ch_4905_, v_f_4907_, v_b_4906_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_4909_, lean_object* v_inst_4910_){
_start:
{
lean_object* v___f_4911_; 
v___f_4911_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4911_, 0, v_inst_4909_);
lean_closure_set(v___f_4911_, 1, v_inst_4910_);
return v___f_4911_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_4912_, lean_object* v_00_u03b1_4913_, lean_object* v_inst_4914_, lean_object* v_inst_4915_){
_start:
{
lean_object* v___f_4916_; 
v___f_4916_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_4916_, 0, v_inst_4914_);
lean_closure_set(v___f_4916_, 1, v_inst_4915_);
return v___f_4916_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_4917_){
_start:
{
lean_object* v___x_4919_; 
v___x_4919_ = l_Std_CloseableChannel_new___redArg(v_capacity_4917_);
return v___x_4919_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Std_Channel_new___redArg(v_capacity_4920_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_4923_, lean_object* v_capacity_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l_Std_CloseableChannel_new___redArg(v_capacity_4924_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_4927_, lean_object* v_capacity_4928_, lean_object* v_a_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Std_Channel_new(v_00_u03b1_4927_, v_capacity_4928_);
return v_res_4930_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_4931_, lean_object* v_v_4932_){
_start:
{
uint8_t v___x_4934_; 
v___x_4934_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4931_, v_v_4932_);
return v___x_4934_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_4935_, lean_object* v_v_4936_, lean_object* v_a_4937_){
_start:
{
uint8_t v_res_4938_; lean_object* v_r_4939_; 
v_res_4938_ = l_Std_Channel_trySend___redArg(v_ch_4935_, v_v_4936_);
v_r_4939_ = lean_box(v_res_4938_);
return v_r_4939_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_4940_, lean_object* v_ch_4941_, lean_object* v_v_4942_){
_start:
{
uint8_t v___x_4944_; 
v___x_4944_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4941_, v_v_4942_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_4945_, lean_object* v_ch_4946_, lean_object* v_v_4947_, lean_object* v_a_4948_){
_start:
{
uint8_t v_res_4949_; lean_object* v_r_4950_; 
v_res_4949_ = l_Std_Channel_trySend(v_00_u03b1_4945_, v_ch_4946_, v_v_4947_);
v_r_4950_ = lean_box(v_res_4949_);
return v_r_4950_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4951_ = lean_box(0);
v___x_4952_ = lean_task_pure(v___x_4951_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_4953_){
_start:
{
lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_142__overap_4958_; lean_object* v___x_4959_; 
v___x_4955_ = l_instMonadBaseIO;
v___x_4956_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_4957_ = l_instInhabitedOfMonad___redArg(v___x_4955_, v___x_4956_);
v___x_142__overap_4958_ = lean_panic_fn_borrowed(v___x_4957_, v_msg_4953_);
lean_dec(v___x_4957_);
v___x_4959_ = lean_apply_1(v___x_142__overap_4958_, lean_box(0));
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_4960_, lean_object* v___y_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_4960_);
return v_res_4962_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4966_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_4967_ = lean_unsigned_to_nat(21u);
v___x_4968_ = lean_unsigned_to_nat(869u);
v___x_4969_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_4970_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_4971_ = l_mkPanicMessageWithDecl(v___x_4970_, v___x_4969_, v___x_4968_, v___x_4967_, v___x_4966_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_4972_){
_start:
{
if (lean_obj_tag(v_x_4972_) == 0)
{
lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4974_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_4975_ = l_panic___at___00Std_Channel_send_spec__0(v___x_4974_);
return v___x_4975_;
}
else
{
lean_object* v___x_4976_; 
v___x_4976_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4976_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_4977_, lean_object* v___y_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l_Std_Channel_send___redArg___lam__0(v_x_4977_);
lean_dec_ref(v_x_4977_);
return v_res_4979_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_4981_, lean_object* v_v_4982_){
_start:
{
lean_object* v___x_4984_; lean_object* v___f_4985_; lean_object* v___x_4986_; uint8_t v___x_4987_; lean_object* v___x_4988_; 
v___x_4984_ = l_Std_CloseableChannel_send___redArg(v_ch_4981_, v_v_4982_);
v___f_4985_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_4986_ = lean_unsigned_to_nat(0u);
v___x_4987_ = 1;
v___x_4988_ = lean_io_bind_task(v___x_4984_, v___f_4985_, v___x_4986_, v___x_4987_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_4989_, lean_object* v_v_4990_, lean_object* v_a_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Std_Channel_send___redArg(v_ch_4989_, v_v_4990_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_4993_, lean_object* v_ch_4994_, lean_object* v_v_4995_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l_Std_Channel_send___redArg(v_ch_4994_, v_v_4995_);
return v___x_4997_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_4998_, lean_object* v_ch_4999_, lean_object* v_v_5000_, lean_object* v_a_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_Std_Channel_send(v_00_u03b1_4998_, v_ch_4999_, v_v_5000_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_5003_){
_start:
{
lean_object* v___x_5005_; 
v___x_5005_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5003_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Std_Channel_tryRecv___redArg(v_ch_5006_);
return v_res_5008_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_5009_, lean_object* v_ch_5010_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5010_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_5013_, lean_object* v_ch_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Std_Channel_tryRecv(v_00_u03b1_5013_, v_ch_5014_);
return v_res_5016_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5018_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_5019_ = lean_unsigned_to_nat(16u);
v___x_5020_ = lean_unsigned_to_nat(880u);
v___x_5021_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_5022_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_5023_ = l_mkPanicMessageWithDecl(v___x_5022_, v___x_5021_, v___x_5020_, v___x_5019_, v___x_5018_);
return v___x_5023_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_5024_, lean_object* v_x_5025_){
_start:
{
if (lean_obj_tag(v_x_5025_) == 0)
{
lean_object* v___x_5027_; lean_object* v___x_140__overap_5028_; lean_object* v___x_5029_; 
v___x_5027_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_140__overap_5028_ = l_panic___redArg(v___x_5024_, v___x_5027_);
v___x_5029_ = lean_apply_1(v___x_140__overap_5028_, lean_box(0));
return v___x_5029_;
}
else
{
lean_object* v_val_5030_; lean_object* v___x_5031_; 
v_val_5030_ = lean_ctor_get(v_x_5025_, 0);
lean_inc(v_val_5030_);
lean_dec_ref(v_x_5025_);
v___x_5031_ = lean_task_pure(v_val_5030_);
return v___x_5031_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_5032_, lean_object* v_x_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l_Std_Channel_recv___redArg___lam__0(v___x_5032_, v_x_5033_);
lean_dec_ref(v___x_5032_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_5036_, lean_object* v_ch_5037_){
_start:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___f_5043_; lean_object* v___x_5044_; uint8_t v___x_5045_; lean_object* v___x_5046_; 
v___x_5039_ = l_instMonadBaseIO;
v___x_5040_ = l_Std_CloseableChannel_recv___redArg(v_ch_5037_);
v___x_5041_ = lean_task_pure(v_inst_5036_);
v___x_5042_ = l_instInhabitedOfMonad___redArg(v___x_5039_, v___x_5041_);
v___f_5043_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5043_, 0, v___x_5042_);
v___x_5044_ = lean_unsigned_to_nat(0u);
v___x_5045_ = 1;
v___x_5046_ = lean_io_bind_task(v___x_5040_, v___f_5043_, v___x_5044_, v___x_5045_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_5047_, lean_object* v_ch_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_Std_Channel_recv___redArg(v_inst_5047_, v_ch_5048_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5051_, lean_object* v_inst_5052_, lean_object* v_ch_5053_){
_start:
{
lean_object* v___x_5055_; 
v___x_5055_ = l_Std_Channel_recv___redArg(v_inst_5052_, v_ch_5053_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5056_, lean_object* v_inst_5057_, lean_object* v_ch_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Std_Channel_recv(v_00_u03b1_5056_, v_inst_5057_, v_ch_5058_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5061_){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5063_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5061_);
v___x_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
v___x_5065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5064_);
return v___x_5065_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5066_, lean_object* v___y_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5066_);
return v_res_5068_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5072_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5073_ = lean_unsigned_to_nat(14u);
v___x_5074_ = lean_unsigned_to_nat(22u);
v___x_5075_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5076_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5077_ = l_mkPanicMessageWithDecl(v___x_5076_, v___x_5075_, v___x_5074_, v___x_5073_, v___x_5072_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5078_, lean_object* v_inst_5079_, lean_object* v_x_5080_){
_start:
{
lean_object* v___y_5083_; lean_object* v___y_5087_; 
if (lean_obj_tag(v_x_5080_) == 0)
{
lean_object* v___x_5089_; lean_object* v___x_5090_; 
v___x_5089_ = lean_box(0);
v___x_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5089_);
return v___x_5090_;
}
else
{
lean_object* v_val_5091_; 
v_val_5091_ = lean_ctor_get(v_x_5080_, 0);
lean_inc(v_val_5091_);
lean_dec_ref(v_x_5080_);
if (lean_obj_tag(v_val_5091_) == 0)
{
lean_object* v_a_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5099_; 
v_a_5092_ = lean_ctor_get(v_val_5091_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v_val_5091_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5094_ = v_val_5091_;
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_a_5092_);
lean_dec(v_val_5091_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5099_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5097_; 
if (v_isShared_5095_ == 0)
{
v___x_5097_ = v___x_5094_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
v___y_5083_ = v___x_5097_;
goto v___jp_5082_;
}
}
}
else
{
lean_object* v_a_5100_; 
v_a_5100_ = lean_ctor_get(v_val_5091_, 0);
lean_inc(v_a_5100_);
lean_dec_ref(v_val_5091_);
if (lean_obj_tag(v_a_5100_) == 0)
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5101_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5102_ = l_panic___redArg(v_inst_5079_, v___x_5101_);
v___y_5087_ = v___x_5102_;
goto v___jp_5086_;
}
else
{
lean_object* v_val_5103_; 
v_val_5103_ = lean_ctor_get(v_a_5100_, 0);
lean_inc(v_val_5103_);
lean_dec_ref(v_a_5100_);
v___y_5087_ = v_val_5103_;
goto v___jp_5086_;
}
}
}
v___jp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = lean_io_promise_resolve(v___y_5083_, v_promise_5078_);
v___x_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5084_);
return v___x_5085_;
}
v___jp_5086_:
{
lean_object* v___x_5088_; 
v___x_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5088_, 0, v___y_5087_);
v___y_5083_ = v___x_5088_;
goto v___jp_5082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5104_, lean_object* v_inst_5105_, lean_object* v_x_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5104_, v_inst_5105_, v_x_5106_);
lean_dec(v_inst_5105_);
lean_dec(v_promise_5104_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5109_, lean_object* v___f_5110_, lean_object* v_x_5111_){
_start:
{
lean_object* v_val_5114_; 
if (lean_obj_tag(v_x_5111_) == 0)
{
lean_object* v___x_5116_; 
lean_dec_ref(v___f_5110_);
v___x_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5116_, 0, v_x_5111_);
return v___x_5116_;
}
else
{
lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5132_; 
v_isSharedCheck_5132_ = !lean_is_exclusive(v_x_5111_);
if (v_isSharedCheck_5132_ == 0)
{
lean_object* v_unused_5133_; 
v_unused_5133_ = lean_ctor_get(v_x_5111_, 0);
lean_dec(v_unused_5133_);
v___x_5118_ = v_x_5111_;
v_isShared_5119_ = v_isSharedCheck_5132_;
goto v_resetjp_5117_;
}
else
{
lean_dec(v_x_5111_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5132_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; lean_object* v___x_5123_; 
v___x_5120_ = lean_io_promise_result_opt(v_a_5109_);
v___x_5121_ = lean_unsigned_to_nat(0u);
v___x_5122_ = 1;
v___x_5123_ = l_EIO_chainTask___redArg(v___x_5120_, v___f_5110_, v___x_5121_, v___x_5122_);
if (lean_obj_tag(v___x_5123_) == 0)
{
lean_object* v_a_5124_; lean_object* v___x_5126_; 
v_a_5124_ = lean_ctor_get(v___x_5123_, 0);
lean_inc(v_a_5124_);
lean_dec_ref(v___x_5123_);
if (v_isShared_5119_ == 0)
{
lean_ctor_set(v___x_5118_, 0, v_a_5124_);
v___x_5126_ = v___x_5118_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5124_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
v_val_5114_ = v___x_5126_;
goto v___jp_5113_;
}
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5130_; 
v_a_5128_ = lean_ctor_get(v___x_5123_, 0);
lean_inc(v_a_5128_);
lean_dec_ref(v___x_5123_);
if (v_isShared_5119_ == 0)
{
lean_ctor_set_tag(v___x_5118_, 0);
lean_ctor_set(v___x_5118_, 0, v_a_5128_);
v___x_5130_ = v___x_5118_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5128_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
v_val_5114_ = v___x_5130_;
goto v___jp_5113_;
}
}
}
}
v___jp_5113_:
{
lean_object* v___x_5115_; 
v___x_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5115_, 0, v_val_5114_);
return v___x_5115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5134_, lean_object* v___f_5135_, lean_object* v_x_5136_, lean_object* v___y_5137_){
_start:
{
lean_object* v_res_5138_; 
v_res_5138_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5134_, v___f_5135_, v_x_5136_);
lean_dec(v_a_5134_);
return v_res_5138_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5139_, lean_object* v_finished_5140_, lean_object* v___f_5141_, lean_object* v_x_5142_){
_start:
{
if (lean_obj_tag(v_x_5142_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5152_; 
lean_dec_ref(v___f_5141_);
lean_dec(v_finished_5140_);
lean_dec_ref(v_sel_5139_);
v_a_5144_ = lean_ctor_get(v_x_5142_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v_x_5142_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5146_ = v_x_5142_;
v_isShared_5147_ = v_isSharedCheck_5152_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v_x_5142_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5152_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5149_; 
if (v_isShared_5147_ == 0)
{
v___x_5149_ = v___x_5146_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5144_);
v___x_5149_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
lean_object* v___x_5150_; 
v___x_5150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5149_);
return v___x_5150_;
}
}
}
else
{
lean_object* v_a_5153_; lean_object* v_registerFn_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___f_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; lean_object* v___x_5160_; 
v_a_5153_ = lean_ctor_get(v_x_5142_, 0);
lean_inc_n(v_a_5153_, 2);
lean_dec_ref(v_x_5142_);
v_registerFn_5154_ = lean_ctor_get(v_sel_5139_, 1);
lean_inc_ref(v_registerFn_5154_);
lean_dec_ref(v_sel_5139_);
v___x_5155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5155_, 0, v_finished_5140_);
lean_ctor_set(v___x_5155_, 1, v_a_5153_);
v___x_5156_ = lean_apply_2(v_registerFn_5154_, v___x_5155_, lean_box(0));
v___f_5157_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5157_, 0, v_a_5153_);
lean_closure_set(v___f_5157_, 1, v___f_5141_);
v___x_5158_ = lean_unsigned_to_nat(0u);
v___x_5159_ = 0;
v___x_5160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5158_, v___x_5159_, v___x_5156_, v___f_5157_);
return v___x_5160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5161_, lean_object* v_finished_5162_, lean_object* v___f_5163_, lean_object* v_x_5164_, lean_object* v___y_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5161_, v_finished_5162_, v___f_5163_, v_x_5164_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5167_, lean_object* v_sel_5168_, lean_object* v_waiter_5169_){
_start:
{
lean_object* v___x_5171_; lean_object* v_finished_5172_; lean_object* v_promise_5173_; lean_object* v___f_5174_; lean_object* v___f_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; uint8_t v___x_5179_; lean_object* v___x_5180_; 
v___x_5171_ = lean_io_promise_new();
v_finished_5172_ = lean_ctor_get(v_waiter_5169_, 0);
lean_inc(v_finished_5172_);
v_promise_5173_ = lean_ctor_get(v_waiter_5169_, 1);
lean_inc(v_promise_5173_);
lean_dec_ref(v_waiter_5169_);
v___f_5174_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5174_, 0, v_promise_5173_);
lean_closure_set(v___f_5174_, 1, v_inst_5167_);
v___f_5175_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5175_, 0, v_sel_5168_);
lean_closure_set(v___f_5175_, 1, v_finished_5172_);
lean_closure_set(v___f_5175_, 2, v___f_5174_);
v___x_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5176_, 0, v___x_5171_);
v___x_5177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5176_);
v___x_5178_ = lean_unsigned_to_nat(0u);
v___x_5179_ = 0;
v___x_5180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5178_, v___x_5179_, v___x_5177_, v___f_5175_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5181_, lean_object* v_sel_5182_, lean_object* v_waiter_5183_, lean_object* v___y_5184_){
_start:
{
lean_object* v_res_5185_; 
v_res_5185_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5181_, v_sel_5182_, v_waiter_5183_);
return v_res_5185_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5186_, lean_object* v_ch_5187_){
_start:
{
lean_object* v_sel_5188_; lean_object* v_unregisterFn_5189_; lean_object* v___f_5190_; lean_object* v___f_5191_; lean_object* v___x_5192_; 
lean_inc_ref(v_ch_5187_);
v_sel_5188_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5187_);
v_unregisterFn_5189_ = lean_ctor_get(v_sel_5188_, 2);
lean_inc_ref(v_unregisterFn_5189_);
v___f_5190_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5190_, 0, v_ch_5187_);
v___f_5191_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5191_, 0, v_inst_5186_);
lean_closure_set(v___f_5191_, 1, v_sel_5188_);
v___x_5192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5192_, 0, v___f_5190_);
lean_ctor_set(v___x_5192_, 1, v___f_5191_);
lean_ctor_set(v___x_5192_, 2, v_unregisterFn_5189_);
return v___x_5192_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5193_, lean_object* v_inst_5194_, lean_object* v_ch_5195_){
_start:
{
lean_object* v___x_5196_; 
v___x_5196_ = l_Std_Channel_recvSelector___redArg(v_inst_5194_, v_ch_5195_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5197_, lean_object* v_inst_5198_, lean_object* v_ch_5199_, lean_object* v_prio_5200_, lean_object* v_v_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5197_, v_inst_5198_, v_ch_5199_, v_prio_5200_, v_v_5201_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5204_, lean_object* v_f_5205_, lean_object* v_ch_5206_, lean_object* v_prio_5207_){
_start:
{
lean_object* v___x_5209_; lean_object* v___f_5210_; uint8_t v___x_5211_; lean_object* v___x_5212_; 
lean_inc_ref(v_ch_5206_);
lean_inc(v_inst_5204_);
v___x_5209_ = l_Std_Channel_recv___redArg(v_inst_5204_, v_ch_5206_);
lean_inc(v_prio_5207_);
v___f_5210_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5210_, 0, v_f_5205_);
lean_closure_set(v___f_5210_, 1, v_inst_5204_);
lean_closure_set(v___f_5210_, 2, v_ch_5206_);
lean_closure_set(v___f_5210_, 3, v_prio_5207_);
v___x_5211_ = 0;
v___x_5212_ = lean_io_bind_task(v___x_5209_, v___f_5210_, v_prio_5207_, v___x_5211_);
return v___x_5212_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5213_, lean_object* v_inst_5214_, lean_object* v_ch_5215_, lean_object* v_prio_5216_, lean_object* v_v_5217_){
_start:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; 
lean_inc_ref(v_f_5213_);
v___x_5219_ = lean_apply_2(v_f_5213_, v_v_5217_, lean_box(0));
v___x_5220_ = l_Std_Channel_forAsync___redArg(v_inst_5214_, v_f_5213_, v_ch_5215_, v_prio_5216_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5221_, lean_object* v_f_5222_, lean_object* v_ch_5223_, lean_object* v_prio_5224_, lean_object* v_a_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Std_Channel_forAsync___redArg(v_inst_5221_, v_f_5222_, v_ch_5223_, v_prio_5224_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5227_, lean_object* v_inst_5228_, lean_object* v_f_5229_, lean_object* v_ch_5230_, lean_object* v_prio_5231_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Std_Channel_forAsync___redArg(v_inst_5228_, v_f_5229_, v_ch_5230_, v_prio_5231_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5234_, lean_object* v_inst_5235_, lean_object* v_f_5236_, lean_object* v_ch_5237_, lean_object* v_prio_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Std_Channel_forAsync(v_00_u03b1_5234_, v_inst_5235_, v_f_5236_, v_ch_5237_, v_prio_5238_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5241_, lean_object* v_channel_5242_){
_start:
{
lean_object* v___x_5243_; 
v___x_5243_ = l_Std_Channel_recvSelector___redArg(v_inst_5241_, v_channel_5242_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5244_){
_start:
{
lean_object* v___f_5245_; lean_object* v___f_5246_; lean_object* v___x_5247_; 
v___f_5245_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5245_, 0, v_inst_5244_);
v___f_5246_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1));
v___x_5247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5247_, 0, v___f_5245_);
lean_ctor_set(v___x_5247_, 1, v___f_5246_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5248_, lean_object* v_inst_5249_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5249_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5251_){
_start:
{
lean_object* v___x_5252_; 
v___x_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5252_, 0, v_a_5251_);
return v___x_5252_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5253_, lean_object* v_x_5254_){
_start:
{
if (lean_obj_tag(v_x_5254_) == 0)
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5264_; 
lean_dec_ref(v___f_5253_);
v_a_5256_ = lean_ctor_get(v_x_5254_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v_x_5254_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5258_ = v_x_5254_;
v_isShared_5259_ = v_isSharedCheck_5264_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v_x_5254_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5264_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5261_; 
if (v_isShared_5259_ == 0)
{
v___x_5261_ = v___x_5258_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5256_);
v___x_5261_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
lean_object* v___x_5262_; 
v___x_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5262_, 0, v___x_5261_);
return v___x_5262_;
}
}
}
else
{
lean_object* v_a_5265_; 
v_a_5265_ = lean_ctor_get(v_x_5254_, 0);
lean_inc(v_a_5265_);
lean_dec_ref(v_x_5254_);
if (lean_obj_tag(v_a_5265_) == 0)
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5274_; 
lean_dec_ref(v___f_5253_);
v_a_5266_ = lean_ctor_get(v_a_5265_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v_a_5265_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5268_ = v_a_5265_;
v_isShared_5269_ = v_isSharedCheck_5274_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v_a_5265_);
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
v_a_5275_ = lean_ctor_get(v_a_5265_, 0);
lean_inc(v_a_5275_);
lean_dec_ref(v_a_5265_);
v___x_5276_ = lean_unsigned_to_nat(0u);
v___x_5277_ = 0;
v___x_5278_ = lean_task_map(v___f_5253_, v_a_5275_, v___x_5276_, v___x_5277_);
v___x_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
return v___x_5279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5280_, lean_object* v_x_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5280_, v_x_5281_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5284_, lean_object* v___f_5285_, lean_object* v_receiver_5286_){
_start:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; uint8_t v___x_5293_; lean_object* v___x_5294_; 
v___x_5288_ = l_Std_Channel_recv___redArg(v_inst_5284_, v_receiver_5286_);
v___x_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5288_);
v___x_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
v___x_5291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5290_);
v___x_5292_ = lean_unsigned_to_nat(0u);
v___x_5293_ = 0;
v___x_5294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5292_, v___x_5293_, v___x_5291_, v___f_5285_);
return v___x_5294_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5295_, lean_object* v___f_5296_, lean_object* v_receiver_5297_, lean_object* v___y_5298_){
_start:
{
lean_object* v_res_5299_; 
v_res_5299_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5295_, v___f_5296_, v_receiver_5297_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5303_){
_start:
{
lean_object* v___f_5304_; lean_object* v___f_5305_; 
v___f_5304_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5305_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5305_, 0, v_inst_5303_);
lean_closure_set(v___f_5305_, 1, v___f_5304_);
return v___f_5305_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5306_, lean_object* v_inst_5307_){
_start:
{
lean_object* v___x_5308_; 
v___x_5308_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5307_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__0(lean_object* v_a_5309_){
_start:
{
lean_object* v___x_5310_; 
v___x_5310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5310_, 0, v_a_5309_);
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1(lean_object* v___f_5311_, lean_object* v_x_5312_){
_start:
{
if (lean_obj_tag(v_x_5312_) == 0)
{
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5322_; 
lean_dec_ref(v___f_5311_);
v_a_5314_ = lean_ctor_get(v_x_5312_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v_x_5312_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5316_ = v_x_5312_;
v_isShared_5317_ = v_isSharedCheck_5322_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v_x_5312_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5322_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5319_; 
if (v_isShared_5317_ == 0)
{
v___x_5319_ = v___x_5316_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5314_);
v___x_5319_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
lean_object* v___x_5320_; 
v___x_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5320_, 0, v___x_5319_);
return v___x_5320_;
}
}
}
else
{
lean_object* v_a_5323_; lean_object* v___x_5324_; uint8_t v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; 
v_a_5323_ = lean_ctor_get(v_x_5312_, 0);
lean_inc(v_a_5323_);
lean_dec_ref(v_x_5312_);
v___x_5324_ = lean_unsigned_to_nat(0u);
v___x_5325_ = 0;
v___x_5326_ = lean_task_map(v___f_5311_, v_a_5323_, v___x_5324_, v___x_5325_);
v___x_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5326_);
return v___x_5327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed(lean_object* v___f_5328_, lean_object* v_x_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__1(v___f_5328_, v_x_5329_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5332_, lean_object* v_receiver_5333_, lean_object* v_x_5334_){
_start:
{
lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; uint8_t v___x_5340_; lean_object* v___x_5341_; 
v___x_5336_ = l_Std_Channel_send___redArg(v_receiver_5333_, v_x_5334_);
v___x_5337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5336_);
v___x_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5338_, 0, v___x_5337_);
v___x_5339_ = lean_unsigned_to_nat(0u);
v___x_5340_ = 0;
v___x_5341_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5339_, v___x_5340_, v___x_5338_, v___f_5332_);
return v___x_5341_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5342_, lean_object* v_receiver_5343_, lean_object* v_x_5344_, lean_object* v___y_5345_){
_start:
{
lean_object* v_res_5346_; 
v_res_5346_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__2(v___f_5342_, v_receiver_5343_, v_x_5344_);
return v_res_5346_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3(void){
_start:
{
lean_object* v___x_5352_; lean_object* v___f_5353_; lean_object* v___f_5354_; 
v___x_5352_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3);
v___f_5353_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___f_5354_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5354_, 0, v___f_5353_);
lean_closure_set(v___f_5354_, 1, v___x_5352_);
return v___f_5354_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___f_5355_; lean_object* v___f_5356_; lean_object* v___f_5357_; lean_object* v___x_5358_; 
v___f_5355_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2));
v___f_5356_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3);
v___f_5357_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___closed__2));
v___x_5358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5358_, 0, v___f_5357_);
lean_ctor_set(v___x_5358_, 1, v___f_5356_);
lean_ctor_set(v___x_5358_, 2, v___f_5355_);
return v___x_5358_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5359_, lean_object* v_inst_5360_){
_start:
{
lean_object* v___x_5361_; 
v___x_5361_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4);
return v___x_5361_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5362_, lean_object* v_inst_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5362_, v_inst_5363_);
lean_dec(v_inst_5363_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5365_){
_start:
{
lean_inc_ref(v_ch_5365_);
return v_ch_5365_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5366_){
_start:
{
lean_object* v_res_5367_; 
v_res_5367_ = l_Std_Channel_sync___redArg(v_ch_5366_);
lean_dec_ref(v_ch_5366_);
return v_res_5367_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5368_, lean_object* v_ch_5369_){
_start:
{
lean_inc_ref(v_ch_5369_);
return v_ch_5369_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5370_, lean_object* v_ch_5371_){
_start:
{
lean_object* v_res_5372_; 
v_res_5372_ = l_Std_Channel_sync(v_00_u03b1_5370_, v_ch_5371_);
lean_dec_ref(v_ch_5371_);
return v_res_5372_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5373_){
_start:
{
lean_object* v___x_5375_; 
v___x_5375_ = l_Std_CloseableChannel_new___redArg(v_capacity_5373_);
return v___x_5375_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5376_, lean_object* v_a_5377_){
_start:
{
lean_object* v_res_5378_; 
v_res_5378_ = l_Std_Channel_Sync_new___redArg(v_capacity_5376_);
return v_res_5378_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5379_, lean_object* v_capacity_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l_Std_CloseableChannel_new___redArg(v_capacity_5380_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5383_, lean_object* v_capacity_5384_, lean_object* v_a_5385_){
_start:
{
lean_object* v_res_5386_; 
v_res_5386_ = l_Std_Channel_Sync_new(v_00_u03b1_5383_, v_capacity_5384_);
return v_res_5386_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5387_, lean_object* v_v_5388_){
_start:
{
uint8_t v___x_5390_; 
v___x_5390_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5387_, v_v_5388_);
return v___x_5390_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5391_, lean_object* v_v_5392_, lean_object* v_a_5393_){
_start:
{
uint8_t v_res_5394_; lean_object* v_r_5395_; 
v_res_5394_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5391_, v_v_5392_);
v_r_5395_ = lean_box(v_res_5394_);
return v_r_5395_;
}
}
LEAN_EXPORT uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5396_, lean_object* v_ch_5397_, lean_object* v_v_5398_){
_start:
{
uint8_t v___x_5400_; 
v___x_5400_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5397_, v_v_5398_);
return v___x_5400_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5401_, lean_object* v_ch_5402_, lean_object* v_v_5403_, lean_object* v_a_5404_){
_start:
{
uint8_t v_res_5405_; lean_object* v_r_5406_; 
v_res_5405_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5401_, v_ch_5402_, v_v_5403_);
v_r_5406_ = lean_box(v_res_5405_);
return v_r_5406_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5407_, lean_object* v_v_5408_){
_start:
{
lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5410_ = l_Std_Channel_send___redArg(v_ch_5407_, v_v_5408_);
v___x_5411_ = lean_io_wait(v___x_5410_);
return v___x_5411_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5412_, lean_object* v_v_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v_res_5415_; 
v_res_5415_ = l_Std_Channel_Sync_send___redArg(v_ch_5412_, v_v_5413_);
return v_res_5415_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5416_, lean_object* v_ch_5417_, lean_object* v_v_5418_){
_start:
{
lean_object* v___x_5420_; 
v___x_5420_ = l_Std_Channel_Sync_send___redArg(v_ch_5417_, v_v_5418_);
return v___x_5420_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5421_, lean_object* v_ch_5422_, lean_object* v_v_5423_, lean_object* v_a_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l_Std_Channel_Sync_send(v_00_u03b1_5421_, v_ch_5422_, v_v_5423_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5426_){
_start:
{
lean_object* v___x_5428_; 
v___x_5428_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5426_);
return v___x_5428_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5429_, lean_object* v_a_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5429_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5432_, lean_object* v_ch_5433_){
_start:
{
lean_object* v___x_5435_; 
v___x_5435_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5433_);
return v___x_5435_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5436_, lean_object* v_ch_5437_, lean_object* v_a_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5436_, v_ch_5437_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5440_, lean_object* v_ch_5441_){
_start:
{
lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5443_ = l_Std_Channel_recv___redArg(v_inst_5440_, v_ch_5441_);
v___x_5444_ = lean_io_wait(v___x_5443_);
return v___x_5444_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5445_, lean_object* v_ch_5446_, lean_object* v_a_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l_Std_Channel_Sync_recv___redArg(v_inst_5445_, v_ch_5446_);
return v_res_5448_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5449_, lean_object* v_inst_5450_, lean_object* v_ch_5451_){
_start:
{
lean_object* v___x_5453_; 
v___x_5453_ = l_Std_Channel_Sync_recv___redArg(v_inst_5450_, v_ch_5451_);
return v___x_5453_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5454_, lean_object* v_inst_5455_, lean_object* v_ch_5456_, lean_object* v_a_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l_Std_Channel_Sync_recv(v_00_u03b1_5454_, v_inst_5455_, v_ch_5456_);
return v_res_5458_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5459_, lean_object* v_b_5460_, lean_object* v_toBind_5461_, lean_object* v___f_5462_, lean_object* v_a_5463_){
_start:
{
lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5464_ = lean_apply_2(v_f_5459_, v_a_5463_, v_b_5460_);
v___x_5465_ = lean_apply_4(v_toBind_5461_, lean_box(0), lean_box(0), v___x_5464_, v___f_5462_);
return v___x_5465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5466_, lean_object* v_inst_5467_, lean_object* v_inst_5468_, lean_object* v_ch_5469_, lean_object* v_f_5470_, lean_object* v_b_5471_){
_start:
{
lean_object* v_toApplicative_5472_; lean_object* v_toBind_5473_; lean_object* v_toPure_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___f_5477_; lean_object* v___f_5478_; lean_object* v___x_5479_; 
v_toApplicative_5472_ = lean_ctor_get(v_inst_5467_, 0);
v_toBind_5473_ = lean_ctor_get(v_inst_5467_, 1);
lean_inc_n(v_toBind_5473_, 2);
v_toPure_5474_ = lean_ctor_get(v_toApplicative_5472_, 1);
lean_inc(v_toPure_5474_);
lean_inc_ref(v_ch_5469_);
lean_inc(v_inst_5466_);
v___x_5475_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5475_, 0, lean_box(0));
lean_closure_set(v___x_5475_, 1, v_inst_5466_);
lean_closure_set(v___x_5475_, 2, v_ch_5469_);
lean_inc(v_inst_5468_);
v___x_5476_ = lean_apply_2(v_inst_5468_, lean_box(0), v___x_5475_);
lean_inc(v_f_5470_);
v___f_5477_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5477_, 0, v_toPure_5474_);
lean_closure_set(v___f_5477_, 1, v_inst_5466_);
lean_closure_set(v___f_5477_, 2, v_inst_5467_);
lean_closure_set(v___f_5477_, 3, v_inst_5468_);
lean_closure_set(v___f_5477_, 4, v_ch_5469_);
lean_closure_set(v___f_5477_, 5, v_f_5470_);
v___f_5478_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5478_, 0, v_f_5470_);
lean_closure_set(v___f_5478_, 1, v_b_5471_);
lean_closure_set(v___f_5478_, 2, v_toBind_5473_);
lean_closure_set(v___f_5478_, 3, v___f_5477_);
v___x_5479_ = lean_apply_4(v_toBind_5473_, lean_box(0), lean_box(0), v___x_5476_, v___f_5478_);
return v___x_5479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5480_, lean_object* v_inst_5481_, lean_object* v_inst_5482_, lean_object* v_inst_5483_, lean_object* v_ch_5484_, lean_object* v_f_5485_, lean_object* v_____do__lift_5486_){
_start:
{
if (lean_obj_tag(v_____do__lift_5486_) == 0)
{
lean_object* v_a_5487_; lean_object* v___x_5488_; 
lean_dec(v_f_5485_);
lean_dec_ref(v_ch_5484_);
lean_dec(v_inst_5483_);
lean_dec_ref(v_inst_5482_);
lean_dec(v_inst_5481_);
v_a_5487_ = lean_ctor_get(v_____do__lift_5486_, 0);
lean_inc(v_a_5487_);
lean_dec_ref(v_____do__lift_5486_);
v___x_5488_ = lean_apply_2(v_toPure_5480_, lean_box(0), v_a_5487_);
return v___x_5488_;
}
else
{
lean_object* v_a_5489_; lean_object* v___x_5490_; 
lean_dec(v_toPure_5480_);
v_a_5489_ = lean_ctor_get(v_____do__lift_5486_, 0);
lean_inc(v_a_5489_);
lean_dec_ref(v_____do__lift_5486_);
v___x_5490_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5481_, v_inst_5482_, v_inst_5483_, v_ch_5484_, v_f_5485_, v_a_5489_);
return v___x_5490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5491_, lean_object* v_m_5492_, lean_object* v_00_u03b2_5493_, lean_object* v_inst_5494_, lean_object* v_inst_5495_, lean_object* v_inst_5496_, lean_object* v_ch_5497_, lean_object* v_f_5498_, lean_object* v_b_5499_){
_start:
{
lean_object* v___x_5500_; 
v___x_5500_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5494_, v_inst_5495_, v_inst_5496_, v_ch_5497_, v_f_5498_, v_b_5499_);
return v___x_5500_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5501_, lean_object* v_inst_5502_, lean_object* v_inst_5503_, lean_object* v_ch_5504_, lean_object* v_b_5505_, lean_object* v_f_5506_){
_start:
{
lean_object* v___x_5507_; 
v___x_5507_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5501_, v_inst_5502_, v_inst_5503_, v_ch_5504_, v_f_5506_, v_b_5505_);
return v___x_5507_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5508_, lean_object* v_m_5509_, lean_object* v_inst_5510_, lean_object* v_inst_5511_, lean_object* v_inst_5512_, lean_object* v_00_u03b2_5513_, lean_object* v_ch_5514_, lean_object* v_b_5515_, lean_object* v_f_5516_){
_start:
{
lean_object* v___x_5517_; 
v___x_5517_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5510_, v_inst_5511_, v_inst_5512_, v_ch_5514_, v_f_5516_, v_b_5515_);
return v___x_5517_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5518_, lean_object* v_inst_5519_, lean_object* v_inst_5520_, lean_object* v_00_u03b2_5521_, lean_object* v_ch_5522_, lean_object* v_b_5523_, lean_object* v_f_5524_){
_start:
{
lean_object* v___x_5525_; 
v___x_5525_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5518_, v_inst_5519_, v_inst_5520_, v_ch_5522_, v_f_5524_, v_b_5523_);
return v___x_5525_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5526_, lean_object* v_inst_5527_, lean_object* v_inst_5528_){
_start:
{
lean_object* v___f_5529_; 
v___f_5529_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5529_, 0, v_inst_5526_);
lean_closure_set(v___f_5529_, 1, v_inst_5527_);
lean_closure_set(v___f_5529_, 2, v_inst_5528_);
return v___f_5529_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5530_, lean_object* v_m_5531_, lean_object* v_inst_5532_, lean_object* v_inst_5533_, lean_object* v_inst_5534_){
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

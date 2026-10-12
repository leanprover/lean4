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
lean_object* l_Std_CloseableChannel_Error_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Error_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_CloseableChannel_Error_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_CloseableChannel_Error_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_CloseableChannel_Error_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_CloseableChannel_Error_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Error_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_CloseableChannel_Error_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_CloseableChannel_Error_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___redArg(lean_object* v_closed_24_){
_start:
{
lean_inc(v_closed_24_);
return v_closed_24_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___redArg___boxed(lean_object* v_closed_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_CloseableChannel_Error_closed_elim___redArg(v_closed_25_);
lean_dec(v_closed_25_);
return v_res_26_;
}
}
lean_object* l_Std_CloseableChannel_Error_closed_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_closed_30_){
_start:
{
lean_inc(v_closed_30_);
return v_closed_30_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Error_closed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_closed_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_CloseableChannel_Error_closed_elim(lean_box(0), v_t_28_, lean_box(0), v_closed_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_closed_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_closed_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_CloseableChannel_Error_closed_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_closed_35_);
lean_dec(v_closed_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(lean_object* v_alreadyClosed_38_){
_start:
{
lean_inc(v_alreadyClosed_38_);
return v_alreadyClosed_38_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg___boxed(lean_object* v_alreadyClosed_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(v_alreadyClosed_39_);
lean_dec(v_alreadyClosed_39_);
return v_res_40_;
}
}
lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_alreadyClosed_44_){
_start:
{
lean_inc(v_alreadyClosed_44_);
return v_alreadyClosed_44_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Error_alreadyClosed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_alreadyClosed_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_CloseableChannel_Error_alreadyClosed_elim(lean_box(0), v_t_42_, lean_box(0), v_alreadyClosed_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_alreadyClosed_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_alreadyClosed_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_CloseableChannel_Error_alreadyClosed_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_alreadyClosed_49_);
lean_dec(v_alreadyClosed_49_);
return v_res_51_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instReprError_repr___closed__4(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(2u);
v___x_59_ = lean_nat_to_int(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instReprError_repr___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
lean_object* l_Std_CloseableChannel_instReprError_repr(uint8_t v_x_62_, lean_object* v_prec_63_){
_start:
{
lean_object* v___y_65_; lean_object* v___y_72_; 
if (v_x_62_ == 0)
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_63_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__4, &l_Std_CloseableChannel_instReprError_repr___closed__4_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__4);
v___y_65_ = v___x_80_;
goto v___jp_64_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__5, &l_Std_CloseableChannel_instReprError_repr___closed__5_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__5);
v___y_65_ = v___x_81_;
goto v___jp_64_;
}
}
else
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1024u);
v___x_83_ = lean_nat_dec_le(v___x_82_, v_prec_63_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__4, &l_Std_CloseableChannel_instReprError_repr___closed__4_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__4);
v___y_72_ = v___x_84_;
goto v___jp_71_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Std_CloseableChannel_instReprError_repr___closed__5, &l_Std_CloseableChannel_instReprError_repr___closed__5_once, _init_l_Std_CloseableChannel_instReprError_repr___closed__5);
v___y_72_ = v___x_85_;
goto v___jp_71_;
}
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_66_ = ((lean_object*)(l_Std_CloseableChannel_instReprError_repr___closed__1));
lean_inc(v___y_65_);
v___x_67_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_67_, 0, v___y_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = 0;
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_68_);
v___x_70_ = l_Repr_addAppParen(v___x_69_, v_prec_63_);
return v___x_70_;
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = ((lean_object*)(l_Std_CloseableChannel_instReprError_repr___closed__3));
lean_inc(v___y_72_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = 0;
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = l_Repr_addAppParen(v___x_76_, v_prec_63_);
return v___x_77_;
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instReprError_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_62_ = stack[0].m_num;
lean_object* v_prec_63_ = stack[1].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Std_CloseableChannel_instReprError_repr(v_x_62_, v_prec_63_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instReprError_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_117__boxed_89_; lean_object* v_res_90_; 
v_x_117__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Std_CloseableChannel_instReprError_repr(v_x_117__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
uint8_t l_Std_CloseableChannel_Error_ofNat(lean_object* v_n_93_){
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
LEAN_EXPORT void l_Std_CloseableChannel_Error_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_93_ = stack[0].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_Std_CloseableChannel_Error_ofNat(v_n_93_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Error_ofNat___boxed(lean_object* v_n_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Std_CloseableChannel_Error_ofNat(v_n_99_);
lean_dec(v_n_99_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
uint8_t l_Std_CloseableChannel_instDecidableEqError(uint8_t v_x_102_, uint8_t v_y_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_104_ = lean_box(v_x_102_);
v___x_105_ = lean_obj_tag_nat(v___x_104_);
lean_dec(v___x_104_);
v___x_106_ = lean_box(v_y_103_);
v___x_107_ = lean_obj_tag_nat(v___x_106_);
lean_dec(v___x_106_);
v___x_108_ = lean_nat_dec_eq(v___x_105_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instDecidableEqError_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_102_ = stack[0].m_num;
uint8_t v_y_103_ = stack[1].m_num;
uint8_t v_res_109_;
v_res_109_ = l_Std_CloseableChannel_instDecidableEqError(v_x_102_, v_y_103_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instDecidableEqError___boxed(lean_object* v_x_110_, lean_object* v_y_111_){
_start:
{
uint8_t v_x_23__boxed_112_; uint8_t v_y_24__boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_x_23__boxed_112_ = lean_unbox(v_x_110_);
v_y_24__boxed_113_ = lean_unbox(v_y_111_);
v_res_114_ = l_Std_CloseableChannel_instDecidableEqError(v_x_23__boxed_112_, v_y_24__boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
uint64_t l_Std_CloseableChannel_instHashableError_hash(uint8_t v_x_116_){
_start:
{
if (v_x_116_ == 0)
{
uint64_t v___x_117_; 
v___x_117_ = 0ULL;
return v___x_117_;
}
else
{
uint64_t v___x_118_; 
v___x_118_ = 1ULL;
return v___x_118_;
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instHashableError_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_116_ = stack[0].m_num;
uint64_t v_res_119_;
v_res_119_ = l_Std_CloseableChannel_instHashableError_hash(v_x_116_);
stack->m_num = v_res_119_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instHashableError_hash___boxed(lean_object* v_x_120_){
_start:
{
uint8_t v_x_28__boxed_121_; uint64_t v_res_122_; lean_object* v_r_123_; 
v_x_28__boxed_121_ = lean_unbox(v_x_120_);
v_res_122_ = l_Std_CloseableChannel_instHashableError_hash(v_x_28__boxed_121_);
v_r_123_ = lean_box_uint64(v_res_122_);
return v_r_123_;
}
}
lean_object* l_Std_CloseableChannel_instToStringError___lam__0(uint8_t v_x_128_){
_start:
{
if (v_x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Std_CloseableChannel_instToStringError___lam__0___closed__0));
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = ((lean_object*)(l_Std_CloseableChannel_instToStringError___lam__0___closed__1));
return v___x_130_;
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instToStringError___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_128_ = stack[0].m_num;
lean_object* v_res_131_;
v_res_131_ = l_Std_CloseableChannel_instToStringError___lam__0(v_x_128_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instToStringError___lam__0___boxed(lean_object* v_x_132_){
_start:
{
uint8_t v_x_26__boxed_133_; lean_object* v_res_134_; 
v_x_26__boxed_133_ = lean_unbox(v_x_132_);
v_res_134_ = l_Std_CloseableChannel_instToStringError___lam__0(v_x_26__boxed_133_);
return v_res_134_;
}
}
lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(lean_object* v_00_u03b1_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = lean_apply_1(v_x_142_, lean_box(0));
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_166_; 
v_a_153_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_166_ == 0)
{
v___x_155_ = v___x_144_;
v_isShared_156_ = v_isSharedCheck_166_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_144_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_166_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
uint8_t v___x_157_; 
v___x_157_ = lean_unbox(v_a_153_);
lean_dec(v_a_153_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_158_ = ((lean_object*)(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0));
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_158_);
v___x_160_ = v___x_155_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
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
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = ((lean_object*)(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1));
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_162_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_142_ = stack[1].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(lean_box(0), v_x_142_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___boxed(lean_object* v_00_u03b1_168_, lean_object* v_x_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(v_00_u03b1_168_, v_x_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___redArg(lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_tag_nat(v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___redArg___boxed(lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___redArg(v_x_176_);
lean_dec_ref(v_x_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl(lean_object* v_00_u03b1_178_, lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_tag_nat(v_x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl___boxed(lean_object* v_00_u03b1_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___impl(v_00_u03b1_181_, v_x_182_);
lean_dec_ref(v_x_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(lean_object* v_t_184_, lean_object* v_k_185_){
_start:
{
if (lean_obj_tag(v_t_184_) == 0)
{
lean_object* v_promise_186_; lean_object* v___x_187_; 
v_promise_186_ = lean_ctor_get(v_t_184_, 0);
lean_inc(v_promise_186_);
lean_dec_ref_known(v_t_184_, 1);
v___x_187_ = lean_apply_1(v_k_185_, v_promise_186_);
return v___x_187_;
}
else
{
lean_object* v_finished_188_; lean_object* v___x_189_; 
v_finished_188_ = lean_ctor_get(v_t_184_, 0);
lean_inc_ref(v_finished_188_);
lean_dec_ref_known(v_t_184_, 1);
v___x_189_ = lean_apply_1(v_k_185_, v_finished_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(lean_object* v_00_u03b1_190_, lean_object* v_motive_191_, lean_object* v_ctorIdx_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_k_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_193_, v_k_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___boxed(lean_object* v_00_u03b1_197_, lean_object* v_motive_198_, lean_object* v_ctorIdx_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_k_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(v_00_u03b1_197_, v_motive_198_, v_ctorIdx_199_, v_t_200_, v_h_201_, v_k_202_);
lean_dec(v_ctorIdx_199_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim___redArg(lean_object* v_t_204_, lean_object* v_normal_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_204_, v_normal_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim(lean_object* v_00_u03b1_207_, lean_object* v_motive_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_normal_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_209_, v_normal_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim___redArg(lean_object* v_t_213_, lean_object* v_select_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_213_, v_select_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim(lean_object* v_00_u03b1_216_, lean_object* v_motive_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_select_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(v_t_218_, v_select_220_);
return v___x_221_;
}
}
uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(lean_object* v_x_222_, lean_object* v_w_223_, lean_object* v_lose_224_){
_start:
{
lean_object* v_finished_226_; lean_object* v_promise_227_; lean_object* v___x_228_; uint8_t v___y_230_; uint8_t v___x_238_; 
v_finished_226_ = lean_ctor_get(v_w_223_, 0);
v_promise_227_ = lean_ctor_get(v_w_223_, 1);
v___x_228_ = lean_st_ref_take(v_finished_226_);
v___x_238_ = lean_unbox(v___x_228_);
lean_dec(v___x_228_);
if (v___x_238_ == 0)
{
uint8_t v___x_239_; 
v___x_239_ = 1;
v___y_230_ = v___x_239_;
goto v___jp_229_;
}
else
{
uint8_t v___x_240_; 
v___x_240_ = 0;
v___y_230_ = v___x_240_;
goto v___jp_229_;
}
v___jp_229_:
{
uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = 1;
v___x_232_ = lean_box(v___x_231_);
v___x_233_ = lean_st_ref_put(v_finished_226_, v___x_232_);
if (v___y_230_ == 0)
{
lean_object* v___x_234_; uint8_t v___x_235_; 
lean_dec(v_x_222_);
v___x_234_ = lean_apply_1(v_lose_224_, lean_box(0));
v___x_235_ = lean_unbox(v___x_234_);
return v___x_235_;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec_ref(v_lose_224_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v_x_222_);
v___x_237_ = lean_io_promise_resolve(v___x_236_, v_promise_227_);
return v___y_230_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_222_ = stack[0].m_obj;
lean_object* v_w_223_ = stack[1].m_obj;
lean_object* v_lose_224_ = stack[2].m_obj;
uint8_t v_res_241_;
v_res_241_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_222_, v_w_223_, v_lose_224_);
stack->m_num = v_res_241_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg___boxed(lean_object* v_x_242_, lean_object* v_w_243_, lean_object* v_lose_244_, lean_object* v___y_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_242_, v_w_243_, v_lose_244_);
lean_dec_ref(v_w_243_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
uint8_t l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(lean_object* v_00_u03b1_248_, lean_object* v_x_249_, lean_object* v_w_250_, lean_object* v_lose_251_){
_start:
{
uint8_t v___x_253_; 
v___x_253_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_249_, v_w_250_, v_lose_251_);
return v___x_253_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_249_ = stack[1].m_obj;
lean_object* v_w_250_ = stack[2].m_obj;
lean_object* v_lose_251_ = stack[3].m_obj;
uint8_t v_res_254_;
v_res_254_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(lean_box(0), v_x_249_, v_w_250_, v_lose_251_);
stack->m_num = v_res_254_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___boxed(lean_object* v_00_u03b1_255_, lean_object* v_x_256_, lean_object* v_w_257_, lean_object* v_lose_258_, lean_object* v___y_259_){
_start:
{
uint8_t v_res_260_; lean_object* v_r_261_; 
v_res_260_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(v_00_u03b1_255_, v_x_256_, v_w_257_, v_lose_258_);
lean_dec_ref(v_w_257_);
v_r_261_ = lean_box(v_res_260_);
return v_r_261_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(uint8_t v___x_262_){
_start:
{
return v___x_262_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_262_ = stack[0].m_num;
uint8_t v_res_264_;
v_res_264_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(v___x_262_);
stack->m_num = v_res_264_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0___boxed(lean_object* v___x_265_, lean_object* v___y_266_){
_start:
{
uint8_t v___x_390__boxed_267_; uint8_t v_res_268_; lean_object* v_r_269_; 
v___x_390__boxed_267_ = lean_unbox(v___x_265_);
v_res_268_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(v___x_390__boxed_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(lean_object* v_c_273_, lean_object* v_x_274_){
_start:
{
if (lean_obj_tag(v_c_273_) == 0)
{
lean_object* v_promise_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_promise_276_ = lean_ctor_get(v_c_273_, 0);
v___x_277_ = lean_io_promise_resolve(v_x_274_, v_promise_276_);
v___x_278_ = 1;
return v___x_278_;
}
else
{
lean_object* v_finished_279_; lean_object* v_lose_280_; uint8_t v___x_281_; 
v_finished_279_ = lean_ctor_get(v_c_273_, 0);
v_lose_280_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0));
v___x_281_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_274_, v_finished_279_, v_lose_280_);
return v___x_281_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_273_ = stack[0].m_obj;
lean_object* v_x_274_ = stack[1].m_obj;
uint8_t v_res_282_;
v_res_282_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_273_, v_x_274_);
stack->m_num = v_res_282_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___boxed(lean_object* v_c_283_, lean_object* v_x_284_, lean_object* v_a_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_283_, v_x_284_);
lean_dec_ref(v_c_283_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(lean_object* v_00_u03b1_288_, lean_object* v_c_289_, lean_object* v_x_290_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_c_289_, v_x_290_);
return v___x_292_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_289_ = stack[1].m_obj;
lean_object* v_x_290_ = stack[2].m_obj;
uint8_t v_res_293_;
v_res_293_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(lean_box(0), v_c_289_, v_x_290_);
stack->m_num = v_res_293_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___boxed(lean_object* v_00_u03b1_294_, lean_object* v_c_295_, lean_object* v_x_296_, lean_object* v_a_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(v_00_u03b1_294_, v_c_295_, v_x_296_);
lean_dec_ref(v_c_295_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0(void){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_Queue_empty___redArg();
return v___x_300_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1(void){
_start:
{
uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = 0;
v___x_302_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_303_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
lean_ctor_set_uint8(v___x_303_, sizeof(void*)*2, v___x_301_);
return v___x_303_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg(){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1);
v___x_306_ = l_Std_Mutex_new___redArg(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_307_;
v_res_307_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___boxed(lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
return v_res_309_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(lean_object* v_00_u03b1_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
return v___x_312_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_313_;
v_res_313_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(lean_box(0));
stack->m_obj
 = v_res_313_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___boxed(lean_object* v_00_u03b1_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(v_00_u03b1_314_);
return v_res_316_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(lean_object* v_mutex_317_, lean_object* v_k_318_){
_start:
{
lean_object* v_ref_320_; lean_object* v_mutex_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_ref_320_ = lean_ctor_get(v_mutex_317_, 0);
lean_inc(v_ref_320_);
v_mutex_321_ = lean_ctor_get(v_mutex_317_, 1);
lean_inc(v_mutex_321_);
lean_dec_ref(v_mutex_317_);
v___x_322_ = lean_io_basemutex_lock(v_mutex_321_);
v___x_323_ = lean_apply_2(v_k_318_, v_ref_320_, lean_box(0));
v___x_324_ = lean_io_basemutex_unlock(v_mutex_321_);
lean_dec(v_mutex_321_);
return v___x_323_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_317_ = stack[0].m_obj;
lean_object* v_k_318_ = stack[1].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_317_, v_k_318_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg___boxed(lean_object* v_mutex_326_, lean_object* v_k_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_326_, v_k_327_);
return v_res_329_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_mutex_332_, lean_object* v_k_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_332_, v_k_333_);
return v___x_335_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_332_ = stack[2].m_obj;
lean_object* v_k_333_ = stack[3].m_obj;
lean_object* v_res_336_;
v_res_336_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(lean_box(0), lean_box(0), v_mutex_332_, v_k_333_);
stack->m_obj
 = v_res_336_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___boxed(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_mutex_339_, lean_object* v_k_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(v_00_u03b1_337_, v_00_u03b2_338_, v_mutex_339_, v_k_340_);
return v_res_342_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(lean_object* v_v_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_values_348_; lean_object* v_consumers_349_; uint8_t v_closed_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_376_; 
v___x_346_ = lean_box(0);
v___x_347_ = lean_st_ref_get(v___y_344_);
v_values_348_ = lean_ctor_get(v___x_347_, 0);
v_consumers_349_ = lean_ctor_get(v___x_347_, 1);
v_closed_350_ = lean_ctor_get_uint8(v___x_347_, sizeof(void*)*2);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_376_ == 0)
{
v___x_352_ = v___x_347_;
v_isShared_353_ = v_isSharedCheck_376_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_consumers_349_);
lean_inc(v_values_348_);
lean_dec(v___x_347_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_376_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; 
lean_inc_ref(v_consumers_349_);
v___x_354_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_349_);
if (lean_obj_tag(v___x_354_) == 1)
{
lean_object* v_val_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v_consumers_349_);
v_val_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_370_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_val_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_370_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_fst_359_; lean_object* v_snd_360_; lean_object* v___x_362_; 
v_fst_359_ = lean_ctor_get(v_val_355_, 0);
lean_inc(v_fst_359_);
v_snd_360_ = lean_ctor_get(v_val_355_, 1);
lean_inc(v_snd_360_);
lean_dec(v_val_355_);
lean_inc(v_v_343_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v_v_343_);
v___x_362_ = v___x_357_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_v_343_);
v___x_362_ = v_reuseFailAlloc_369_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
uint8_t v___x_363_; lean_object* v___x_365_; 
v___x_363_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_359_, v___x_362_);
lean_dec(v_fst_359_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_snd_360_);
v___x_365_ = v___x_352_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_values_348_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_snd_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_368_, sizeof(void*)*2, v_closed_350_);
v___x_365_ = v_reuseFailAlloc_368_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = lean_st_ref_swap(v___y_344_, v___x_365_);
lean_dec(v___x_366_);
if (v___x_363_ == 0)
{
goto _start;
}
else
{
lean_dec(v_v_343_);
return v___x_346_;
}
}
}
}
}
else
{
lean_object* v___x_371_; lean_object* v___x_373_; 
lean_dec(v___x_354_);
v___x_371_ = l_Std_Queue_enqueue___redArg(v_v_343_, v_values_348_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_371_);
v___x_373_ = v___x_352_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_consumers_349_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, sizeof(void*)*2, v_closed_350_);
v___x_373_ = v_reuseFailAlloc_375_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; 
v___x_374_ = lean_st_ref_swap(v___y_344_, v___x_373_);
lean_dec(v___x_374_);
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_343_ = stack[0].m_obj;
lean_object* v___y_344_ = stack[1].m_obj;
lean_object* v_res_377_;
v_res_377_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_343_, v___y_344_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg___boxed(lean_object* v_v_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_378_, v___y_379_);
lean_dec(v___y_379_);
return v_res_381_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(lean_object* v_v_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; uint8_t v_closed_386_; 
v___x_385_ = lean_st_ref_get(v___y_383_);
v_closed_386_ = lean_ctor_get_uint8(v___x_385_, sizeof(void*)*2);
lean_dec(v___x_385_);
if (v_closed_386_ == 0)
{
uint8_t v___x_387_; lean_object* v___x_388_; 
v___x_387_ = 1;
v___x_388_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_382_, v___y_383_);
return v___x_387_;
}
else
{
uint8_t v___x_389_; 
lean_dec(v_v_382_);
v___x_389_ = 0;
return v___x_389_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_382_ = stack[0].m_obj;
lean_object* v___y_383_ = stack[1].m_obj;
uint8_t v_res_390_;
v_res_390_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(v_v_382_, v___y_383_);
stack->m_num = v_res_390_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed(lean_object* v_v_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
uint8_t v_res_394_; lean_object* v_r_395_; 
v_res_394_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(v_v_391_, v___y_392_);
lean_dec(v___y_392_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(lean_object* v_ch_396_, lean_object* v_v_397_){
_start:
{
lean_object* v___f_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___f_399_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_399_, 0, v_v_397_);
v___x_400_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_396_, v___f_399_);
v___x_401_ = lean_unbox(v___x_400_);
lean_dec(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_396_ = stack[0].m_obj;
lean_object* v_v_397_ = stack[1].m_obj;
uint8_t v_res_402_;
v_res_402_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_396_, v_v_397_);
stack->m_num = v_res_402_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___boxed(lean_object* v_ch_403_, lean_object* v_v_404_, lean_object* v_a_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_403_, v_v_404_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(lean_object* v_00_u03b1_408_, lean_object* v_ch_409_, lean_object* v_v_410_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_409_, v_v_410_);
return v___x_412_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_409_ = stack[1].m_obj;
lean_object* v_v_410_ = stack[2].m_obj;
uint8_t v_res_413_;
v_res_413_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(lean_box(0), v_ch_409_, v_v_410_);
stack->m_num = v_res_413_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___boxed(lean_object* v_00_u03b1_414_, lean_object* v_ch_415_, lean_object* v_v_416_, lean_object* v_a_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(v_00_u03b1_414_, v_ch_415_, v_v_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(lean_object* v_00_u03b1_420_, lean_object* v_v_421_, lean_object* v_inst_422_, lean_object* v_a_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_421_, v___y_424_);
return v___x_426_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_421_ = stack[1].m_obj;
lean_object* v_a_423_ = stack[3].m_obj;
lean_object* v___y_424_ = stack[4].m_obj;
lean_object* v_res_427_;
v_res_427_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(lean_box(0), v_v_421_, lean_box(0), v_a_423_, v___y_424_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_428_, lean_object* v_v_429_, lean_object* v_inst_430_, lean_object* v_a_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(v_00_u03b1_428_, v_v_429_, v_inst_430_, v_a_431_, v___y_432_);
lean_dec(v___y_432_);
return v_res_434_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
v___x_439_ = lean_task_pure(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
v___x_443_ = lean_task_pure(v___x_442_);
return v___x_443_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(lean_object* v_ch_444_, lean_object* v_v_445_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_444_, v_v_445_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_448_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_449_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_444_ = stack[0].m_obj;
lean_object* v_v_445_ = stack[1].m_obj;
lean_object* v_res_450_;
v_res_450_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_444_, v_v_445_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___boxed(lean_object* v_ch_451_, lean_object* v_v_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_451_, v_v_452_);
return v_res_454_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(lean_object* v_00_u03b1_455_, lean_object* v_ch_456_, lean_object* v_v_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_456_, v_v_457_);
return v___x_459_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_456_ = stack[1].m_obj;
lean_object* v_v_457_ = stack[2].m_obj;
lean_object* v_res_460_;
v_res_460_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(lean_box(0), v_ch_456_, v_v_457_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___boxed(lean_object* v_00_u03b1_461_, lean_object* v_ch_462_, lean_object* v_v_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(v_00_u03b1_461_, v_ch_462_, v_v_463_);
return v_res_465_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(lean_object* v_mutex_466_, lean_object* v_k_467_){
_start:
{
lean_object* v_ref_469_; lean_object* v_mutex_470_; lean_object* v___x_471_; lean_object* v_r_472_; 
v_ref_469_ = lean_ctor_get(v_mutex_466_, 0);
lean_inc(v_ref_469_);
v_mutex_470_ = lean_ctor_get(v_mutex_466_, 1);
lean_inc(v_mutex_470_);
lean_dec_ref(v_mutex_466_);
v___x_471_ = lean_io_basemutex_lock(v_mutex_470_);
v_r_472_ = lean_apply_2(v_k_467_, v_ref_469_, lean_box(0));
if (lean_obj_tag(v_r_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_a_473_ = lean_ctor_get(v_r_472_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_r_472_);
if (v_isSharedCheck_481_ == 0)
{
v___x_475_ = v_r_472_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v_r_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = lean_io_basemutex_unlock(v_mutex_470_);
lean_dec(v_mutex_470_);
if (v_isShared_476_ == 0)
{
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_473_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
v_a_482_ = lean_ctor_get(v_r_472_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_r_472_);
if (v_isSharedCheck_490_ == 0)
{
v___x_484_ = v_r_472_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v_r_472_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_io_basemutex_unlock(v_mutex_470_);
lean_dec(v_mutex_470_);
if (v_isShared_485_ == 0)
{
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_482_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_466_ = stack[0].m_obj;
lean_object* v_k_467_ = stack[1].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_466_, v_k_467_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg___boxed(lean_object* v_mutex_492_, lean_object* v_k_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_492_, v_k_493_);
return v_res_495_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(lean_object* v_00_u03b1_496_, lean_object* v_00_u03b2_497_, lean_object* v_mutex_498_, lean_object* v_k_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_498_, v_k_499_);
return v___x_501_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_498_ = stack[2].m_obj;
lean_object* v_k_499_ = stack[3].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(lean_box(0), lean_box(0), v_mutex_498_, v_k_499_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___boxed(lean_object* v_00_u03b1_503_, lean_object* v_00_u03b2_504_, lean_object* v_mutex_505_, lean_object* v_k_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(v_00_u03b1_503_, v_00_u03b2_504_, v_mutex_505_, v_k_506_);
return v_res_508_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(lean_object* v_as_509_, size_t v_sz_510_, size_t v_i_511_, lean_object* v_b_512_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_lt(v_i_511_, v_sz_510_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_b_512_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v___x_518_; uint8_t v___x_519_; size_t v___x_520_; size_t v___x_521_; 
v___x_516_ = lean_box(0);
v_a_517_ = lean_array_uget_borrowed(v_as_509_, v_i_511_);
v___x_518_ = lean_box(0);
v___x_519_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_517_, v___x_518_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_add(v_i_511_, v___x_520_);
v_i_511_ = v___x_521_;
v_b_512_ = v___x_516_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_509_ = stack[0].m_obj;
size_t v_sz_510_ = stack[1].m_num;
size_t v_i_511_ = stack[2].m_num;
lean_object* v_b_512_ = stack[3].m_obj;
lean_object* v_res_523_;
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_509_, v_sz_510_, v_i_511_, v_b_512_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg___boxed(lean_object* v_as_524_, lean_object* v_sz_525_, lean_object* v_i_526_, lean_object* v_b_527_, lean_object* v___y_528_){
_start:
{
size_t v_sz_boxed_529_; size_t v_i_boxed_530_; lean_object* v_res_531_; 
v_sz_boxed_529_ = lean_unbox_usize(v_sz_525_);
lean_dec(v_sz_525_);
v_i_boxed_530_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_524_, v_sz_boxed_529_, v_i_boxed_530_, v_b_527_);
lean_dec_ref(v_as_524_);
return v_res_531_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; uint8_t v_closed_535_; 
v___x_534_ = lean_st_ref_get(v___y_532_);
v_closed_535_ = lean_ctor_get_uint8(v___x_534_, sizeof(void*)*2);
if (v_closed_535_ == 0)
{
lean_object* v_values_536_; lean_object* v_consumers_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_560_; 
v_values_536_ = lean_ctor_get(v___x_534_, 0);
v_consumers_537_ = lean_ctor_get(v___x_534_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_560_ == 0)
{
v___x_539_ = v___x_534_;
v_isShared_540_ = v_isSharedCheck_560_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_consumers_537_);
lean_inc(v_values_536_);
lean_dec(v___x_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_560_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; size_t v_sz_543_; size_t v___x_544_; lean_object* v___x_545_; 
v___x_541_ = l_Std_Queue_toArray___redArg(v_consumers_537_);
v___x_542_ = lean_box(0);
v_sz_543_ = lean_array_size(v___x_541_);
v___x_544_ = ((size_t)0ULL);
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v___x_541_, v_sz_543_, v___x_544_, v___x_542_);
lean_dec_ref(v___x_541_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_558_; 
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v___x_545_, 0);
lean_dec(v_unused_559_);
v___x_547_ = v___x_545_;
v_isShared_548_ = v_isSharedCheck_558_;
goto v_resetjp_546_;
}
else
{
lean_dec(v___x_545_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_558_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; uint8_t v___x_550_; lean_object* v___x_552_; 
v___x_549_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_550_ = 1;
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_549_);
v___x_552_ = v___x_539_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_values_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_549_);
v___x_552_ = v_reuseFailAlloc_557_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*2, v___x_550_);
v___x_553_ = lean_st_ref_swap(v___y_532_, v___x_552_);
lean_dec(v___x_553_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_542_);
v___x_555_ = v___x_547_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_542_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_del_object(v___x_539_);
lean_dec_ref(v_values_536_);
return v___x_545_;
}
}
}
else
{
uint8_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v___x_534_);
v___x_561_ = 1;
v___x_562_ = lean_box(v___x_561_);
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_532_ = stack[0].m_obj;
lean_object* v_res_564_;
v_res_564_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(v___y_532_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed(lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(v___y_565_);
lean_dec(v___y_565_);
return v_res_567_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(lean_object* v_ch_569_){
_start:
{
lean_object* v___f_571_; lean_object* v___x_572_; 
v___f_571_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0));
v___x_572_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_569_, v___f_571_);
return v___x_572_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_569_ = stack[0].m_obj;
lean_object* v_res_573_;
v_res_573_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_569_);
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___boxed(lean_object* v_ch_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_574_);
return v_res_576_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(lean_object* v_00_u03b1_577_, lean_object* v_ch_578_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_578_);
return v___x_580_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_578_ = stack[1].m_obj;
lean_object* v_res_581_;
v_res_581_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(lean_box(0), v_ch_578_);
stack->m_obj
 = v_res_581_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___boxed(lean_object* v_00_u03b1_582_, lean_object* v_ch_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(v_00_u03b1_582_, v_ch_583_);
return v_res_585_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(lean_object* v_00_u03b1_586_, lean_object* v_as_587_, size_t v_sz_588_, size_t v_i_589_, lean_object* v_b_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_587_, v_sz_588_, v_i_589_, v_b_590_);
return v___x_593_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_587_ = stack[1].m_obj;
size_t v_sz_588_ = stack[2].m_num;
size_t v_i_589_ = stack[3].m_num;
lean_object* v_b_590_ = stack[4].m_obj;
lean_object* v___y_591_ = stack[5].m_obj;
lean_object* v_res_594_;
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(lean_box(0), v_as_587_, v_sz_588_, v_i_589_, v_b_590_, v___y_591_);
stack->m_obj
 = v_res_594_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___boxed(lean_object* v_00_u03b1_595_, lean_object* v_as_596_, lean_object* v_sz_597_, lean_object* v_i_598_, lean_object* v_b_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
size_t v_sz_boxed_602_; size_t v_i_boxed_603_; lean_object* v_res_604_; 
v_sz_boxed_602_ = lean_unbox_usize(v_sz_597_);
lean_dec(v_sz_597_);
v_i_boxed_603_ = lean_unbox_usize(v_i_598_);
lean_dec(v_i_598_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(v_00_u03b1_595_, v_as_596_, v_sz_boxed_602_, v_i_boxed_603_, v_b_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v_as_596_);
return v_res_604_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; uint8_t v_closed_608_; 
v___x_607_ = lean_st_ref_get(v___y_605_);
v_closed_608_ = lean_ctor_get_uint8(v___x_607_, sizeof(void*)*2);
lean_dec(v___x_607_);
return v_closed_608_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_605_ = stack[0].m_obj;
uint8_t v_res_609_;
v_res_609_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(v___y_605_);
stack->m_num = v_res_609_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(v___y_610_);
lean_dec(v___y_610_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(lean_object* v_ch_615_){
_start:
{
lean_object* v___f_617_; lean_object* v___x_618_; 
v___f_617_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0));
v___x_618_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_615_, v___f_617_);
return v___x_618_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_615_ = stack[0].m_obj;
lean_object* v_res_619_;
v_res_619_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_615_);
stack->m_obj
 = v_res_619_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___boxed(lean_object* v_ch_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_620_);
return v_res_622_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(lean_object* v_00_u03b1_623_, lean_object* v_ch_624_){
_start:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_624_);
v___x_627_ = lean_unbox(v___x_626_);
lean_dec(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_624_ = stack[1].m_obj;
uint8_t v_res_628_;
v_res_628_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(lean_box(0), v_ch_624_);
stack->m_num = v_res_628_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___boxed(lean_object* v_00_u03b1_629_, lean_object* v_ch_630_, lean_object* v_a_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(v_00_u03b1_629_, v_ch_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_634_, lean_object* v_fst_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_toPure_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_toPure_637_ = lean_ctor_get(v_toApplicative_634_, 1);
lean_inc(v_toPure_637_);
lean_dec_ref(v_toApplicative_634_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v_fst_635_);
v___x_639_ = lean_apply_2(v_toPure_637_, lean_box(0), v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(lean_object* v_toApplicative_640_, lean_object* v_a_641_, lean_object* v_inst_642_, lean_object* v_toBind_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_values_645_; lean_object* v_consumers_646_; uint8_t v_closed_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_665_; 
v_values_645_ = lean_ctor_get(v_a_644_, 0);
v_consumers_646_ = lean_ctor_get(v_a_644_, 1);
v_closed_647_ = lean_ctor_get_uint8(v_a_644_, sizeof(void*)*2);
v_isSharedCheck_665_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_665_ == 0)
{
v___x_649_ = v_a_644_;
v_isShared_650_ = v_isSharedCheck_665_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_consumers_646_);
lean_inc(v_values_645_);
lean_dec(v_a_644_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_665_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; 
v___x_651_ = l_Std_Queue_dequeue_x3f___redArg(v_values_645_);
if (lean_obj_tag(v___x_651_) == 1)
{
lean_object* v_val_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___f_655_; lean_object* v___x_657_; 
v_val_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_val_652_);
lean_dec_ref_known(v___x_651_, 1);
v_fst_653_ = lean_ctor_get(v_val_652_, 0);
lean_inc(v_fst_653_);
v_snd_654_ = lean_ctor_get(v_val_652_, 1);
lean_inc(v_snd_654_);
lean_dec(v_val_652_);
v___f_655_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_655_, 0, v_toApplicative_640_);
lean_closure_set(v___f_655_, 1, v_fst_653_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v_snd_654_);
v___x_657_ = v___x_649_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_snd_654_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_consumers_646_);
lean_ctor_set_uint8(v_reuseFailAlloc_661_, sizeof(void*)*2, v_closed_647_);
v___x_657_ = v_reuseFailAlloc_661_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_inc(v_a_641_);
v___x_658_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_658_, 0, lean_box(0));
lean_closure_set(v___x_658_, 1, lean_box(0));
lean_closure_set(v___x_658_, 2, v_a_641_);
lean_closure_set(v___x_658_, 3, v___x_657_);
v___x_659_ = lean_apply_2(v_inst_642_, lean_box(0), v___x_658_);
v___x_660_ = lean_apply_4(v_toBind_643_, lean_box(0), lean_box(0), v___x_659_, v___f_655_);
return v___x_660_;
}
}
else
{
lean_object* v_toPure_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v___x_651_);
lean_del_object(v___x_649_);
lean_dec_ref(v_consumers_646_);
lean_dec(v_toBind_643_);
lean_dec(v_inst_642_);
v_toPure_662_ = lean_ctor_get(v_toApplicative_640_, 1);
lean_inc(v_toPure_662_);
lean_dec_ref(v_toApplicative_640_);
v___x_663_ = lean_box(0);
v___x_664_ = lean_apply_2(v_toPure_662_, lean_box(0), v___x_663_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_666_, lean_object* v_a_667_, lean_object* v_inst_668_, lean_object* v_toBind_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(v_toApplicative_666_, v_a_667_, v_inst_668_, v_toBind_669_, v_a_670_);
lean_dec(v_a_667_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_toApplicative_675_; lean_object* v_toBind_676_; lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_toApplicative_675_ = lean_ctor_get(v_inst_672_, 0);
lean_inc_ref(v_toApplicative_675_);
v_toBind_676_ = lean_ctor_get(v_inst_672_, 1);
lean_inc_n(v_toBind_676_, 2);
lean_dec_ref(v_inst_672_);
lean_inc(v_inst_673_);
lean_inc_n(v_a_674_, 2);
v___f_677_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_677_, 0, v_toApplicative_675_);
lean_closure_set(v___f_677_, 1, v_a_674_);
lean_closure_set(v___f_677_, 2, v_inst_673_);
lean_closure_set(v___f_677_, 3, v_toBind_676_);
v___x_678_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_678_, 0, lean_box(0));
lean_closure_set(v___x_678_, 1, lean_box(0));
lean_closure_set(v___x_678_, 2, v_a_674_);
v___x_679_ = lean_apply_2(v_inst_673_, lean_box(0), v___x_678_);
v___x_680_ = lean_apply_4(v_toBind_676_, lean_box(0), lean_box(0), v___x_679_, v___f_677_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_681_, v_inst_682_, v_a_683_);
lean_dec(v_a_683_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(lean_object* v_m_685_, lean_object* v_00_u03b1_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(v_inst_687_, v_inst_688_, v_a_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___boxed(lean_object* v_m_691_, lean_object* v_00_u03b1_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(v_m_691_, v_00_u03b1_692_, v_inst_693_, v_inst_694_, v_a_695_);
lean_dec(v_a_695_);
return v_res_696_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; lean_object* v_values_700_; lean_object* v_consumers_701_; uint8_t v_closed_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_722_; 
v___x_699_ = lean_st_ref_get(v_a_697_);
v_values_700_ = lean_ctor_get(v___x_699_, 0);
v_consumers_701_ = lean_ctor_get(v___x_699_, 1);
v_closed_702_ = lean_ctor_get_uint8(v___x_699_, sizeof(void*)*2);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_722_ == 0)
{
v___x_704_ = v___x_699_;
v_isShared_705_ = v_isSharedCheck_722_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_consumers_701_);
lean_inc(v_values_700_);
lean_dec(v___x_699_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_722_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_Queue_dequeue_x3f___redArg(v_values_700_);
if (lean_obj_tag(v___x_706_) == 1)
{
lean_object* v_val_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_720_; 
v_val_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_720_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_720_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_val_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_720_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_fst_711_; lean_object* v_snd_712_; lean_object* v___x_714_; 
v_fst_711_ = lean_ctor_get(v_val_707_, 0);
lean_inc(v_fst_711_);
v_snd_712_ = lean_ctor_get(v_val_707_, 1);
lean_inc(v_snd_712_);
lean_dec(v_val_707_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v_snd_712_);
v___x_714_ = v___x_704_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_snd_712_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_consumers_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*2, v_closed_702_);
v___x_714_ = v_reuseFailAlloc_719_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_st_ref_swap(v_a_697_, v___x_714_);
lean_dec(v___x_715_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v_fst_711_);
v___x_717_ = v___x_709_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_fst_711_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v___x_721_; 
lean_dec(v___x_706_);
lean_del_object(v___x_704_);
lean_dec_ref(v_consumers_701_);
v___x_721_ = lean_box(0);
return v___x_721_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_697_ = stack[0].m_obj;
lean_object* v_res_723_;
v_res_723_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_697_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_724_);
lean_dec(v_a_724_);
return v_res_726_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_object* v_00_u03b1_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_728_);
return v___x_730_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_728_ = stack[1].m_obj;
lean_object* v_res_731_;
v_res_731_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(lean_box(0), v_a_728_);
stack->m_obj
 = v_res_731_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_732_, lean_object* v_a_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(v_00_u03b1_732_, v_a_733_);
lean_dec(v_a_733_);
return v_res_735_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(lean_object* v_ch_737_){
_start:
{
lean_object* v___f_739_; lean_object* v___x_740_; 
v___f_739_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0));
v___x_740_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_737_, v___f_739_);
return v___x_740_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_737_ = stack[0].m_obj;
lean_object* v_res_741_;
v_res_741_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_737_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(lean_object* v_ch_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_742_);
return v_res_744_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_object* v_00_u03b1_745_, lean_object* v_ch_746_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_746_);
return v___x_748_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_746_ = stack[1].m_obj;
lean_object* v_res_749_;
v_res_749_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(lean_box(0), v_ch_746_);
stack->m_obj
 = v_res_749_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(lean_object* v_00_u03b1_750_, lean_object* v_ch_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(v_00_u03b1_750_, v_ch_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_object* v___x_755_; 
v___x_755_ = lean_box(0);
return v___x_755_;
}
else
{
lean_object* v_val_756_; 
v_val_756_ = lean_ctor_get(v_x_754_, 0);
lean_inc(v_val_756_);
return v_val_756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(v_x_757_);
lean_dec(v_x_757_);
return v_res_758_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_box(0);
v___x_760_ = lean_task_pure(v___x_759_);
return v___x_760_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(lean_object* v___f_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v___y_762_);
if (lean_obj_tag(v___x_764_) == 1)
{
lean_object* v___x_765_; 
lean_dec_ref(v___f_761_);
v___x_765_ = lean_task_pure(v___x_764_);
return v___x_765_;
}
else
{
lean_object* v___x_766_; uint8_t v_closed_767_; 
lean_dec(v___x_764_);
v___x_766_ = lean_st_ref_get(v___y_762_);
v_closed_767_ = lean_ctor_get_uint8(v___x_766_, sizeof(void*)*2);
lean_dec(v___x_766_);
if (v_closed_767_ == 0)
{
uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_values_771_; lean_object* v_consumers_772_; uint8_t v_closed_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_786_; 
v___x_768_ = 1;
v___x_769_ = lean_io_promise_new();
v___x_770_ = lean_st_ref_take(v___y_762_);
v_values_771_ = lean_ctor_get(v___x_770_, 0);
v_consumers_772_ = lean_ctor_get(v___x_770_, 1);
v_closed_773_ = lean_ctor_get_uint8(v___x_770_, sizeof(void*)*2);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_786_ == 0)
{
v___x_775_ = v___x_770_;
v_isShared_776_ = v_isSharedCheck_786_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_consumers_772_);
lean_inc(v_values_771_);
lean_dec(v___x_770_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_786_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
lean_inc(v___x_769_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_769_);
v___x_778_ = l_Std_Queue_enqueue___redArg(v___x_777_, v_consumers_772_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_778_);
v___x_780_ = v___x_775_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_values_771_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_778_);
lean_ctor_set_uint8(v_reuseFailAlloc_785_, sizeof(void*)*2, v_closed_773_);
v___x_780_ = v_reuseFailAlloc_785_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_781_ = lean_st_ref_put(v___y_762_, v___x_780_);
v___x_782_ = lean_io_promise_result_opt(v___x_769_);
lean_dec(v___x_769_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_task_map(v___f_761_, v___x_782_, v___x_783_, v___x_768_);
return v___x_784_;
}
}
}
else
{
lean_object* v___x_787_; 
lean_dec_ref(v___f_761_);
v___x_787_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_787_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_761_ = stack[0].m_obj;
lean_object* v___y_762_ = stack[1].m_obj;
lean_object* v_res_788_;
v_res_788_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(v___f_761_, v___y_762_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(lean_object* v___f_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(v___f_789_, v___y_790_);
lean_dec(v___y_790_);
return v_res_792_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(lean_object* v_ch_796_){
_start:
{
lean_object* v___f_798_; lean_object* v___x_799_; 
v___f_798_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1));
v___x_799_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_796_, v___f_798_);
return v___x_799_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_796_ = stack[0].m_obj;
lean_object* v_res_800_;
v_res_800_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_796_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(lean_object* v_ch_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_801_);
return v_res_803_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_object* v_00_u03b1_804_, lean_object* v_ch_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_805_);
return v___x_807_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_805_ = stack[1].m_obj;
lean_object* v_res_808_;
v_res_808_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(lean_box(0), v_ch_805_);
stack->m_obj
 = v_res_808_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(lean_object* v_00_u03b1_809_, lean_object* v_ch_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(v_00_u03b1_809_, v_ch_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_813_, lean_object* v_a_814_){
_start:
{
uint8_t v___y_816_; lean_object* v_values_820_; uint8_t v_closed_821_; uint8_t v___x_822_; 
v_values_820_ = lean_ctor_get(v_a_814_, 0);
v_closed_821_ = lean_ctor_get_uint8(v_a_814_, sizeof(void*)*2);
v___x_822_ = l_Std_Queue_isEmpty___redArg(v_values_820_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; 
v___x_823_ = 1;
v___y_816_ = v___x_823_;
goto v___jp_815_;
}
else
{
v___y_816_ = v_closed_821_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v_toPure_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_toPure_817_ = lean_ctor_get(v_toApplicative_813_, 1);
lean_inc(v_toPure_817_);
lean_dec_ref(v_toApplicative_813_);
v___x_818_ = lean_box(v___y_816_);
v___x_819_ = lean_apply_2(v_toPure_817_, lean_box(0), v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(v_toApplicative_824_, v_a_825_);
lean_dec_ref(v_a_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_toApplicative_830_; lean_object* v_toBind_831_; lean_object* v___f_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_toApplicative_830_ = lean_ctor_get(v_inst_827_, 0);
lean_inc_ref(v_toApplicative_830_);
v_toBind_831_ = lean_ctor_get(v_inst_827_, 1);
lean_inc(v_toBind_831_);
lean_dec_ref(v_inst_827_);
v___f_832_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_832_, 0, v_toApplicative_830_);
lean_inc(v_a_829_);
v___x_833_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_833_, 0, lean_box(0));
lean_closure_set(v___x_833_, 1, lean_box(0));
lean_closure_set(v___x_833_, 2, v_a_829_);
v___x_834_ = lean_apply_2(v_inst_828_, lean_box(0), v___x_833_);
v___x_835_ = lean_apply_4(v_toBind_831_, lean_box(0), lean_box(0), v___x_834_, v___f_832_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___boxed(lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(v_inst_836_, v_inst_837_, v_a_838_);
lean_dec(v_a_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(lean_object* v_m_840_, lean_object* v_00_u03b1_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_toApplicative_845_; lean_object* v_toBind_846_; lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_toApplicative_845_ = lean_ctor_get(v_inst_842_, 0);
lean_inc_ref(v_toApplicative_845_);
v_toBind_846_ = lean_ctor_get(v_inst_842_, 1);
lean_inc(v_toBind_846_);
lean_dec_ref(v_inst_842_);
v___f_847_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_847_, 0, v_toApplicative_845_);
lean_inc(v_a_844_);
v___x_848_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_848_, 0, lean_box(0));
lean_closure_set(v___x_848_, 1, lean_box(0));
lean_closure_set(v___x_848_, 2, v_a_844_);
v___x_849_ = lean_apply_2(v_inst_843_, lean_box(0), v___x_848_);
v___x_850_ = lean_apply_4(v_toBind_846_, lean_box(0), lean_box(0), v___x_849_, v___f_847_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___boxed(lean_object* v_m_851_, lean_object* v_00_u03b1_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(v_m_851_, v_00_u03b1_852_, v_inst_853_, v_inst_854_, v_a_855_);
lean_dec(v_a_855_);
return v_res_856_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_fst_857_, lean_object* v_x_858_){
_start:
{
if (lean_obj_tag(v_x_858_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_fst_857_);
v_a_860_ = lean_ctor_get(v_x_858_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x_858_);
if (v_isSharedCheck_868_ == 0)
{
v___x_862_ = v_x_858_;
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v_x_858_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_868_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_867_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; 
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
}
else
{
lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_877_; 
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_858_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v_x_858_, 0);
lean_dec(v_unused_878_);
v___x_870_ = v_x_858_;
v_isShared_871_ = v_isSharedCheck_877_;
goto v_resetjp_869_;
}
else
{
lean_dec(v_x_858_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_877_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v_fst_857_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_876_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; 
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_857_ = stack[0].m_obj;
lean_object* v_x_858_ = stack[1].m_obj;
lean_object* v_res_879_;
v_res_879_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_857_, v_x_858_);
stack->m_obj
 = v_res_879_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_fst_880_, lean_object* v_x_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_880_, v_x_881_);
return v_res_883_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_a_895_ = lean_ctor_get(v_x_893_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_903_ == 0)
{
v___x_897_ = v_x_893_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v_x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_902_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; 
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v_values_905_; lean_object* v_consumers_906_; uint8_t v_closed_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_925_; 
v_a_904_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v_x_893_, 1);
v_values_905_ = lean_ctor_get(v_a_904_, 0);
v_consumers_906_ = lean_ctor_get(v_a_904_, 1);
v_closed_907_ = lean_ctor_get_uint8(v_a_904_, sizeof(void*)*2);
v_isSharedCheck_925_ = !lean_is_exclusive(v_a_904_);
if (v_isSharedCheck_925_ == 0)
{
v___x_909_ = v_a_904_;
v_isShared_910_ = v_isSharedCheck_925_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_consumers_906_);
lean_inc(v_values_905_);
lean_dec(v_a_904_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_925_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; 
v___x_911_ = l_Std_Queue_dequeue_x3f___redArg(v_values_905_);
if (lean_obj_tag(v___x_911_) == 1)
{
lean_object* v_val_912_; lean_object* v_fst_913_; lean_object* v_snd_914_; lean_object* v___f_915_; lean_object* v___x_917_; 
v_val_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v___x_911_, 1);
v_fst_913_ = lean_ctor_get(v_val_912_, 0);
lean_inc(v_fst_913_);
v_snd_914_ = lean_ctor_get(v_val_912_, 1);
lean_inc(v_snd_914_);
lean_dec(v_val_912_);
v___f_915_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_915_, 0, v_fst_913_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_snd_914_);
v___x_917_ = v___x_909_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_snd_914_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_consumers_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_923_, sizeof(void*)*2, v_closed_907_);
v___x_917_ = v_reuseFailAlloc_923_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = 0;
v___x_920_ = lean_st_ref_swap(v_a_892_, v___x_917_);
lean_dec(v___x_920_);
v___x_921_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_922_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_918_, v___x_919_, v___x_921_, v___f_915_);
return v___x_922_;
}
}
else
{
lean_object* v___x_924_; 
lean_dec(v___x_911_);
lean_del_object(v___x_909_);
lean_dec_ref(v_consumers_906_);
v___x_924_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_892_ = stack[0].m_obj;
lean_object* v_x_893_ = stack[1].m_obj;
lean_object* v_res_926_;
v_res_926_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_892_, v_x_893_);
stack->m_obj
 = v_res_926_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_927_, lean_object* v_x_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_927_, v_x_928_);
lean_dec(v_a_927_);
return v_res_930_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(lean_object* v_a_931_){
_start:
{
lean_object* v___f_933_; lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_inc(v_a_931_);
v___f_933_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_933_, 0, v_a_931_);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = 0;
v___x_936_ = lean_st_ref_get(v_a_931_);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
v___x_939_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_934_, v___x_935_, v___x_938_, v___f_933_);
return v___x_939_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_931_ = stack[0].m_obj;
lean_object* v_res_940_;
v_res_940_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_931_);
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_941_);
lean_dec(v_a_941_);
return v_res_943_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_object* v_00_u03b1_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_945_);
return v___x_947_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_945_ = stack[1].m_obj;
lean_object* v_res_948_;
v_res_948_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(lean_box(0), v_a_945_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_949_, lean_object* v_a_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_949_, v_a_950_);
lean_dec(v_a_950_);
return v_res_952_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_promise_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_964_; 
v_a_956_ = lean_ctor_get(v_x_954_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_954_);
if (v_isSharedCheck_964_ == 0)
{
v___x_958_ = v_x_954_;
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v_x_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_io_promise_resolve(v_x_954_, v_promise_953_);
v___x_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_953_ = stack[0].m_obj;
lean_object* v_x_954_ = stack[1].m_obj;
lean_object* v_res_968_;
v_res_968_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_953_, v_x_954_);
stack->m_obj
 = v_res_968_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_promise_969_, lean_object* v_x_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_969_, v_x_970_);
lean_dec(v_promise_969_);
return v_res_972_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_973_, lean_object* v___y_974_, lean_object* v___f_975_, lean_object* v_x_976_){
_start:
{
if (lean_obj_tag(v_x_976_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_986_; 
lean_dec_ref(v___f_975_);
lean_dec_ref(v_lose_973_);
v_a_978_ = lean_ctor_get(v_x_976_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_976_);
if (v_isSharedCheck_986_ == 0)
{
v___x_980_ = v_x_976_;
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v_x_976_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_986_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
else
{
lean_object* v_a_987_; uint8_t v___x_988_; 
v_a_987_ = lean_ctor_get(v_x_976_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v_x_976_, 1);
v___x_988_ = lean_unbox(v_a_987_);
lean_dec(v_a_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v___f_975_);
lean_inc(v___y_974_);
v___x_989_ = lean_apply_2(v_lose_973_, v___y_974_, lean_box(0));
return v___x_989_;
}
else
{
lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec_ref(v_lose_973_);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = 0;
v___x_992_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_974_);
v___x_993_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_990_, v___x_991_, v___x_992_, v___f_975_);
return v___x_993_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lose_973_ = stack[0].m_obj;
lean_object* v___y_974_ = stack[1].m_obj;
lean_object* v___f_975_ = stack[2].m_obj;
lean_object* v_x_976_ = stack[3].m_obj;
lean_object* v_res_994_;
v_res_994_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_973_, v___y_974_, v___f_975_, v_x_976_);
stack->m_obj
 = v_res_994_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_995_, lean_object* v___y_996_, lean_object* v___f_997_, lean_object* v_x_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_995_, v___y_996_, v___f_997_, v_x_998_);
lean_dec(v___y_996_);
return v_res_1000_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(lean_object* v_w_1001_, lean_object* v_lose_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_finished_1005_; lean_object* v_promise_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; uint8_t v___y_1013_; uint8_t v___x_1021_; 
v_finished_1005_ = lean_ctor_get(v_w_1001_, 0);
lean_inc(v_finished_1005_);
v_promise_1006_ = lean_ctor_get(v_w_1001_, 1);
lean_inc(v_promise_1006_);
lean_dec_ref(v_w_1001_);
v___f_1007_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1007_, 0, v_promise_1006_);
lean_inc(v___y_1003_);
v___f_1008_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1008_, 0, v_lose_1002_);
lean_closure_set(v___f_1008_, 1, v___y_1003_);
lean_closure_set(v___f_1008_, 2, v___f_1007_);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = 0;
v___x_1011_ = lean_st_ref_take(v_finished_1005_);
v___x_1021_ = lean_unbox(v___x_1011_);
lean_dec(v___x_1011_);
if (v___x_1021_ == 0)
{
uint8_t v___x_1022_; 
v___x_1022_ = 1;
v___y_1013_ = v___x_1022_;
goto v___jp_1012_;
}
else
{
v___y_1013_ = v___x_1010_;
goto v___jp_1012_;
}
v___jp_1012_:
{
uint8_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1014_ = 1;
v___x_1015_ = lean_box(v___x_1014_);
v___x_1016_ = lean_st_ref_put(v_finished_1005_, v___x_1015_);
lean_dec(v_finished_1005_);
v___x_1017_ = lean_box(v___y_1013_);
v___x_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1009_, v___x_1010_, v___x_1019_, v___f_1008_);
return v___x_1020_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1001_ = stack[0].m_obj;
lean_object* v_lose_1002_ = stack[1].m_obj;
lean_object* v___y_1003_ = stack[2].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_1001_, v_lose_1002_, v___y_1003_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(lean_object* v_w_1024_, lean_object* v_lose_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_1024_, v_lose_1025_, v___y_1026_);
lean_dec(v___y_1026_);
return v_res_1028_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_object* v_00_u03b1_1029_, lean_object* v_w_1030_, lean_object* v_lose_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_1030_, v_lose_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_1030_ = stack[1].m_obj;
lean_object* v_lose_1031_ = stack[2].m_obj;
lean_object* v___y_1032_ = stack[3].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(lean_box(0), v_w_1030_, v_lose_1031_, v___y_1032_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_1036_, lean_object* v_w_1037_, lean_object* v_lose_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_1036_, v_w_1037_, v_lose_1038_, v___y_1039_);
lean_dec(v___y_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(lean_object* v___y_1042_){
_start:
{
if (lean_obj_tag(v___y_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v___y_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___y_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___y_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___y_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_a_1051_ = lean_ctor_get(v___y_1042_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___y_1042_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1053_ = v___y_1042_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___y_1042_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_fst_1055_; lean_object* v___x_1057_; 
v_fst_1055_ = lean_ctor_get(v_a_1051_, 0);
lean_inc(v_fst_1055_);
lean_dec(v_a_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v_fst_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_fst_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(lean_object* v_mutex_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1063_ = lean_io_basemutex_unlock(v_mutex_1060_);
v___x_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1060_ = stack[0].m_obj;
lean_object* v_x_1061_ = stack[1].m_obj;
lean_object* v_res_1066_;
v_res_1066_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_mutex_1060_, v_x_1061_);
stack->m_obj
 = v_res_1066_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_1067_, lean_object* v_x_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_mutex_1067_, v_x_1068_);
lean_dec(v_x_1068_);
lean_dec(v_mutex_1067_);
return v_res_1070_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(lean_object* v_k_1071_, lean_object* v_ref_1072_, lean_object* v_x_1073_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
lean_dec(v_ref_1072_);
lean_dec_ref(v_k_1071_);
v_a_1075_ = lean_ctor_get(v_x_1073_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v_x_1073_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v_x_1073_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
else
{
lean_object* v___x_1084_; 
lean_dec_ref_known(v_x_1073_, 1);
v___x_1084_ = lean_apply_2(v_k_1071_, v_ref_1072_, lean_box(0));
return v___x_1084_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1071_ = stack[0].m_obj;
lean_object* v_ref_1072_ = stack[1].m_obj;
lean_object* v_x_1073_ = stack[2].m_obj;
lean_object* v_res_1085_;
v_res_1085_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_k_1071_, v_ref_1072_, v_x_1073_);
stack->m_obj
 = v_res_1085_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_k_1086_, lean_object* v_ref_1087_, lean_object* v_x_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_k_1086_, v_ref_1087_, v_x_1088_);
return v_res_1090_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(lean_object* v_mutex_1091_, lean_object* v___f_1092_){
_start:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = 0;
v___x_1096_ = lean_io_basemutex_lock(v_mutex_1091_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
v___x_1099_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1094_, v___x_1095_, v___x_1098_, v___f_1092_);
return v___x_1099_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1091_ = stack[0].m_obj;
lean_object* v___f_1092_ = stack[1].m_obj;
lean_object* v_res_1100_;
v_res_1100_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(v_mutex_1091_, v___f_1092_);
stack->m_obj
 = v_res_1100_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_1101_, lean_object* v___f_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(v_mutex_1101_, v___f_1102_);
lean_dec(v_mutex_1101_);
return v_res_1104_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(lean_object* v_mutex_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v_ref_1109_; lean_object* v_mutex_1110_; lean_object* v___f_1111_; lean_object* v___f_1112_; lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___y_1119_; 
v_ref_1109_ = lean_ctor_get(v_mutex_1106_, 0);
lean_inc(v_ref_1109_);
v_mutex_1110_ = lean_ctor_get(v_mutex_1106_, 1);
lean_inc_n(v_mutex_1110_, 2);
lean_dec_ref(v_mutex_1106_);
v___f_1111_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0));
v___f_1112_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1112_, 0, v_mutex_1110_);
v___f_1113_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1113_, 0, v_k_1107_);
lean_closure_set(v___f_1113_, 1, v_ref_1109_);
v___f_1114_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1114_, 0, v_mutex_1110_);
lean_closure_set(v___f_1114_, 1, v___f_1113_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = 0;
v___x_1117_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1114_, v___f_1112_, v___x_1115_, v___x_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1121_; 
v_a_1121_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1117_, 1);
if (lean_obj_tag(v_a_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v_a_1121_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_a_1121_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v_a_1121_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v_a_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v___y_1119_ = v___x_1127_;
goto v___jp_1118_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v_a_1130_ = lean_ctor_get(v_a_1121_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_a_1121_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v_a_1121_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v_a_1121_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_fst_1134_; lean_object* v___x_1136_; 
v_fst_1134_ = lean_ctor_get(v_a_1130_, 0);
lean_inc(v_fst_1134_);
lean_dec(v_a_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v_fst_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_fst_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
v___y_1119_ = v___x_1136_;
goto v___jp_1118_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1147_; 
v_a_1139_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1141_ = v___x_1117_;
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1117_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_task_map(v___f_1111_, v_a_1139_, v___x_1115_, v___x_1116_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1143_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
v___jp_1118_:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___y_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1106_ = stack[0].m_obj;
lean_object* v_k_1107_ = stack[1].m_obj;
lean_object* v_res_1148_;
v_res_1148_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1106_, v_k_1107_);
stack->m_obj
 = v_res_1148_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_1149_, lean_object* v_k_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1149_, v_k_1150_);
return v_res_1152_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_object* v_00_u03b1_1153_, lean_object* v_00_u03b2_1154_, lean_object* v_mutex_1155_, lean_object* v_k_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_1155_, v_k_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1155_ = stack[2].m_obj;
lean_object* v_k_1156_ = stack[3].m_obj;
lean_object* v_res_1159_;
v_res_1159_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(lean_box(0), lean_box(0), v_mutex_1155_, v_k_1156_);
stack->m_obj
 = v_res_1159_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_mutex_1162_, lean_object* v_k_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_1160_, v_00_u03b2_1161_, v_mutex_1162_, v_k_1163_);
return v_res_1165_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(lean_object* v_x_1166_){
_start:
{
if (lean_obj_tag(v_x_1166_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1176_; 
v_a_1168_ = lean_ctor_get(v_x_1166_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_x_1166_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1170_ = v_x_1166_;
v_isShared_1171_ = v_isSharedCheck_1176_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v_x_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1176_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1186_; 
v_a_1177_ = lean_ctor_get(v_x_1166_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_x_1166_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1179_ = v_x_1166_;
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v_x_1166_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_a_1177_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
return v___x_1184_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1166_ = stack[0].m_obj;
lean_object* v_res_1187_;
v_res_1187_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1166_);
stack->m_obj
 = v_res_1187_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(lean_object* v_x_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_1188_);
return v_res_1190_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(lean_object* v_x_1191_){
_start:
{
uint8_t v___y_1194_; 
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1206_; 
v_a_1198_ = lean_ctor_get(v_x_1191_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1200_ = v_x_1191_;
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v_x_1191_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v_values_1208_; uint8_t v_closed_1209_; uint8_t v___x_1210_; 
v_a_1207_ = lean_ctor_get(v_x_1191_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v_x_1191_, 1);
v_values_1208_ = lean_ctor_get(v_a_1207_, 0);
lean_inc_ref(v_values_1208_);
v_closed_1209_ = lean_ctor_get_uint8(v_a_1207_, sizeof(void*)*2);
lean_dec(v_a_1207_);
v___x_1210_ = l_Std_Queue_isEmpty___redArg(v_values_1208_);
lean_dec_ref(v_values_1208_);
if (v___x_1210_ == 0)
{
uint8_t v___x_1211_; 
v___x_1211_ = 1;
v___y_1194_ = v___x_1211_;
goto v___jp_1193_;
}
else
{
v___y_1194_ = v_closed_1209_;
goto v___jp_1193_;
}
}
v___jp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_box(v___y_1194_);
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1191_ = stack[0].m_obj;
lean_object* v_res_1212_;
v_res_1212_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1191_);
stack->m_obj
 = v_res_1212_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(lean_object* v_x_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_1213_);
return v_res_1215_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(lean_object* v___x_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1216_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1216_ = stack[0].m_obj;
lean_object* v___y_1217_ = stack[1].m_obj;
lean_object* v_res_1221_;
v_res_1221_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1216_, v___y_1217_);
stack->m_obj
 = v_res_1221_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_1222_, v___y_1223_);
lean_dec(v___y_1223_);
return v_res_1225_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(lean_object* v___y_1228_, lean_object* v_waiter_1229_, lean_object* v_x_1230_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_waiter_1229_);
v_a_1232_ = lean_ctor_get(v_x_1230_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_1230_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1234_ = v_x_1230_;
v_isShared_1235_ = v_isSharedCheck_1240_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v_x_1230_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1240_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
}
}
else
{
lean_object* v_a_1241_; uint8_t v___x_1242_; 
v_a_1241_ = lean_ctor_get(v_x_1230_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v_x_1230_, 1);
v___x_1242_ = lean_unbox(v_a_1241_);
lean_dec(v_a_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v_values_1244_; lean_object* v_consumers_1245_; uint8_t v_closed_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1257_; 
v___x_1243_ = lean_st_ref_take(v___y_1228_);
v_values_1244_ = lean_ctor_get(v___x_1243_, 0);
v_consumers_1245_ = lean_ctor_get(v___x_1243_, 1);
v_closed_1246_ = lean_ctor_get_uint8(v___x_1243_, sizeof(void*)*2);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1248_ = v___x_1243_;
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_consumers_1245_);
lean_inc(v_values_1244_);
lean_dec(v___x_1243_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1257_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1250_, 0, v_waiter_1229_);
v___x_1251_ = l_Std_Queue_enqueue___redArg(v___x_1250_, v_consumers_1245_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v___x_1251_);
v___x_1253_ = v___x_1248_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_values_1244_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v___x_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1256_, sizeof(void*)*2, v_closed_1246_);
v___x_1253_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_st_ref_put(v___y_1228_, v___x_1253_);
v___x_1255_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_1255_;
}
}
}
else
{
lean_object* v_lose_1258_; lean_object* v___x_1259_; 
v_lose_1258_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0));
v___x_1259_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_1229_, v_lose_1258_, v___y_1228_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1228_ = stack[0].m_obj;
lean_object* v_waiter_1229_ = stack[1].m_obj;
lean_object* v_x_1230_ = stack[2].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1228_, v_waiter_1229_, v_x_1230_);
stack->m_obj
 = v_res_1260_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(lean_object* v___y_1261_, lean_object* v_waiter_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_1261_, v_waiter_1262_, v_x_1263_);
lean_dec(v___y_1261_);
return v_res_1265_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(lean_object* v_waiter_1266_, lean_object* v___f_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___f_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_inc(v___y_1268_);
v___f_1270_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_1270_, 0, v___y_1268_);
lean_closure_set(v___f_1270_, 1, v_waiter_1266_);
v___x_1271_ = lean_unsigned_to_nat(0u);
v___x_1272_ = 0;
v___x_1273_ = lean_st_ref_get(v___y_1268_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
v___x_1276_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1271_, v___x_1272_, v___x_1275_, v___f_1267_);
v___x_1277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1271_, v___x_1272_, v___x_1276_, v___f_1270_);
return v___x_1277_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_1266_ = stack[0].m_obj;
lean_object* v___f_1267_ = stack[1].m_obj;
lean_object* v___y_1268_ = stack[2].m_obj;
lean_object* v_res_1278_;
v_res_1278_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v_waiter_1266_, v___f_1267_, v___y_1268_);
stack->m_obj
 = v_res_1278_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(lean_object* v_waiter_1279_, lean_object* v___f_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v_waiter_1279_, v___f_1280_, v___y_1281_);
lean_dec(v___y_1281_);
return v_res_1283_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(lean_object* v___f_1284_, lean_object* v_ch_1285_, lean_object* v_waiter_1286_){
_start:
{
lean_object* v___f_1288_; lean_object* v___x_1289_; 
v___f_1288_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_1288_, 0, v_waiter_1286_);
lean_closure_set(v___f_1288_, 1, v___f_1284_);
v___x_1289_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_1285_, v___f_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1284_ = stack[0].m_obj;
lean_object* v_ch_1285_ = stack[1].m_obj;
lean_object* v_waiter_1286_ = stack[2].m_obj;
lean_object* v_res_1290_;
v_res_1290_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1284_, v_ch_1285_, v_waiter_1286_);
stack->m_obj
 = v_res_1290_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(lean_object* v___f_1291_, lean_object* v_ch_1292_, lean_object* v_waiter_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_1291_, v_ch_1292_, v_waiter_1293_);
return v_res_1295_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(lean_object* v___y_1300_, lean_object* v___f_1301_, lean_object* v_x_1302_){
_start:
{
if (lean_obj_tag(v_x_1302_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v___f_1301_);
v_a_1304_ = lean_ctor_get(v_x_1302_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_x_1302_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1306_ = v_x_1302_;
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v_x_1302_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
}
}
else
{
lean_object* v_a_1313_; uint8_t v___x_1314_; 
v_a_1313_ = lean_ctor_get(v_x_1302_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v_x_1302_, 1);
v___x_1314_ = lean_unbox(v_a_1313_);
lean_dec(v_a_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref(v___f_1301_);
v___x_1315_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_1315_;
}
else
{
lean_object* v___x_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = 0;
v___x_1318_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_1300_);
v___x_1319_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1316_, v___x_1317_, v___x_1318_, v___f_1301_);
return v___x_1319_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1300_ = stack[0].m_obj;
lean_object* v___f_1301_ = stack[1].m_obj;
lean_object* v_x_1302_ = stack[2].m_obj;
lean_object* v_res_1320_;
v_res_1320_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1300_, v___f_1301_, v_x_1302_);
stack->m_obj
 = v_res_1320_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(lean_object* v___y_1321_, lean_object* v___f_1322_, lean_object* v_x_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_1321_, v___f_1322_, v_x_1323_);
lean_dec(v___y_1321_);
return v_res_1325_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(lean_object* v___f_1326_, lean_object* v___f_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___f_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_inc(v___y_1328_);
v___f_1330_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1330_, 0, v___y_1328_);
lean_closure_set(v___f_1330_, 1, v___f_1326_);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = 0;
v___x_1333_ = lean_st_ref_get(v___y_1328_);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
v___x_1336_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1331_, v___x_1332_, v___x_1335_, v___f_1327_);
v___x_1337_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1331_, v___x_1332_, v___x_1336_, v___f_1330_);
return v___x_1337_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1326_ = stack[0].m_obj;
lean_object* v___f_1327_ = stack[1].m_obj;
lean_object* v___y_1328_ = stack[2].m_obj;
lean_object* v_res_1338_;
v_res_1338_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1326_, v___f_1327_, v___y_1328_);
stack->m_obj
 = v_res_1338_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(lean_object* v___f_1339_, lean_object* v___f_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_1339_, v___f_1340_, v___y_1341_);
lean_dec(v___y_1341_);
return v_res_1343_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(lean_object* v_values_1344_, uint8_t v_closed_1345_, lean_object* v___y_1346_, lean_object* v_x_1347_){
_start:
{
if (lean_obj_tag(v_x_1347_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_values_1344_);
v_a_1349_ = lean_ctor_get(v_x_1347_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_x_1347_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1351_ = v_x_1347_;
v_isShared_1352_ = v_isSharedCheck_1357_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v_x_1347_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1357_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_a_1358_ = lean_ctor_get(v_x_1347_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v_x_1347_, 1);
v___x_1359_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1359_, 0, v_values_1344_);
lean_ctor_set(v___x_1359_, 1, v_a_1358_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*2, v_closed_1345_);
v___x_1360_ = lean_st_ref_swap(v___y_1346_, v___x_1359_);
lean_dec(v___x_1360_);
v___x_1361_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_1361_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_values_1344_ = stack[0].m_obj;
uint8_t v_closed_1345_ = stack[1].m_num;
lean_object* v___y_1346_ = stack[2].m_obj;
lean_object* v_x_1347_ = stack[3].m_obj;
lean_object* v_res_1362_;
v_res_1362_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_1344_, v_closed_1345_, v___y_1346_, v_x_1347_);
stack->m_obj
 = v_res_1362_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(lean_object* v_values_1363_, lean_object* v_closed_1364_, lean_object* v___y_1365_, lean_object* v_x_1366_, lean_object* v___y_1367_){
_start:
{
uint8_t v_closed_boxed_1368_; lean_object* v_res_1369_; 
v_closed_boxed_1368_ = lean_unbox(v_closed_1364_);
v_res_1369_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_1363_, v_closed_boxed_1368_, v___y_1365_, v_x_1366_);
lean_dec(v___y_1365_);
return v_res_1369_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_1370_){
_start:
{
if (lean_obj_tag(v_x_1370_) == 0)
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v_x_1370_);
return v___x_1372_;
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1382_; 
v_a_1373_ = lean_ctor_get(v_x_1370_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_x_1370_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1375_ = v_x_1370_;
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v_x_1370_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = l_List_reverse___redArg(v_a_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1370_ = stack[0].m_obj;
lean_object* v_res_1383_;
v_res_1383_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_1370_);
stack->m_obj
 = v_res_1383_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_1384_);
return v_res_1386_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_1387_, lean_object* v___x_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v___x_1388_);
lean_dec(v_a_1387_);
v_a_1391_ = lean_ctor_get(v_x_1389_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1393_ = v_x_1389_;
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v_x_1389_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1399_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1416_; 
v_a_1400_ = lean_ctor_get(v_x_1389_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1402_ = v_x_1389_;
v_isShared_1403_ = v_isSharedCheck_1416_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v_x_1389_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1416_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
uint8_t v___x_1404_; 
v___x_1404_ = l_List_isEmpty___redArg(v_a_1387_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_dec(v___x_1388_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_a_1400_);
lean_ctor_set(v___x_1405_, 1, v_a_1387_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1405_);
v___x_1407_ = v___x_1402_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec(v_a_1387_);
v___x_1410_ = l_List_reverse___redArg(v_a_1400_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1388_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1411_);
v___x_1413_ = v___x_1402_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1387_ = stack[0].m_obj;
lean_object* v___x_1388_ = stack[1].m_obj;
lean_object* v_x_1389_ = stack[2].m_obj;
lean_object* v_res_1417_;
v_res_1417_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_1387_, v___x_1388_, v_x_1389_);
stack->m_obj
 = v_res_1417_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_1418_, lean_object* v___x_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_1418_, v___x_1419_, v_x_1420_);
return v_res_1422_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(lean_object* v_x_1423_){
_start:
{
uint8_t v___y_1426_; 
if (lean_obj_tag(v_x_1423_) == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_x_1423_);
return v___x_1430_;
}
else
{
lean_object* v_a_1431_; uint8_t v___x_1432_; 
v_a_1431_ = lean_ctor_get(v_x_1423_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v_x_1423_, 1);
v___x_1432_ = lean_unbox(v_a_1431_);
lean_dec(v_a_1431_);
if (v___x_1432_ == 0)
{
uint8_t v___x_1433_; 
v___x_1433_ = 1;
v___y_1426_ = v___x_1433_;
goto v___jp_1425_;
}
else
{
uint8_t v___x_1434_; 
v___x_1434_ = 0;
v___y_1426_ = v___x_1434_;
goto v___jp_1425_;
}
}
v___jp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = lean_box(v___y_1426_);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1423_ = stack[0].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1423_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(lean_object* v_x_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_tail_1439_, lean_object* v_x_1440_, lean_object* v_head_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1439_, v_x_1440_, v_head_1441_, v_x_1442_);
return v_res_1444_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(lean_object* v_x_1451_, lean_object* v_x_1452_){
_start:
{
if (lean_obj_tag(v_x_1451_) == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_x_1452_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v_head_1456_; lean_object* v_tail_1457_; lean_object* v___f_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_head_1456_ = lean_ctor_get(v_x_1451_, 0);
lean_inc_n(v_head_1456_, 2);
v_tail_1457_ = lean_ctor_get(v_x_1451_, 1);
lean_inc(v_tail_1457_);
lean_dec_ref_known(v_x_1451_, 2);
v___f_1458_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1458_, 0, v_tail_1457_);
lean_closure_set(v___f_1458_, 1, v_x_1452_);
lean_closure_set(v___f_1458_, 2, v_head_1456_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v___x_1460_ = 0;
if (lean_obj_tag(v_head_1456_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref_known(v_head_1456_, 1);
v___x_1461_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_1462_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1459_, v___x_1460_, v___x_1461_, v___f_1458_);
return v___x_1462_;
}
else
{
lean_object* v_finished_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1476_; 
v_finished_1463_ = lean_ctor_get(v_head_1456_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_head_1456_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1465_ = v_head_1456_;
v_isShared_1466_ = v_isSharedCheck_1476_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_finished_1463_);
lean_dec(v_head_1456_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1476_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_finished_1467_; lean_object* v___f_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v_finished_1467_ = lean_ctor_get(v_finished_1463_, 0);
lean_inc(v_finished_1467_);
lean_dec_ref(v_finished_1463_);
v___f_1468_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_1469_ = lean_st_ref_get(v_finished_1467_);
lean_dec(v_finished_1467_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1469_);
v___x_1471_ = v___x_1465_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
v___x_1473_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1459_, v___x_1460_, v___x_1472_, v___f_1468_);
v___x_1474_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1459_, v___x_1460_, v___x_1473_, v___f_1458_);
return v___x_1474_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1451_ = stack[0].m_obj;
lean_object* v_x_1452_ = stack[1].m_obj;
lean_object* v_res_1477_;
v_res_1477_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1451_, v_x_1452_);
stack->m_obj
 = v_res_1477_;
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(lean_object* v_tail_1478_, lean_object* v_x_1479_, lean_object* v_head_1480_, lean_object* v_x_1481_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v_head_1480_);
lean_dec(v_x_1479_);
lean_dec(v_tail_1478_);
v_a_1483_ = lean_ctor_get(v_x_1481_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1481_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1485_ = v_x_1481_;
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v_x_1481_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
}
}
else
{
lean_object* v_a_1492_; uint8_t v___x_1493_; 
v_a_1492_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1493_ = lean_unbox(v_a_1492_);
lean_dec(v_a_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
lean_dec_ref(v_head_1480_);
v___x_1494_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1478_, v_x_1479_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_head_1480_);
lean_ctor_set(v___x_1495_, 1, v_x_1479_);
v___x_1496_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_1478_, v___x_1495_);
return v___x_1496_;
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_1478_ = stack[0].m_obj;
lean_object* v_x_1479_ = stack[1].m_obj;
lean_object* v_head_1480_ = stack[2].m_obj;
lean_object* v_x_1481_ = stack[3].m_obj;
lean_object* v_res_1497_;
v_res_1497_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_1478_, v_x_1479_, v_head_1480_, v_x_1481_);
stack->m_obj
 = v_res_1497_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1498_, v_x_1499_);
return v_res_1501_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(lean_object* v___x_1502_, lean_object* v_eList_1503_, lean_object* v___f_1504_, lean_object* v_x_1505_){
_start:
{
if (lean_obj_tag(v_x_1505_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v___f_1504_);
lean_dec(v_eList_1503_);
lean_dec(v___x_1502_);
v_a_1507_ = lean_ctor_get(v_x_1505_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_x_1505_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1509_ = v_x_1505_;
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v_x_1505_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___f_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1516_ = lean_ctor_get(v_x_1505_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v_x_1505_, 1);
lean_inc(v___x_1502_);
v___f_1517_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1517_, 0, v_a_1516_);
lean_closure_set(v___f_1517_, 1, v___x_1502_);
v___x_1518_ = lean_unsigned_to_nat(0u);
v___x_1519_ = 0;
v___x_1520_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_1503_, v___x_1502_);
v___x_1521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1518_, v___x_1519_, v___x_1520_, v___f_1504_);
v___x_1522_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1518_, v___x_1519_, v___x_1521_, v___f_1517_);
return v___x_1522_;
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1502_ = stack[0].m_obj;
lean_object* v_eList_1503_ = stack[1].m_obj;
lean_object* v___f_1504_ = stack[2].m_obj;
lean_object* v_x_1505_ = stack[3].m_obj;
lean_object* v_res_1523_;
v_res_1523_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v___x_1502_, v_eList_1503_, v___f_1504_, v_x_1505_);
stack->m_obj
 = v_res_1523_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v___x_1524_, lean_object* v_eList_1525_, lean_object* v___f_1526_, lean_object* v_x_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v___x_1524_, v_eList_1525_, v___f_1526_, v_x_1527_);
return v_res_1529_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(lean_object* v_q_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_eList_1534_; lean_object* v_dList_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; lean_object* v___f_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_eList_1534_ = lean_ctor_get(v_q_1531_, 0);
lean_inc(v_eList_1534_);
v_dList_1535_ = lean_ctor_get(v_q_1531_, 1);
lean_inc(v_dList_1535_);
lean_dec_ref(v_q_1531_);
v___f_1536_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_1537_ = lean_box(0);
v___f_1538_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1538_, 0, v___x_1537_);
lean_closure_set(v___f_1538_, 1, v_eList_1534_);
lean_closure_set(v___f_1538_, 2, v___f_1536_);
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = 0;
v___x_1541_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_1535_, v___x_1537_);
v___x_1542_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1539_, v___x_1540_, v___x_1541_, v___f_1536_);
v___x_1543_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1539_, v___x_1540_, v___x_1542_, v___f_1538_);
return v___x_1543_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_1531_ = stack[0].m_obj;
lean_object* v___y_1532_ = stack[1].m_obj;
lean_object* v_res_1544_;
v_res_1544_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1531_, v___y_1532_);
stack->m_obj
 = v_res_1544_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(lean_object* v_q_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1545_, v___y_1546_);
lean_dec(v___y_1546_);
return v_res_1548_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(lean_object* v___y_1549_, lean_object* v_x_1550_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
v_a_1552_ = lean_ctor_get(v_x_1550_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_x_1550_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1554_ = v_x_1550_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v_x_1550_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v_values_1562_; lean_object* v_consumers_1563_; uint8_t v_closed_1564_; lean_object* v___x_1565_; lean_object* v___f_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1561_ = lean_ctor_get(v_x_1550_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v_x_1550_, 1);
v_values_1562_ = lean_ctor_get(v_a_1561_, 0);
lean_inc_ref(v_values_1562_);
v_consumers_1563_ = lean_ctor_get(v_a_1561_, 1);
lean_inc_ref(v_consumers_1563_);
v_closed_1564_ = lean_ctor_get_uint8(v_a_1561_, sizeof(void*)*2);
lean_dec(v_a_1561_);
v___x_1565_ = lean_box(v_closed_1564_);
lean_inc(v___y_1549_);
v___f_1566_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1566_, 0, v_values_1562_);
lean_closure_set(v___f_1566_, 1, v___x_1565_);
lean_closure_set(v___f_1566_, 2, v___y_1549_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = 0;
v___x_1569_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_1563_, v___y_1549_);
v___x_1570_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1567_, v___x_1568_, v___x_1569_, v___f_1566_);
return v___x_1570_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1549_ = stack[0].m_obj;
lean_object* v_x_1550_ = stack[1].m_obj;
lean_object* v_res_1571_;
v_res_1571_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1549_, v_x_1550_);
stack->m_obj
 = v_res_1571_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(lean_object* v___y_1572_, lean_object* v_x_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_1572_, v_x_1573_);
lean_dec(v___y_1572_);
return v_res_1575_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(lean_object* v___y_1576_){
_start:
{
lean_object* v___f_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_inc(v___y_1576_);
v___f_1578_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_1578_, 0, v___y_1576_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = 0;
v___x_1581_ = lean_st_ref_get(v___y_1576_);
v___x_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
v___x_1584_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1579_, v___x_1580_, v___x_1583_, v___f_1578_);
return v___x_1584_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1576_ = stack[0].m_obj;
lean_object* v_res_1585_;
v_res_1585_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1576_);
stack->m_obj
 = v_res_1585_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_1586_);
lean_dec(v___y_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(lean_object* v_ch_1595_){
_start:
{
lean_object* v___f_1596_; lean_object* v___f_1597_; lean_object* v___f_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___f_1596_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1));
lean_inc_ref_n(v_ch_1595_, 2);
v___f_1597_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_1597_, 0, v___f_1596_);
lean_closure_set(v___f_1597_, 1, v_ch_1595_);
v___f_1598_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2));
v___f_1599_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3));
v___x_1600_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1600_, 0, lean_box(0));
lean_closure_set(v___x_1600_, 1, lean_box(0));
lean_closure_set(v___x_1600_, 2, v_ch_1595_);
lean_closure_set(v___x_1600_, 3, v___f_1598_);
v___x_1601_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_1601_, 0, lean_box(0));
lean_closure_set(v___x_1601_, 1, lean_box(0));
lean_closure_set(v___x_1601_, 2, v_ch_1595_);
lean_closure_set(v___x_1601_, 3, v___f_1599_);
v___x_1602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1600_);
lean_ctor_set(v___x_1602_, 1, v___f_1597_);
lean_ctor_set(v___x_1602_, 2, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(lean_object* v_00_u03b1_1603_, lean_object* v_ch_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_1604_);
return v___x_1605_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_object* v_00_u03b1_1606_, lean_object* v_q_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_1607_, v___y_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_1607_ = stack[1].m_obj;
lean_object* v___y_1608_ = stack[2].m_obj;
lean_object* v_res_1611_;
v_res_1611_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(lean_box(0), v_q_1607_, v___y_1608_);
stack->m_obj
 = v_res_1611_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_q_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_1612_, v_q_1613_, v___y_1614_);
lean_dec(v___y_1614_);
return v_res_1616_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_object* v_00_u03b1_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_1618_, v_x_1619_);
return v___x_1622_;
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1618_ = stack[1].m_obj;
lean_object* v_x_1619_ = stack[2].m_obj;
lean_object* v___y_1620_ = stack[3].m_obj;
lean_object* v_res_1623_;
v_res_1623_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(lean_box(0), v_x_1618_, v_x_1619_, v___y_1620_);
stack->m_obj
 = v_res_1623_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_1624_, v_x_1625_, v_x_1626_, v___y_1627_);
lean_dec(v___y_1627_);
return v_res_1629_;
}
}
static lean_object* _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0(void){
_start:
{
uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = 0;
v___x_1631_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_1632_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*2, v___x_1630_);
return v___x_1632_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg(){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0);
v___x_1635_ = l_Std_Mutex_new___redArg(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1636_;
v_res_1636_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
stack->m_obj
 = v_res_1636_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v_res_1638_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_object* v_00_u03b1_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
return v___x_1641_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1642_;
v_res_1642_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(lean_box(0));
stack->m_obj
 = v_res_1642_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_1643_);
return v_res_1645_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(lean_object* v_v_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v_producers_1660_; lean_object* v_consumers_1661_; uint8_t v_closed_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1684_; 
v___x_1658_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0));
v___x_1659_ = lean_st_ref_get(v___y_1656_);
v_producers_1660_ = lean_ctor_get(v___x_1659_, 0);
v_consumers_1661_ = lean_ctor_get(v___x_1659_, 1);
v_closed_1662_ = lean_ctor_get_uint8(v___x_1659_, sizeof(void*)*2);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1664_ = v___x_1659_;
v_isShared_1665_ = v_isSharedCheck_1684_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_consumers_1661_);
lean_inc(v_producers_1660_);
lean_dec(v___x_1659_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1684_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_1661_);
if (lean_obj_tag(v___x_1666_) == 1)
{
lean_object* v_val_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1682_; 
v_val_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1682_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_val_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1682_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v_fst_1671_; lean_object* v_snd_1672_; lean_object* v___x_1674_; 
v_fst_1671_ = lean_ctor_get(v_val_1667_, 0);
lean_inc(v_fst_1671_);
v_snd_1672_ = lean_ctor_get(v_val_1667_, 1);
lean_inc(v_snd_1672_);
lean_dec(v_val_1667_);
lean_inc(v_v_1655_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_v_1655_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_v_1655_);
v___x_1674_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
uint8_t v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_fst_1671_, v___x_1674_);
lean_dec(v_fst_1671_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v_snd_1672_);
v___x_1677_ = v___x_1664_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_producers_1660_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_snd_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1680_, sizeof(void*)*2, v_closed_1662_);
v___x_1677_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_st_ref_swap(v___y_1656_, v___x_1677_);
lean_dec(v___x_1678_);
if (v___x_1675_ == 0)
{
goto _start;
}
else
{
lean_dec(v_v_1655_);
return v___x_1658_;
}
}
}
}
}
else
{
lean_object* v___x_1683_; 
lean_dec(v___x_1666_);
lean_del_object(v___x_1664_);
lean_dec_ref(v_producers_1660_);
lean_dec(v_v_1655_);
v___x_1683_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2));
return v___x_1683_;
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1655_ = stack[0].m_obj;
lean_object* v___y_1656_ = stack[1].m_obj;
lean_object* v_res_1685_;
v_res_1685_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1655_, v___y_1656_);
stack->m_obj
 = v_res_1685_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(lean_object* v_v_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1686_, v___y_1687_);
lean_dec(v___y_1687_);
return v_res_1689_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(lean_object* v_v_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v___x_1693_; lean_object* v_fst_1694_; 
v___x_1693_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1690_, v_a_1691_);
v_fst_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_fst_1694_);
lean_dec_ref(v___x_1693_);
if (lean_obj_tag(v_fst_1694_) == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = 1;
return v___x_1695_;
}
else
{
lean_object* v_val_1696_; uint8_t v___x_1697_; 
v_val_1696_ = lean_ctor_get(v_fst_1694_, 0);
lean_inc(v_val_1696_);
lean_dec_ref_known(v_fst_1694_, 1);
v___x_1697_ = lean_unbox(v_val_1696_);
lean_dec(v_val_1696_);
return v___x_1697_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1690_ = stack[0].m_obj;
lean_object* v_a_1691_ = stack[1].m_obj;
uint8_t v_res_1698_;
v_res_1698_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1690_, v_a_1691_);
stack->m_num = v_res_1698_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(lean_object* v_v_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
uint8_t v_res_1702_; lean_object* v_r_1703_; 
v_res_1702_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1699_, v_a_1700_);
lean_dec(v_a_1700_);
v_r_1703_ = lean_box(v_res_1702_);
return v_r_1703_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_object* v_00_u03b1_1704_, lean_object* v_v_1705_, lean_object* v_a_1706_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1705_, v_a_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1705_ = stack[1].m_obj;
lean_object* v_a_1706_ = stack[2].m_obj;
uint8_t v_res_1709_;
v_res_1709_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(lean_box(0), v_v_1705_, v_a_1706_);
stack->m_num = v_res_1709_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(lean_object* v_00_u03b1_1710_, lean_object* v_v_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
uint8_t v_res_1714_; lean_object* v_r_1715_; 
v_res_1714_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(v_00_u03b1_1710_, v_v_1711_, v_a_1712_);
lean_dec(v_a_1712_);
v_r_1715_ = lean_box(v_res_1714_);
return v_r_1715_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_object* v_00_u03b1_1716_, lean_object* v_v_1717_, lean_object* v_inst_1718_, lean_object* v_a_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_1717_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1717_ = stack[1].m_obj;
lean_object* v_a_1719_ = stack[3].m_obj;
lean_object* v___y_1720_ = stack[4].m_obj;
lean_object* v_res_1723_;
v_res_1723_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(lean_box(0), v_v_1717_, lean_box(0), v_a_1719_, v___y_1720_);
stack->m_obj
 = v_res_1723_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_v_1725_, lean_object* v_inst_1726_, lean_object* v_a_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_1724_, v_v_1725_, v_inst_1726_, v_a_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1730_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(lean_object* v_v_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; uint8_t v_closed_1735_; 
v___x_1734_ = lean_st_ref_get(v___y_1732_);
v_closed_1735_ = lean_ctor_get_uint8(v___x_1734_, sizeof(void*)*2);
lean_dec(v___x_1734_);
if (v_closed_1735_ == 0)
{
uint8_t v___x_1736_; 
v___x_1736_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1731_, v___y_1732_);
return v___x_1736_;
}
else
{
uint8_t v___x_1737_; 
lean_dec(v_v_1731_);
v___x_1737_ = 0;
return v___x_1737_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1731_ = stack[0].m_obj;
lean_object* v___y_1732_ = stack[1].m_obj;
uint8_t v_res_1738_;
v_res_1738_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1731_, v___y_1732_);
stack->m_num = v_res_1738_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(lean_object* v_v_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v_res_1742_; lean_object* v_r_1743_; 
v_res_1742_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(v_v_1739_, v___y_1740_);
lean_dec(v___y_1740_);
v_r_1743_ = lean_box(v_res_1742_);
return v_r_1743_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(lean_object* v_ch_1744_, lean_object* v_v_1745_){
_start:
{
lean_object* v___f_1747_; lean_object* v___x_1748_; 
v___f_1747_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1747_, 0, v_v_1745_);
v___x_1748_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1744_, v___f_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1744_ = stack[0].m_obj;
lean_object* v_v_1745_ = stack[1].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1744_, v_v_1745_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(lean_object* v_ch_1750_, lean_object* v_v_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1750_, v_v_1751_);
return v_res_1753_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_object* v_00_u03b1_1754_, lean_object* v_ch_1755_, lean_object* v_v_1756_){
_start:
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_1755_, v_v_1756_);
v___x_1759_ = lean_unbox(v___x_1758_);
lean_dec(v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1755_ = stack[1].m_obj;
lean_object* v_v_1756_ = stack[2].m_obj;
uint8_t v_res_1760_;
v_res_1760_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(lean_box(0), v_ch_1755_, v_v_1756_);
stack->m_num = v_res_1760_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_ch_1762_, lean_object* v_v_1763_, lean_object* v_a_1764_){
_start:
{
uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_res_1765_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(v_00_u03b1_1761_, v_ch_1762_, v_v_1763_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(lean_object* v_x_1767_){
_start:
{
if (lean_obj_tag(v_x_1767_) == 0)
{
goto v___jp_1768_;
}
else
{
lean_object* v_val_1770_; uint8_t v___x_1771_; 
v_val_1770_ = lean_ctor_get(v_x_1767_, 0);
v___x_1771_ = lean_unbox(v_val_1770_);
if (v___x_1771_ == 0)
{
goto v___jp_1768_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2));
return v___x_1772_;
}
}
v___jp_1768_:
{
lean_object* v___x_1769_; 
v___x_1769_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0));
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(lean_object* v_x_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_1773_);
lean_dec(v_x_1773_);
return v_res_1774_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(lean_object* v_v_1775_, lean_object* v___f_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; uint8_t v_closed_1780_; 
v___x_1779_ = lean_st_ref_get(v___y_1777_);
v_closed_1780_ = lean_ctor_get_uint8(v___x_1779_, sizeof(void*)*2);
lean_dec(v___x_1779_);
if (v_closed_1780_ == 0)
{
uint8_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = 1;
lean_inc(v_v_1775_);
v___x_1782_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_1775_, v___y_1777_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v_producers_1785_; lean_object* v_consumers_1786_; uint8_t v_closed_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1800_; 
v___x_1783_ = lean_io_promise_new();
v___x_1784_ = lean_st_ref_take(v___y_1777_);
v_producers_1785_ = lean_ctor_get(v___x_1784_, 0);
v_consumers_1786_ = lean_ctor_get(v___x_1784_, 1);
v_closed_1787_ = lean_ctor_get_uint8(v___x_1784_, sizeof(void*)*2);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1789_ = v___x_1784_;
v_isShared_1790_ = v_isSharedCheck_1800_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_consumers_1786_);
lean_inc(v_producers_1785_);
lean_dec(v___x_1784_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1800_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_inc(v___x_1783_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_v_1775_);
lean_ctor_set(v___x_1791_, 1, v___x_1783_);
v___x_1792_ = l_Std_Queue_enqueue___redArg(v___x_1791_, v_producers_1785_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1792_);
v___x_1794_ = v___x_1789_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_consumers_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1799_, sizeof(void*)*2, v_closed_1787_);
v___x_1794_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1795_ = lean_st_ref_put(v___y_1777_, v___x_1794_);
v___x_1796_ = lean_io_promise_result_opt(v___x_1783_);
lean_dec(v___x_1783_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_task_map(v___f_1776_, v___x_1796_, v___x_1797_, v___x_1781_);
return v___x_1798_;
}
}
}
else
{
lean_object* v___x_1801_; 
lean_dec_ref(v___f_1776_);
lean_dec(v_v_1775_);
v___x_1801_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_1801_;
}
}
else
{
lean_object* v___x_1802_; 
lean_dec_ref(v___f_1776_);
lean_dec(v_v_1775_);
v___x_1802_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_1802_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1775_ = stack[0].m_obj;
lean_object* v___f_1776_ = stack[1].m_obj;
lean_object* v___y_1777_ = stack[2].m_obj;
lean_object* v_res_1803_;
v_res_1803_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1775_, v___f_1776_, v___y_1777_);
stack->m_obj
 = v_res_1803_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(lean_object* v_v_1804_, lean_object* v___f_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(v_v_1804_, v___f_1805_, v___y_1806_);
lean_dec(v___y_1806_);
return v_res_1808_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(lean_object* v_ch_1810_, lean_object* v_v_1811_){
_start:
{
lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; 
v___f_1813_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0));
v___f_1814_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1814_, 0, v_v_1811_);
lean_closure_set(v___f_1814_, 1, v___f_1813_);
v___x_1815_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1810_, v___f_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1810_ = stack[0].m_obj;
lean_object* v_v_1811_ = stack[1].m_obj;
lean_object* v_res_1816_;
v_res_1816_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1810_, v_v_1811_);
stack->m_obj
 = v_res_1816_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(lean_object* v_ch_1817_, lean_object* v_v_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1817_, v_v_1818_);
return v_res_1820_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_object* v_00_u03b1_1821_, lean_object* v_ch_1822_, lean_object* v_v_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_1822_, v_v_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1822_ = stack[1].m_obj;
lean_object* v_v_1823_ = stack[2].m_obj;
lean_object* v_res_1826_;
v_res_1826_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(lean_box(0), v_ch_1822_, v_v_1823_);
stack->m_obj
 = v_res_1826_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(lean_object* v_00_u03b1_1827_, lean_object* v_ch_1828_, lean_object* v_v_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(v_00_u03b1_1827_, v_ch_1828_, v_v_1829_);
return v_res_1831_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(lean_object* v_as_1832_, size_t v_sz_1833_, size_t v_i_1834_, lean_object* v_b_1835_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_usize_dec_lt(v_i_1834_, v_sz_1833_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_b_1835_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v_a_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; size_t v___x_1843_; size_t v___x_1844_; 
v___x_1839_ = lean_box(0);
v_a_1840_ = lean_array_uget_borrowed(v_as_1832_, v_i_1834_);
v___x_1841_ = lean_box(0);
v___x_1842_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_1840_, v___x_1841_);
v___x_1843_ = ((size_t)1ULL);
v___x_1844_ = lean_usize_add(v_i_1834_, v___x_1843_);
v_i_1834_ = v___x_1844_;
v_b_1835_ = v___x_1839_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1832_ = stack[0].m_obj;
size_t v_sz_1833_ = stack[1].m_num;
size_t v_i_1834_ = stack[2].m_num;
lean_object* v_b_1835_ = stack[3].m_obj;
lean_object* v_res_1846_;
v_res_1846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1832_, v_sz_1833_, v_i_1834_, v_b_1835_);
stack->m_obj
 = v_res_1846_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(lean_object* v_as_1847_, lean_object* v_sz_1848_, lean_object* v_i_1849_, lean_object* v_b_1850_, lean_object* v___y_1851_){
_start:
{
size_t v_sz_boxed_1852_; size_t v_i_boxed_1853_; lean_object* v_res_1854_; 
v_sz_boxed_1852_ = lean_unbox_usize(v_sz_1848_);
lean_dec(v_sz_1848_);
v_i_boxed_1853_ = lean_unbox_usize(v_i_1849_);
lean_dec(v_i_1849_);
v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1847_, v_sz_boxed_1852_, v_i_boxed_1853_, v_b_1850_);
lean_dec_ref(v_as_1847_);
return v_res_1854_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; uint8_t v_closed_1858_; 
v___x_1857_ = lean_st_ref_get(v___y_1855_);
v_closed_1858_ = lean_ctor_get_uint8(v___x_1857_, sizeof(void*)*2);
if (v_closed_1858_ == 0)
{
lean_object* v_producers_1859_; lean_object* v_consumers_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1883_; 
v_producers_1859_ = lean_ctor_get(v___x_1857_, 0);
v_consumers_1860_ = lean_ctor_get(v___x_1857_, 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1862_ = v___x_1857_;
v_isShared_1863_ = v_isSharedCheck_1883_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_consumers_1860_);
lean_inc(v_producers_1859_);
lean_dec(v___x_1857_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1883_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; size_t v_sz_1866_; size_t v___x_1867_; lean_object* v___x_1868_; 
v___x_1864_ = l_Std_Queue_toArray___redArg(v_consumers_1860_);
v___x_1865_ = lean_box(0);
v_sz_1866_ = lean_array_size(v___x_1864_);
v___x_1867_ = ((size_t)0ULL);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_1864_, v_sz_1866_, v___x_1867_, v___x_1865_);
lean_dec_ref(v___x_1864_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1881_; 
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; 
v_unused_1882_ = lean_ctor_get(v___x_1868_, 0);
lean_dec(v_unused_1882_);
v___x_1870_ = v___x_1868_;
v_isShared_1871_ = v_isSharedCheck_1881_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v___x_1868_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1881_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; uint8_t v___x_1873_; lean_object* v___x_1875_; 
v___x_1872_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_1873_ = 1;
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___x_1872_);
v___x_1875_ = v___x_1862_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_producers_1859_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1872_);
v___x_1875_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*2, v___x_1873_);
v___x_1876_ = lean_st_ref_swap(v___y_1855_, v___x_1875_);
lean_dec(v___x_1876_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1865_);
v___x_1878_ = v___x_1870_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1865_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_del_object(v___x_1862_);
lean_dec_ref(v_producers_1859_);
return v___x_1868_;
}
}
}
else
{
uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v___x_1857_);
v___x_1884_ = 1;
v___x_1885_ = lean_box(v___x_1884_);
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1855_ = stack[0].m_obj;
lean_object* v_res_1887_;
v_res_1887_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1855_);
stack->m_obj
 = v_res_1887_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(v___y_1888_);
lean_dec(v___y_1888_);
return v_res_1890_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(lean_object* v_ch_1892_){
_start:
{
lean_object* v___f_1894_; lean_object* v___x_1895_; 
v___f_1894_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0));
v___x_1895_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_1892_, v___f_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1892_ = stack[0].m_obj;
lean_object* v_res_1896_;
v_res_1896_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1892_);
stack->m_obj
 = v_res_1896_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(lean_object* v_ch_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1897_);
return v_res_1899_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_object* v_00_u03b1_1900_, lean_object* v_ch_1901_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1901_ = stack[1].m_obj;
lean_object* v_res_1904_;
v_res_1904_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(lean_box(0), v_ch_1901_);
stack->m_obj
 = v_res_1904_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(lean_object* v_00_u03b1_1905_, lean_object* v_ch_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(v_00_u03b1_1905_, v_ch_1906_);
return v_res_1908_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_object* v_00_u03b1_1909_, lean_object* v_as_1910_, size_t v_sz_1911_, size_t v_i_1912_, lean_object* v_b_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_1910_, v_sz_1911_, v_i_1912_, v_b_1913_);
return v___x_1916_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1910_ = stack[1].m_obj;
size_t v_sz_1911_ = stack[2].m_num;
size_t v_i_1912_ = stack[3].m_num;
lean_object* v_b_1913_ = stack[4].m_obj;
lean_object* v___y_1914_ = stack[5].m_obj;
lean_object* v_res_1917_;
v_res_1917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(lean_box(0), v_as_1910_, v_sz_1911_, v_i_1912_, v_b_1913_, v___y_1914_);
stack->m_obj
 = v_res_1917_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_as_1919_, lean_object* v_sz_1920_, lean_object* v_i_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
size_t v_sz_boxed_1925_; size_t v_i_boxed_1926_; lean_object* v_res_1927_; 
v_sz_boxed_1925_ = lean_unbox_usize(v_sz_1920_);
lean_dec(v_sz_1920_);
v_i_boxed_1926_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_1918_, v_as_1919_, v_sz_boxed_1925_, v_i_boxed_1926_, v_b_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v_as_1919_);
return v_res_1927_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; uint8_t v_closed_1931_; 
v___x_1930_ = lean_st_ref_get(v___y_1928_);
v_closed_1931_ = lean_ctor_get_uint8(v___x_1930_, sizeof(void*)*2);
lean_dec(v___x_1930_);
return v_closed_1931_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1928_ = stack[0].m_obj;
uint8_t v_res_1932_;
v_res_1932_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1928_);
stack->m_num = v_res_1932_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v_res_1935_; lean_object* v_r_1936_; 
v_res_1935_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(v___y_1933_);
lean_dec(v___y_1933_);
v_r_1936_ = lean_box(v_res_1935_);
return v_r_1936_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(lean_object* v_ch_1938_){
_start:
{
lean_object* v___f_1940_; lean_object* v___x_1941_; 
v___f_1940_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0));
v___x_1941_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_1938_, v___f_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1938_ = stack[0].m_obj;
lean_object* v_res_1942_;
v_res_1942_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1938_);
stack->m_obj
 = v_res_1942_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(lean_object* v_ch_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1943_);
return v_res_1945_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_object* v_00_u03b1_1946_, lean_object* v_ch_1947_){
_start:
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_1947_);
v___x_1950_ = lean_unbox(v___x_1949_);
lean_dec(v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1947_ = stack[1].m_obj;
uint8_t v_res_1951_;
v_res_1951_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(lean_box(0), v_ch_1947_);
stack->m_num = v_res_1951_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_ch_1953_, lean_object* v_a_1954_){
_start:
{
uint8_t v_res_1955_; lean_object* v_r_1956_; 
v_res_1955_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(v_00_u03b1_1952_, v_ch_1953_);
v_r_1956_ = lean_box(v_res_1955_);
return v_r_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(lean_object* v_snd_1957_, lean_object* v_inst_1958_, lean_object* v_toBind_1959_, lean_object* v___f_1960_, lean_object* v_a_1961_){
_start:
{
uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1962_ = 1;
v___x_1963_ = lean_box(v___x_1962_);
v___x_1964_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1964_, 0, lean_box(0));
lean_closure_set(v___x_1964_, 1, v___x_1963_);
lean_closure_set(v___x_1964_, 2, v_snd_1957_);
v___x_1965_ = lean_apply_2(v_inst_1958_, lean_box(0), v___x_1964_);
v___x_1966_ = lean_apply_4(v_toBind_1959_, lean_box(0), lean_box(0), v___x_1965_, v___f_1960_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_1967_, lean_object* v_inst_1968_, lean_object* v_toBind_1969_, lean_object* v_a_1970_, lean_object* v_inst_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_producers_1973_; lean_object* v_consumers_1974_; uint8_t v_closed_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1996_; 
v_producers_1973_ = lean_ctor_get(v_a_1972_, 0);
v_consumers_1974_ = lean_ctor_get(v_a_1972_, 1);
v_closed_1975_ = lean_ctor_get_uint8(v_a_1972_, sizeof(void*)*2);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_a_1972_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1977_ = v_a_1972_;
v_isShared_1978_ = v_isSharedCheck_1996_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_consumers_1974_);
lean_inc(v_producers_1973_);
lean_dec(v_a_1972_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1996_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1973_);
if (lean_obj_tag(v___x_1979_) == 1)
{
lean_object* v_val_1980_; lean_object* v_fst_1981_; lean_object* v_snd_1982_; lean_object* v_fst_1983_; lean_object* v_snd_1984_; lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___x_1988_; 
v_val_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_val_1980_);
lean_dec_ref_known(v___x_1979_, 1);
v_fst_1981_ = lean_ctor_get(v_val_1980_, 0);
lean_inc(v_fst_1981_);
v_snd_1982_ = lean_ctor_get(v_val_1980_, 1);
lean_inc(v_snd_1982_);
lean_dec(v_val_1980_);
v_fst_1983_ = lean_ctor_get(v_fst_1981_, 0);
lean_inc(v_fst_1983_);
v_snd_1984_ = lean_ctor_get(v_fst_1981_, 1);
lean_inc(v_snd_1984_);
lean_dec(v_fst_1981_);
v___f_1985_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1985_, 0, v_toApplicative_1967_);
lean_closure_set(v___f_1985_, 1, v_fst_1983_);
lean_inc(v_toBind_1969_);
v___f_1986_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1986_, 0, v_snd_1984_);
lean_closure_set(v___f_1986_, 1, v_inst_1968_);
lean_closure_set(v___f_1986_, 2, v_toBind_1969_);
lean_closure_set(v___f_1986_, 3, v___f_1985_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v_snd_1982_);
v___x_1988_ = v___x_1977_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_snd_1982_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_consumers_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*2, v_closed_1975_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_inc(v_a_1970_);
v___x_1989_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1989_, 0, lean_box(0));
lean_closure_set(v___x_1989_, 1, lean_box(0));
lean_closure_set(v___x_1989_, 2, v_a_1970_);
lean_closure_set(v___x_1989_, 3, v___x_1988_);
v___x_1990_ = lean_apply_2(v_inst_1971_, lean_box(0), v___x_1989_);
v___x_1991_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v___x_1990_, v___f_1986_);
return v___x_1991_;
}
}
else
{
lean_object* v_toPure_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec(v___x_1979_);
lean_del_object(v___x_1977_);
lean_dec_ref(v_consumers_1974_);
lean_dec(v_inst_1971_);
lean_dec(v_toBind_1969_);
lean_dec(v_inst_1968_);
v_toPure_1993_ = lean_ctor_get(v_toApplicative_1967_, 1);
lean_inc(v_toPure_1993_);
lean_dec_ref(v_toApplicative_1967_);
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_apply_2(v_toPure_1993_, lean_box(0), v___x_1994_);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_1997_, lean_object* v_inst_1998_, lean_object* v_toBind_1999_, lean_object* v_a_2000_, lean_object* v_inst_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(v_toApplicative_1997_, v_inst_1998_, v_toBind_1999_, v_a_2000_, v_inst_2001_, v_a_2002_);
lean_dec(v_a_2000_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_toApplicative_2008_; lean_object* v_toBind_2009_; lean_object* v___f_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_toApplicative_2008_ = lean_ctor_get(v_inst_2004_, 0);
lean_inc_ref(v_toApplicative_2008_);
v_toBind_2009_ = lean_ctor_get(v_inst_2004_, 1);
lean_inc_n(v_toBind_2009_, 2);
lean_dec_ref(v_inst_2004_);
lean_inc(v_inst_2005_);
lean_inc_n(v_a_2007_, 2);
v___f_2010_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2010_, 0, v_toApplicative_2008_);
lean_closure_set(v___f_2010_, 1, v_inst_2006_);
lean_closure_set(v___f_2010_, 2, v_toBind_2009_);
lean_closure_set(v___f_2010_, 3, v_a_2007_);
lean_closure_set(v___f_2010_, 4, v_inst_2005_);
v___x_2011_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2011_, 0, lean_box(0));
lean_closure_set(v___x_2011_, 1, lean_box(0));
lean_closure_set(v___x_2011_, 2, v_a_2007_);
v___x_2012_ = lean_apply_2(v_inst_2005_, lean_box(0), v___x_2011_);
v___x_2013_ = lean_apply_4(v_toBind_2009_, lean_box(0), lean_box(0), v___x_2012_, v___f_2010_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_2014_, v_inst_2015_, v_inst_2016_, v_a_2017_);
lean_dec(v_a_2017_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(lean_object* v_m_2019_, lean_object* v_00_u03b1_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(v_inst_2021_, v_inst_2022_, v_inst_2023_, v_a_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(lean_object* v_m_2026_, lean_object* v_00_u03b1_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(v_m_2026_, v_00_u03b1_2027_, v_inst_2028_, v_inst_2029_, v_inst_2030_, v_a_2031_);
lean_dec(v_a_2031_);
return v_res_2032_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(lean_object* v_a_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v_producers_2036_; lean_object* v_consumers_2037_; uint8_t v_closed_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2063_; 
v___x_2035_ = lean_st_ref_get(v_a_2033_);
v_producers_2036_ = lean_ctor_get(v___x_2035_, 0);
v_consumers_2037_ = lean_ctor_get(v___x_2035_, 1);
v_closed_2038_ = lean_ctor_get_uint8(v___x_2035_, sizeof(void*)*2);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2040_ = v___x_2035_;
v_isShared_2041_ = v_isSharedCheck_2063_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_consumers_2037_);
lean_inc(v_producers_2036_);
lean_dec(v___x_2035_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2063_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2036_);
if (lean_obj_tag(v___x_2042_) == 1)
{
lean_object* v_val_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2061_; 
v_val_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2061_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_val_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2061_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v_fst_2047_; lean_object* v_snd_2048_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v___x_2052_; 
v_fst_2047_ = lean_ctor_get(v_val_2043_, 0);
lean_inc(v_fst_2047_);
v_snd_2048_ = lean_ctor_get(v_val_2043_, 1);
lean_inc(v_snd_2048_);
lean_dec(v_val_2043_);
v_fst_2049_ = lean_ctor_get(v_fst_2047_, 0);
lean_inc(v_fst_2049_);
v_snd_2050_ = lean_ctor_get(v_fst_2047_, 1);
lean_inc(v_snd_2050_);
lean_dec(v_fst_2047_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v_snd_2048_);
v___x_2052_ = v___x_2040_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_snd_2048_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_consumers_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*2, v_closed_2038_);
v___x_2052_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2053_ = lean_st_ref_swap(v_a_2033_, v___x_2052_);
lean_dec(v___x_2053_);
v___x_2054_ = 1;
v___x_2055_ = lean_box(v___x_2054_);
v___x_2056_ = lean_io_promise_resolve(v___x_2055_, v_snd_2050_);
lean_dec(v_snd_2050_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v_fst_2049_);
v___x_2058_ = v___x_2045_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_fst_2049_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v___x_2062_; 
lean_dec(v___x_2042_);
lean_del_object(v___x_2040_);
lean_dec_ref(v_consumers_2037_);
v___x_2062_ = lean_box(0);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2033_ = stack[0].m_obj;
lean_object* v_res_2064_;
v_res_2064_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2033_);
stack->m_obj
 = v_res_2064_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(lean_object* v_a_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2065_);
lean_dec(v_a_2065_);
return v_res_2067_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_object* v_00_u03b1_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2069_ = stack[1].m_obj;
lean_object* v_res_2072_;
v_res_2072_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(lean_box(0), v_a_2069_);
stack->m_obj
 = v_res_2072_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_2073_, lean_object* v_a_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_2073_, v_a_2074_);
lean_dec(v_a_2074_);
return v_res_2076_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(lean_object* v_ch_2078_){
_start:
{
lean_object* v___f_2080_; lean_object* v___x_2081_; 
v___f_2080_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0));
v___x_2081_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2078_, v___f_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2078_ = stack[0].m_obj;
lean_object* v_res_2082_;
v_res_2082_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2078_);
stack->m_obj
 = v_res_2082_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(lean_object* v_ch_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2083_);
return v_res_2085_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_object* v_00_u03b1_2086_, lean_object* v_ch_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2087_ = stack[1].m_obj;
lean_object* v_res_2090_;
v_res_2090_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(lean_box(0), v_ch_2087_);
stack->m_obj
 = v_res_2090_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(lean_object* v_00_u03b1_2091_, lean_object* v_ch_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(v_00_u03b1_2091_, v_ch_2092_);
return v_res_2094_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(lean_object* v___f_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_st_ref_get(v___y_2096_);
v___x_2099_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_2096_);
if (lean_obj_tag(v___x_2099_) == 1)
{
lean_object* v___x_2100_; 
lean_dec(v___x_2098_);
lean_dec_ref(v___f_2095_);
v___x_2100_ = lean_task_pure(v___x_2099_);
return v___x_2100_;
}
else
{
uint8_t v_closed_2101_; 
lean_dec(v___x_2099_);
v_closed_2101_ = lean_ctor_get_uint8(v___x_2098_, sizeof(void*)*2);
if (v_closed_2101_ == 0)
{
lean_object* v_producers_2102_; lean_object* v_consumers_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2118_; 
v_producers_2102_ = lean_ctor_get(v___x_2098_, 0);
v_consumers_2103_ = lean_ctor_get(v___x_2098_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2105_ = v___x_2098_;
v_isShared_2106_ = v_isSharedCheck_2118_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_consumers_2103_);
lean_inc(v_producers_2102_);
lean_dec(v___x_2098_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2118_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2107_ = 1;
v___x_2108_ = lean_io_promise_new();
lean_inc(v___x_2108_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
v___x_2110_ = l_Std_Queue_enqueue___redArg(v___x_2109_, v_consumers_2103_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___x_2110_);
v___x_2112_ = v___x_2105_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_producers_2102_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2110_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*2, v_closed_2101_);
v___x_2112_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2113_ = lean_st_ref_swap(v___y_2096_, v___x_2112_);
lean_dec(v___x_2113_);
v___x_2114_ = lean_io_promise_result_opt(v___x_2108_);
lean_dec(v___x_2108_);
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_task_map(v___f_2095_, v___x_2114_, v___x_2115_, v___x_2107_);
return v___x_2116_;
}
}
}
else
{
lean_object* v___x_2119_; 
lean_dec(v___x_2098_);
lean_dec_ref(v___f_2095_);
v___x_2119_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_2119_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2095_ = stack[0].m_obj;
lean_object* v___y_2096_ = stack[1].m_obj;
lean_object* v_res_2120_;
v_res_2120_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2095_, v___y_2096_);
stack->m_obj
 = v_res_2120_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(lean_object* v___f_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(v___f_2121_, v___y_2122_);
lean_dec(v___y_2122_);
return v_res_2124_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(lean_object* v_ch_2127_){
_start:
{
lean_object* v___f_2129_; lean_object* v___x_2130_; 
v___f_2129_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0));
v___x_2130_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2127_, v___f_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2127_ = stack[0].m_obj;
lean_object* v_res_2131_;
v_res_2131_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2127_);
stack->m_obj
 = v_res_2131_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(lean_object* v_ch_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2132_);
return v_res_2134_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_object* v_00_u03b1_2135_, lean_object* v_ch_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2136_ = stack[1].m_obj;
lean_object* v_res_2139_;
v_res_2139_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(lean_box(0), v_ch_2136_);
stack->m_obj
 = v_res_2139_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(lean_object* v_00_u03b1_2140_, lean_object* v_ch_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(v_00_u03b1_2140_, v_ch_2141_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_2144_, lean_object* v_a_2145_){
_start:
{
uint8_t v___y_2147_; lean_object* v_producers_2151_; uint8_t v_closed_2152_; uint8_t v___x_2153_; 
v_producers_2151_ = lean_ctor_get(v_a_2145_, 0);
v_closed_2152_ = lean_ctor_get_uint8(v_a_2145_, sizeof(void*)*2);
v___x_2153_ = l_Std_Queue_isEmpty___redArg(v_producers_2151_);
if (v___x_2153_ == 0)
{
uint8_t v___x_2154_; 
v___x_2154_ = 1;
v___y_2147_ = v___x_2154_;
goto v___jp_2146_;
}
else
{
v___y_2147_ = v_closed_2152_;
goto v___jp_2146_;
}
v___jp_2146_:
{
lean_object* v_toPure_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_toPure_2148_ = lean_ctor_get(v_toApplicative_2144_, 1);
lean_inc(v_toPure_2148_);
lean_dec_ref(v_toApplicative_2144_);
v___x_2149_ = lean_box(v___y_2147_);
v___x_2150_ = lean_apply_2(v_toPure_2148_, lean_box(0), v___x_2149_);
return v___x_2150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(v_toApplicative_2155_, v_a_2156_);
lean_dec_ref(v_a_2156_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_toApplicative_2161_; lean_object* v_toBind_2162_; lean_object* v___f_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_toApplicative_2161_ = lean_ctor_get(v_inst_2158_, 0);
lean_inc_ref(v_toApplicative_2161_);
v_toBind_2162_ = lean_ctor_get(v_inst_2158_, 1);
lean_inc(v_toBind_2162_);
lean_dec_ref(v_inst_2158_);
v___f_2163_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2163_, 0, v_toApplicative_2161_);
lean_inc(v_a_2160_);
v___x_2164_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2164_, 0, lean_box(0));
lean_closure_set(v___x_2164_, 1, lean_box(0));
lean_closure_set(v___x_2164_, 2, v_a_2160_);
v___x_2165_ = lean_apply_2(v_inst_2159_, lean_box(0), v___x_2164_);
v___x_2166_ = lean_apply_4(v_toBind_2162_, lean_box(0), lean_box(0), v___x_2165_, v___f_2163_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(v_inst_2167_, v_inst_2168_, v_a_2169_);
lean_dec(v_a_2169_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(lean_object* v_m_2171_, lean_object* v_00_u03b1_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_toApplicative_2176_; lean_object* v_toBind_2177_; lean_object* v___f_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_toApplicative_2176_ = lean_ctor_get(v_inst_2173_, 0);
lean_inc_ref(v_toApplicative_2176_);
v_toBind_2177_ = lean_ctor_get(v_inst_2173_, 1);
lean_inc(v_toBind_2177_);
lean_dec_ref(v_inst_2173_);
v___f_2178_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2178_, 0, v_toApplicative_2176_);
lean_inc(v_a_2175_);
v___x_2179_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2179_, 0, lean_box(0));
lean_closure_set(v___x_2179_, 1, lean_box(0));
lean_closure_set(v___x_2179_, 2, v_a_2175_);
v___x_2180_ = lean_apply_2(v_inst_2174_, lean_box(0), v___x_2179_);
v___x_2181_ = lean_apply_4(v_toBind_2177_, lean_box(0), lean_box(0), v___x_2180_, v___f_2178_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(lean_object* v_m_2182_, lean_object* v_00_u03b1_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(v_m_2182_, v_00_u03b1_2183_, v_inst_2184_, v_inst_2185_, v_a_2186_);
lean_dec(v_a_2186_);
return v_res_2187_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(lean_object* v_snd_2188_, lean_object* v___f_2189_, lean_object* v_x_2190_){
_start:
{
if (lean_obj_tag(v_x_2190_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v___f_2189_);
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
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2214_; 
v_isSharedCheck_2214_ = !lean_is_exclusive(v_x_2190_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v_x_2190_, 0);
lean_dec(v_unused_2215_);
v___x_2202_ = v_x_2190_;
v_isShared_2203_ = v_isSharedCheck_2214_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v_x_2190_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2214_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint8_t v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2204_ = 1;
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = 0;
v___x_2207_ = lean_box(v___x_2204_);
v___x_2208_ = lean_io_promise_resolve(v___x_2207_, v_snd_2188_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2208_);
v___x_2210_ = v___x_2202_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2205_, v___x_2206_, v___x_2211_, v___f_2189_);
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2188_ = stack[0].m_obj;
lean_object* v___f_2189_ = stack[1].m_obj;
lean_object* v_x_2190_ = stack[2].m_obj;
lean_object* v_res_2216_;
v_res_2216_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2188_, v___f_2189_, v_x_2190_);
stack->m_obj
 = v_res_2216_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_snd_2217_, lean_object* v___f_2218_, lean_object* v_x_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_2217_, v___f_2218_, v_x_2219_);
lean_dec(v_snd_2217_);
return v_res_2221_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(lean_object* v_a_2222_, lean_object* v_x_2223_){
_start:
{
if (lean_obj_tag(v_x_2223_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
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
lean_object* v_a_2234_; lean_object* v_producers_2235_; lean_object* v_consumers_2236_; uint8_t v_closed_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2258_; 
v_a_2234_ = lean_ctor_get(v_x_2223_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v_x_2223_, 1);
v_producers_2235_ = lean_ctor_get(v_a_2234_, 0);
v_consumers_2236_ = lean_ctor_get(v_a_2234_, 1);
v_closed_2237_ = lean_ctor_get_uint8(v_a_2234_, sizeof(void*)*2);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_a_2234_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2239_ = v_a_2234_;
v_isShared_2240_ = v_isSharedCheck_2258_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_consumers_2236_);
lean_inc(v_producers_2235_);
lean_dec(v_a_2234_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2258_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2235_);
if (lean_obj_tag(v___x_2241_) == 1)
{
lean_object* v_val_2242_; lean_object* v_fst_2243_; lean_object* v_snd_2244_; lean_object* v_fst_2245_; lean_object* v_snd_2246_; lean_object* v___f_2247_; lean_object* v___f_2248_; lean_object* v___x_2250_; 
v_val_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v___x_2241_, 1);
v_fst_2243_ = lean_ctor_get(v_val_2242_, 0);
lean_inc(v_fst_2243_);
v_snd_2244_ = lean_ctor_get(v_val_2242_, 1);
lean_inc(v_snd_2244_);
lean_dec(v_val_2242_);
v_fst_2245_ = lean_ctor_get(v_fst_2243_, 0);
lean_inc(v_fst_2245_);
v_snd_2246_ = lean_ctor_get(v_fst_2243_, 1);
lean_inc(v_snd_2246_);
lean_dec(v_fst_2243_);
v___f_2247_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2247_, 0, v_fst_2245_);
v___f_2248_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2248_, 0, v_snd_2246_);
lean_closure_set(v___f_2248_, 1, v___f_2247_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v_snd_2244_);
v___x_2250_ = v___x_2239_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_snd_2244_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_consumers_2236_);
lean_ctor_set_uint8(v_reuseFailAlloc_2256_, sizeof(void*)*2, v_closed_2237_);
v___x_2250_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2251_; uint8_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2251_ = lean_unsigned_to_nat(0u);
v___x_2252_ = 0;
v___x_2253_ = lean_st_ref_swap(v_a_2222_, v___x_2250_);
lean_dec(v___x_2253_);
v___x_2254_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_2255_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2251_, v___x_2252_, v___x_2254_, v___f_2248_);
return v___x_2255_;
}
}
else
{
lean_object* v___x_2257_; 
lean_dec(v___x_2241_);
lean_del_object(v___x_2239_);
lean_dec_ref(v_consumers_2236_);
v___x_2257_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_2257_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2222_ = stack[0].m_obj;
lean_object* v_x_2223_ = stack[1].m_obj;
lean_object* v_res_2259_;
v_res_2259_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2222_, v_x_2223_);
stack->m_obj
 = v_res_2259_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_a_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_2260_, v_x_2261_);
lean_dec(v_a_2260_);
return v_res_2263_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(lean_object* v_a_2264_){
_start:
{
lean_object* v___f_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_inc(v_a_2264_);
v___f_2266_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2266_, 0, v_a_2264_);
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = 0;
v___x_2269_ = lean_st_ref_get(v_a_2264_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
v___x_2272_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2267_, v___x_2268_, v___x_2271_, v___f_2266_);
return v___x_2272_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2264_ = stack[0].m_obj;
lean_object* v_res_2273_;
v_res_2273_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2264_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(lean_object* v_a_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2274_);
lean_dec(v_a_2274_);
return v_res_2276_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_object* v_00_u03b1_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2278_ = stack[1].m_obj;
lean_object* v_res_2281_;
v_res_2281_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(lean_box(0), v_a_2278_);
stack->m_obj
 = v_res_2281_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_a_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_2282_, v_a_2283_);
lean_dec(v_a_2283_);
return v_res_2285_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(lean_object* v_lose_2286_, lean_object* v___y_2287_, lean_object* v___f_2288_, lean_object* v_x_2289_){
_start:
{
if (lean_obj_tag(v_x_2289_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v___f_2288_);
lean_dec_ref(v_lose_2286_);
v_a_2291_ = lean_ctor_get(v_x_2289_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_x_2289_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2293_ = v_x_2289_;
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v_x_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
}
else
{
lean_object* v_a_2300_; uint8_t v___x_2301_; 
v_a_2300_ = lean_ctor_get(v_x_2289_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v_x_2289_, 1);
v___x_2301_ = lean_unbox(v_a_2300_);
lean_dec(v_a_2300_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; 
lean_dec_ref(v___f_2288_);
lean_inc(v___y_2287_);
v___x_2302_ = lean_apply_2(v_lose_2286_, v___y_2287_, lean_box(0));
return v___x_2302_;
}
else
{
lean_object* v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec_ref(v_lose_2286_);
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = 0;
v___x_2305_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2287_);
v___x_2306_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2303_, v___x_2304_, v___x_2305_, v___f_2288_);
return v___x_2306_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lose_2286_ = stack[0].m_obj;
lean_object* v___y_2287_ = stack[1].m_obj;
lean_object* v___f_2288_ = stack[2].m_obj;
lean_object* v_x_2289_ = stack[3].m_obj;
lean_object* v_res_2307_;
v_res_2307_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2286_, v___y_2287_, v___f_2288_, v_x_2289_);
stack->m_obj
 = v_res_2307_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v_lose_2308_, lean_object* v___y_2309_, lean_object* v___f_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_2308_, v___y_2309_, v___f_2310_, v_x_2311_);
lean_dec(v___y_2309_);
return v_res_2313_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(lean_object* v_w_2314_, lean_object* v_lose_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_finished_2318_; lean_object* v_promise_2319_; lean_object* v___f_2320_; lean_object* v___f_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; uint8_t v___y_2326_; uint8_t v___x_2334_; 
v_finished_2318_ = lean_ctor_get(v_w_2314_, 0);
lean_inc(v_finished_2318_);
v_promise_2319_ = lean_ctor_get(v_w_2314_, 1);
lean_inc(v_promise_2319_);
lean_dec_ref(v_w_2314_);
v___f_2320_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2320_, 0, v_promise_2319_);
lean_inc(v___y_2316_);
v___f_2321_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_2321_, 0, v_lose_2315_);
lean_closure_set(v___f_2321_, 1, v___y_2316_);
lean_closure_set(v___f_2321_, 2, v___f_2320_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = 0;
v___x_2324_ = lean_st_ref_take(v_finished_2318_);
v___x_2334_ = lean_unbox(v___x_2324_);
lean_dec(v___x_2324_);
if (v___x_2334_ == 0)
{
uint8_t v___x_2335_; 
v___x_2335_ = 1;
v___y_2326_ = v___x_2335_;
goto v___jp_2325_;
}
else
{
v___y_2326_ = v___x_2323_;
goto v___jp_2325_;
}
v___jp_2325_:
{
uint8_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2327_ = 1;
v___x_2328_ = lean_box(v___x_2327_);
v___x_2329_ = lean_st_ref_put(v_finished_2318_, v___x_2328_);
lean_dec(v_finished_2318_);
v___x_2330_ = lean_box(v___y_2326_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
v___x_2333_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2322_, v___x_2323_, v___x_2332_, v___f_2321_);
return v___x_2333_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_2314_ = stack[0].m_obj;
lean_object* v_lose_2315_ = stack[1].m_obj;
lean_object* v___y_2316_ = stack[2].m_obj;
lean_object* v_res_2336_;
v_res_2336_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2314_, v_lose_2315_, v___y_2316_);
stack->m_obj
 = v_res_2336_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(lean_object* v_w_2337_, lean_object* v_lose_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2337_, v_lose_2338_, v___y_2339_);
lean_dec(v___y_2339_);
return v_res_2341_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_object* v_00_u03b1_2342_, lean_object* v_w_2343_, lean_object* v_lose_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_2343_, v_lose_2344_, v___y_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_2343_ = stack[1].m_obj;
lean_object* v_lose_2344_ = stack[2].m_obj;
lean_object* v___y_2345_ = stack[3].m_obj;
lean_object* v_res_2348_;
v_res_2348_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(lean_box(0), v_w_2343_, v_lose_2344_, v___y_2345_);
stack->m_obj
 = v_res_2348_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_2349_, lean_object* v_w_2350_, lean_object* v_lose_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_2349_, v_w_2350_, v_lose_2351_, v___y_2352_);
lean_dec(v___y_2352_);
return v_res_2354_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(lean_object* v_x_2355_){
_start:
{
uint8_t v___y_2358_; 
if (lean_obj_tag(v_x_2355_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2370_; 
v_a_2362_ = lean_ctor_get(v_x_2355_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_x_2355_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2364_ = v_x_2355_;
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v_x_2355_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2370_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v_producers_2372_; uint8_t v_closed_2373_; uint8_t v___x_2374_; 
v_a_2371_ = lean_ctor_get(v_x_2355_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v_x_2355_, 1);
v_producers_2372_ = lean_ctor_get(v_a_2371_, 0);
lean_inc_ref(v_producers_2372_);
v_closed_2373_ = lean_ctor_get_uint8(v_a_2371_, sizeof(void*)*2);
lean_dec(v_a_2371_);
v___x_2374_ = l_Std_Queue_isEmpty___redArg(v_producers_2372_);
lean_dec_ref(v_producers_2372_);
if (v___x_2374_ == 0)
{
uint8_t v___x_2375_; 
v___x_2375_ = 1;
v___y_2358_ = v___x_2375_;
goto v___jp_2357_;
}
else
{
v___y_2358_ = v_closed_2373_;
goto v___jp_2357_;
}
}
v___jp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_box(v___y_2358_);
v___x_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2355_ = stack[0].m_obj;
lean_object* v_res_2376_;
v_res_2376_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2355_);
stack->m_obj
 = v_res_2376_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(lean_object* v_x_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(v_x_2377_);
return v_res_2379_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(lean_object* v___y_2380_, lean_object* v_waiter_2381_, lean_object* v_x_2382_){
_start:
{
if (lean_obj_tag(v_x_2382_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2392_; 
lean_dec_ref(v_waiter_2381_);
v_a_2384_ = lean_ctor_get(v_x_2382_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_x_2382_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2386_ = v_x_2382_;
v_isShared_2387_ = v_isSharedCheck_2392_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v_x_2382_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2392_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
}
}
else
{
lean_object* v_a_2393_; uint8_t v___x_2394_; 
v_a_2393_ = lean_ctor_get(v_x_2382_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v_x_2382_, 1);
v___x_2394_ = lean_unbox(v_a_2393_);
lean_dec(v_a_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v_producers_2396_; lean_object* v_consumers_2397_; uint8_t v_closed_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2409_; 
v___x_2395_ = lean_st_ref_take(v___y_2380_);
v_producers_2396_ = lean_ctor_get(v___x_2395_, 0);
v_consumers_2397_ = lean_ctor_get(v___x_2395_, 1);
v_closed_2398_ = lean_ctor_get_uint8(v___x_2395_, sizeof(void*)*2);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2400_ = v___x_2395_;
v_isShared_2401_ = v_isSharedCheck_2409_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_consumers_2397_);
lean_inc(v_producers_2396_);
lean_dec(v___x_2395_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2409_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v_waiter_2381_);
v___x_2403_ = l_Std_Queue_enqueue___redArg(v___x_2402_, v_consumers_2397_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 1, v___x_2403_);
v___x_2405_ = v___x_2400_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_producers_2396_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2408_, sizeof(void*)*2, v_closed_2398_);
v___x_2405_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_st_ref_put(v___y_2380_, v___x_2405_);
v___x_2407_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2407_;
}
}
}
else
{
lean_object* v_lose_2410_; lean_object* v___x_2411_; 
v_lose_2410_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0));
v___x_2411_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_2381_, v_lose_2410_, v___y_2380_);
return v___x_2411_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2380_ = stack[0].m_obj;
lean_object* v_waiter_2381_ = stack[1].m_obj;
lean_object* v_x_2382_ = stack[2].m_obj;
lean_object* v_res_2412_;
v_res_2412_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2380_, v_waiter_2381_, v_x_2382_);
stack->m_obj
 = v_res_2412_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(lean_object* v___y_2413_, lean_object* v_waiter_2414_, lean_object* v_x_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(v___y_2413_, v_waiter_2414_, v_x_2415_);
lean_dec(v___y_2413_);
return v_res_2417_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(lean_object* v_waiter_2418_, lean_object* v___f_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___f_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_inc(v___y_2420_);
v___f_2422_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2422_, 0, v___y_2420_);
lean_closure_set(v___f_2422_, 1, v_waiter_2418_);
v___x_2423_ = lean_unsigned_to_nat(0u);
v___x_2424_ = 0;
v___x_2425_ = lean_st_ref_get(v___y_2420_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
v___x_2428_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2423_, v___x_2424_, v___x_2427_, v___f_2419_);
v___x_2429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2423_, v___x_2424_, v___x_2428_, v___f_2422_);
return v___x_2429_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_2418_ = stack[0].m_obj;
lean_object* v___f_2419_ = stack[1].m_obj;
lean_object* v___y_2420_ = stack[2].m_obj;
lean_object* v_res_2430_;
v_res_2430_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v_waiter_2418_, v___f_2419_, v___y_2420_);
stack->m_obj
 = v_res_2430_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(lean_object* v_waiter_2431_, lean_object* v___f_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(v_waiter_2431_, v___f_2432_, v___y_2433_);
lean_dec(v___y_2433_);
return v_res_2435_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(lean_object* v___f_2436_, lean_object* v_ch_2437_, lean_object* v_waiter_2438_){
_start:
{
lean_object* v___f_2440_; lean_object* v___x_2441_; 
v___f_2440_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2440_, 0, v_waiter_2438_);
lean_closure_set(v___f_2440_, 1, v___f_2436_);
v___x_2441_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_2437_, v___f_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2436_ = stack[0].m_obj;
lean_object* v_ch_2437_ = stack[1].m_obj;
lean_object* v_waiter_2438_ = stack[2].m_obj;
lean_object* v_res_2442_;
v_res_2442_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2436_, v_ch_2437_, v_waiter_2438_);
stack->m_obj
 = v_res_2442_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(lean_object* v___f_2443_, lean_object* v_ch_2444_, lean_object* v_waiter_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(v___f_2443_, v_ch_2444_, v_waiter_2445_);
return v_res_2447_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(lean_object* v___y_2448_, lean_object* v___f_2449_, lean_object* v_x_2450_){
_start:
{
if (lean_obj_tag(v_x_2450_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v___f_2449_);
v_a_2452_ = lean_ctor_get(v_x_2450_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_x_2450_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2454_ = v_x_2450_;
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v_x_2450_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2460_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
return v___x_2458_;
}
}
}
else
{
lean_object* v_a_2461_; uint8_t v___x_2462_; 
v_a_2461_ = lean_ctor_get(v_x_2450_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v_x_2450_, 1);
v___x_2462_ = lean_unbox(v_a_2461_);
lean_dec(v_a_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
lean_dec_ref(v___f_2449_);
v___x_2463_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_2463_;
}
else
{
lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = 0;
v___x_2466_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_2448_);
v___x_2467_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2464_, v___x_2465_, v___x_2466_, v___f_2449_);
return v___x_2467_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2448_ = stack[0].m_obj;
lean_object* v___f_2449_ = stack[1].m_obj;
lean_object* v_x_2450_ = stack[2].m_obj;
lean_object* v_res_2468_;
v_res_2468_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2448_, v___f_2449_, v_x_2450_);
stack->m_obj
 = v_res_2468_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(lean_object* v___y_2469_, lean_object* v___f_2470_, lean_object* v_x_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(v___y_2469_, v___f_2470_, v_x_2471_);
lean_dec(v___y_2469_);
return v_res_2473_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(lean_object* v___f_2474_, lean_object* v___f_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___f_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_inc(v___y_2476_);
v___f_2478_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed), 4, 2);
lean_closure_set(v___f_2478_, 0, v___y_2476_);
lean_closure_set(v___f_2478_, 1, v___f_2474_);
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = 0;
v___x_2481_ = lean_st_ref_get(v___y_2476_);
v___x_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
v___x_2484_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2479_, v___x_2480_, v___x_2483_, v___f_2475_);
v___x_2485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2479_, v___x_2480_, v___x_2484_, v___f_2478_);
return v___x_2485_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2474_ = stack[0].m_obj;
lean_object* v___f_2475_ = stack[1].m_obj;
lean_object* v___y_2476_ = stack[2].m_obj;
lean_object* v_res_2486_;
v_res_2486_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2474_, v___f_2475_, v___y_2476_);
stack->m_obj
 = v_res_2486_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(lean_object* v___f_2487_, lean_object* v___f_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(v___f_2487_, v___f_2488_, v___y_2489_);
lean_dec(v___y_2489_);
return v_res_2491_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(lean_object* v_producers_2492_, uint8_t v_closed_2493_, lean_object* v___y_2494_, lean_object* v_x_2495_){
_start:
{
if (lean_obj_tag(v_x_2495_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2505_; 
lean_dec_ref(v_producers_2492_);
v_a_2497_ = lean_ctor_get(v_x_2495_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_x_2495_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2499_ = v_x_2495_;
v_isShared_2500_ = v_isSharedCheck_2505_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v_x_2495_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2505_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
return v___x_2503_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_a_2506_ = lean_ctor_get(v_x_2495_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v_x_2495_, 1);
v___x_2507_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2507_, 0, v_producers_2492_);
lean_ctor_set(v___x_2507_, 1, v_a_2506_);
lean_ctor_set_uint8(v___x_2507_, sizeof(void*)*2, v_closed_2493_);
v___x_2508_ = lean_st_ref_swap(v___y_2494_, v___x_2507_);
lean_dec(v___x_2508_);
v___x_2509_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_2509_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_producers_2492_ = stack[0].m_obj;
uint8_t v_closed_2493_ = stack[1].m_num;
lean_object* v___y_2494_ = stack[2].m_obj;
lean_object* v_x_2495_ = stack[3].m_obj;
lean_object* v_res_2510_;
v_res_2510_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2492_, v_closed_2493_, v___y_2494_, v_x_2495_);
stack->m_obj
 = v_res_2510_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(lean_object* v_producers_2511_, lean_object* v_closed_2512_, lean_object* v___y_2513_, lean_object* v_x_2514_, lean_object* v___y_2515_){
_start:
{
uint8_t v_closed_boxed_2516_; lean_object* v_res_2517_; 
v_closed_boxed_2516_ = lean_unbox(v_closed_2512_);
v_res_2517_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(v_producers_2511_, v_closed_boxed_2516_, v___y_2513_, v_x_2514_);
lean_dec(v___y_2513_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_2518_, lean_object* v_x_2519_, lean_object* v_head_2520_, lean_object* v_x_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2518_, v_x_2519_, v_head_2520_, v_x_2521_);
return v_res_2523_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
if (lean_obj_tag(v_x_2524_) == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v_x_2525_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
else
{
lean_object* v_head_2529_; lean_object* v_tail_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v_head_2529_ = lean_ctor_get(v_x_2524_, 0);
lean_inc_n(v_head_2529_, 2);
v_tail_2530_ = lean_ctor_get(v_x_2524_, 1);
lean_inc(v_tail_2530_);
lean_dec_ref_known(v_x_2524_, 2);
v___f_2531_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_2531_, 0, v_tail_2530_);
lean_closure_set(v___f_2531_, 1, v_x_2525_);
lean_closure_set(v___f_2531_, 2, v_head_2529_);
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = 0;
if (lean_obj_tag(v_head_2529_) == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec_ref_known(v_head_2529_, 1);
v___x_2534_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_2535_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2532_, v___x_2533_, v___x_2534_, v___f_2531_);
return v___x_2535_;
}
else
{
lean_object* v_finished_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2549_; 
v_finished_2536_ = lean_ctor_get(v_head_2529_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_head_2529_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2538_ = v_head_2529_;
v_isShared_2539_ = v_isSharedCheck_2549_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_finished_2536_);
lean_dec(v_head_2529_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2549_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_finished_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v_finished_2540_ = lean_ctor_get(v_finished_2536_, 0);
lean_inc(v_finished_2540_);
lean_dec_ref(v_finished_2536_);
v___f_2541_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_2542_ = lean_st_ref_get(v_finished_2540_);
lean_dec(v_finished_2540_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2542_);
v___x_2544_ = v___x_2538_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
v___x_2546_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2532_, v___x_2533_, v___x_2545_, v___f_2541_);
v___x_2547_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2532_, v___x_2533_, v___x_2546_, v___f_2531_);
return v___x_2547_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2524_ = stack[0].m_obj;
lean_object* v_x_2525_ = stack[1].m_obj;
lean_object* v_res_2550_;
v_res_2550_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2524_, v_x_2525_);
stack->m_obj
 = v_res_2550_;
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_2551_, lean_object* v_x_2552_, lean_object* v_head_2553_, lean_object* v_x_2554_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_head_2553_);
lean_dec(v_x_2552_);
lean_dec(v_tail_2551_);
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
lean_object* v_a_2565_; uint8_t v___x_2566_; 
v_a_2565_ = lean_ctor_get(v_x_2554_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v_x_2554_, 1);
v___x_2566_ = lean_unbox(v_a_2565_);
lean_dec(v_a_2565_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref(v_head_2553_);
v___x_2567_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2551_, v_x_2552_);
return v___x_2567_;
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v_head_2553_);
lean_ctor_set(v___x_2568_, 1, v_x_2552_);
v___x_2569_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_2551_, v___x_2568_);
return v___x_2569_;
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_2551_ = stack[0].m_obj;
lean_object* v_x_2552_ = stack[1].m_obj;
lean_object* v_head_2553_ = stack[2].m_obj;
lean_object* v_x_2554_ = stack[3].m_obj;
lean_object* v_res_2570_;
v_res_2570_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_2551_, v_x_2552_, v_head_2553_, v_x_2554_);
stack->m_obj
 = v_res_2570_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(lean_object* v_x_2571_, lean_object* v_x_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2571_, v_x_2572_);
return v_res_2574_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(lean_object* v___x_2575_, lean_object* v_eList_2576_, lean_object* v___f_2577_, lean_object* v_x_2578_){
_start:
{
if (lean_obj_tag(v_x_2578_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2588_; 
lean_dec_ref(v___f_2577_);
lean_dec(v_eList_2576_);
lean_dec(v___x_2575_);
v_a_2580_ = lean_ctor_get(v_x_2578_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_x_2578_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2582_ = v_x_2578_;
v_isShared_2583_ = v_isSharedCheck_2588_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v_x_2578_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2588_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
return v___x_2586_;
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_a_2589_ = lean_ctor_get(v_x_2578_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v_x_2578_, 1);
lean_inc(v___x_2575_);
v___f_2590_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2590_, 0, v_a_2589_);
lean_closure_set(v___f_2590_, 1, v___x_2575_);
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = 0;
v___x_2593_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_2576_, v___x_2575_);
v___x_2594_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2591_, v___x_2592_, v___x_2593_, v___f_2577_);
v___x_2595_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2591_, v___x_2592_, v___x_2594_, v___f_2590_);
return v___x_2595_;
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2575_ = stack[0].m_obj;
lean_object* v_eList_2576_ = stack[1].m_obj;
lean_object* v___f_2577_ = stack[2].m_obj;
lean_object* v_x_2578_ = stack[3].m_obj;
lean_object* v_res_2596_;
v_res_2596_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v___x_2575_, v_eList_2576_, v___f_2577_, v_x_2578_);
stack->m_obj
 = v_res_2596_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v___x_2597_, lean_object* v_eList_2598_, lean_object* v___f_2599_, lean_object* v_x_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v___x_2597_, v_eList_2598_, v___f_2599_, v_x_2600_);
return v_res_2602_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(lean_object* v_q_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_eList_2606_; lean_object* v_dList_2607_; lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___f_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v_eList_2606_ = lean_ctor_get(v_q_2603_, 0);
lean_inc(v_eList_2606_);
v_dList_2607_ = lean_ctor_get(v_q_2603_, 1);
lean_inc(v_dList_2607_);
lean_dec_ref(v_q_2603_);
v___f_2608_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0));
v___x_2609_ = lean_box(0);
v___f_2610_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2610_, 0, v___x_2609_);
lean_closure_set(v___f_2610_, 1, v_eList_2606_);
lean_closure_set(v___f_2610_, 2, v___f_2608_);
v___x_2611_ = lean_unsigned_to_nat(0u);
v___x_2612_ = 0;
v___x_2613_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_2607_, v___x_2609_);
v___x_2614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2611_, v___x_2612_, v___x_2613_, v___f_2608_);
v___x_2615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2611_, v___x_2612_, v___x_2614_, v___f_2610_);
return v___x_2615_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_2603_ = stack[0].m_obj;
lean_object* v___y_2604_ = stack[1].m_obj;
lean_object* v_res_2616_;
v_res_2616_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2603_, v___y_2604_);
stack->m_obj
 = v_res_2616_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(lean_object* v_q_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2617_, v___y_2618_);
lean_dec(v___y_2618_);
return v_res_2620_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(lean_object* v___y_2621_, lean_object* v_x_2622_){
_start:
{
if (lean_obj_tag(v_x_2622_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2632_; 
v_a_2624_ = lean_ctor_get(v_x_2622_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_x_2622_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2626_ = v_x_2622_;
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v_x_2622_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
return v___x_2630_;
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v_producers_2634_; lean_object* v_consumers_2635_; uint8_t v_closed_2636_; lean_object* v___x_2637_; lean_object* v___f_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v_a_2633_ = lean_ctor_get(v_x_2622_, 0);
lean_inc(v_a_2633_);
lean_dec_ref_known(v_x_2622_, 1);
v_producers_2634_ = lean_ctor_get(v_a_2633_, 0);
lean_inc_ref(v_producers_2634_);
v_consumers_2635_ = lean_ctor_get(v_a_2633_, 1);
lean_inc_ref(v_consumers_2635_);
v_closed_2636_ = lean_ctor_get_uint8(v_a_2633_, sizeof(void*)*2);
lean_dec(v_a_2633_);
v___x_2637_ = lean_box(v_closed_2636_);
lean_inc(v___y_2621_);
v___f_2638_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_2638_, 0, v_producers_2634_);
lean_closure_set(v___f_2638_, 1, v___x_2637_);
lean_closure_set(v___f_2638_, 2, v___y_2621_);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = 0;
v___x_2641_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_2635_, v___y_2621_);
v___x_2642_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2639_, v___x_2640_, v___x_2641_, v___f_2638_);
return v___x_2642_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2621_ = stack[0].m_obj;
lean_object* v_x_2622_ = stack[1].m_obj;
lean_object* v_res_2643_;
v_res_2643_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2621_, v_x_2622_);
stack->m_obj
 = v_res_2643_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(lean_object* v___y_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(v___y_2644_, v_x_2645_);
lean_dec(v___y_2644_);
return v_res_2647_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(lean_object* v___y_2648_){
_start:
{
lean_object* v___f_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_inc(v___y_2648_);
v___f_2650_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2650_, 0, v___y_2648_);
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = 0;
v___x_2653_ = lean_st_ref_get(v___y_2648_);
v___x_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
v___x_2656_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2651_, v___x_2652_, v___x_2655_, v___f_2650_);
return v___x_2656_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2648_ = stack[0].m_obj;
lean_object* v_res_2657_;
v_res_2657_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2648_);
stack->m_obj
 = v_res_2657_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(v___y_2658_);
lean_dec(v___y_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(lean_object* v_ch_2666_){
_start:
{
lean_object* v___f_2667_; lean_object* v___f_2668_; lean_object* v___f_2669_; lean_object* v___f_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___f_2667_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0));
lean_inc_ref_n(v_ch_2666_, 2);
v___f_2668_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_2668_, 0, v___f_2667_);
lean_closure_set(v___f_2668_, 1, v_ch_2666_);
v___f_2669_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1));
v___f_2670_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2));
v___x_2671_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2671_, 0, lean_box(0));
lean_closure_set(v___x_2671_, 1, lean_box(0));
lean_closure_set(v___x_2671_, 2, v_ch_2666_);
lean_closure_set(v___x_2671_, 3, v___f_2669_);
v___x_2672_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_2672_, 0, lean_box(0));
lean_closure_set(v___x_2672_, 1, lean_box(0));
lean_closure_set(v___x_2672_, 2, v_ch_2666_);
lean_closure_set(v___x_2672_, 3, v___f_2670_);
v___x_2673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___f_2668_);
lean_ctor_set(v___x_2673_, 2, v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(lean_object* v_00_u03b1_2674_, lean_object* v_ch_2675_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_2675_);
return v___x_2676_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_object* v_00_u03b1_2677_, lean_object* v_q_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_2678_, v___y_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_2678_ = stack[1].m_obj;
lean_object* v___y_2679_ = stack[2].m_obj;
lean_object* v_res_2682_;
v_res_2682_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(lean_box(0), v_q_2678_, v___y_2679_);
stack->m_obj
 = v_res_2682_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_2683_, lean_object* v_q_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_2683_, v_q_2684_, v___y_2685_);
lean_dec(v___y_2685_);
return v_res_2687_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_object* v_00_u03b1_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_2689_, v_x_2690_);
return v___x_2693_;
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2689_ = stack[1].m_obj;
lean_object* v_x_2690_ = stack[2].m_obj;
lean_object* v___y_2691_ = stack[3].m_obj;
lean_object* v_res_2694_;
v_res_2694_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(lean_box(0), v_x_2689_, v_x_2690_, v___y_2691_);
stack->m_obj
 = v_res_2694_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2695_, lean_object* v_x_2696_, lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_2695_, v_x_2696_, v_x_2697_, v___y_2698_);
lean_dec(v___y_2698_);
return v_res_2700_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(lean_object* v_c_2701_, uint8_t v_b_2702_){
_start:
{
lean_object* v_promise_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_promise_2704_ = lean_ctor_get(v_c_2701_, 0);
v___x_2705_ = lean_box(v_b_2702_);
v___x_2706_ = lean_io_promise_resolve(v___x_2705_, v_promise_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2701_ = stack[0].m_obj;
uint8_t v_b_2702_ = stack[1].m_num;
lean_object* v_res_2707_;
v_res_2707_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2701_, v_b_2702_);
stack->m_obj
 = v_res_2707_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(lean_object* v_c_2708_, lean_object* v_b_2709_, lean_object* v_a_2710_){
_start:
{
uint8_t v_b_boxed_2711_; lean_object* v_res_2712_; 
v_b_boxed_2711_ = lean_unbox(v_b_2709_);
v_res_2712_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2708_, v_b_boxed_2711_);
lean_dec_ref(v_c_2708_);
return v_res_2712_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_object* v_00_u03b1_2713_, lean_object* v_c_2714_, uint8_t v_b_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_c_2714_, v_b_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2714_ = stack[1].m_obj;
uint8_t v_b_2715_ = stack[2].m_num;
lean_object* v_res_2718_;
v_res_2718_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(lean_box(0), v_c_2714_, v_b_2715_);
stack->m_obj
 = v_res_2718_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(lean_object* v_00_u03b1_2719_, lean_object* v_c_2720_, lean_object* v_b_2721_, lean_object* v_a_2722_){
_start:
{
uint8_t v_b_boxed_2723_; lean_object* v_res_2724_; 
v_b_boxed_2723_ = lean_unbox(v_b_2721_);
v_res_2724_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(v_00_u03b1_2719_, v_c_2720_, v_b_boxed_2723_);
lean_dec_ref(v_c_2720_);
return v_res_2724_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(lean_object* v_x_2725_){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_box(0);
v___x_2728_ = lean_st_mk_ref(v___x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2725_ = stack[0].m_obj;
lean_object* v_res_2729_;
v_res_2729_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2725_);
stack->m_obj
 = v_res_2729_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(v_x_2730_);
lean_dec(v_x_2730_);
return v_res_2732_;
}
}
lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(lean_object* v_n_2733_, lean_object* v_f_2734_, lean_object* v_xs_2735_, lean_object* v_k_2736_, lean_object* v_acc_2737_){
_start:
{
uint8_t v___x_2739_; 
v___x_2739_ = lean_nat_dec_lt(v_k_2736_, v_n_2733_);
if (v___x_2739_ == 0)
{
lean_dec(v_k_2736_);
lean_dec_ref(v_f_2734_);
return v_acc_2737_;
}
else
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2740_ = lean_array_fget_borrowed(v_xs_2735_, v_k_2736_);
lean_inc_ref(v_f_2734_);
lean_inc(v___x_2740_);
v___x_2741_ = lean_apply_2(v_f_2734_, v___x_2740_, lean_box(0));
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_nat_add(v_k_2736_, v___x_2742_);
lean_dec(v_k_2736_);
v___x_2744_ = lean_array_push(v_acc_2737_, v___x_2741_);
v_k_2736_ = v___x_2743_;
v_acc_2737_ = v___x_2744_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2733_ = stack[0].m_obj;
lean_object* v_f_2734_ = stack[1].m_obj;
lean_object* v_xs_2735_ = stack[2].m_obj;
lean_object* v_k_2736_ = stack[3].m_obj;
lean_object* v_acc_2737_ = stack[4].m_obj;
lean_object* v_res_2746_;
v_res_2746_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2733_, v_f_2734_, v_xs_2735_, v_k_2736_, v_acc_2737_);
stack->m_obj
 = v_res_2746_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_2747_, lean_object* v_f_2748_, lean_object* v_xs_2749_, lean_object* v_k_2750_, lean_object* v_acc_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2747_, v_f_2748_, v_xs_2749_, v_k_2750_, v_acc_2751_);
lean_dec_ref(v_xs_2749_);
lean_dec(v_n_2747_);
return v_res_2753_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(lean_object* v_capacity_2757_){
_start:
{
lean_object* v___f_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___f_2759_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0));
lean_inc(v_capacity_2757_);
v___x_2760_ = l_Array_range(v_capacity_2757_);
v___x_2761_ = lean_unsigned_to_nat(0u);
v___x_2762_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1));
v___x_2763_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_2757_, v___f_2759_, v___x_2760_, v___x_2761_, v___x_2762_);
lean_dec_ref(v___x_2760_);
v___x_2764_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_2765_ = 0;
v___x_2766_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2764_);
lean_ctor_set(v___x_2766_, 2, v_capacity_2757_);
lean_ctor_set(v___x_2766_, 3, v___x_2763_);
lean_ctor_set(v___x_2766_, 4, v___x_2761_);
lean_ctor_set(v___x_2766_, 5, v___x_2761_);
lean_ctor_set(v___x_2766_, 6, v___x_2761_);
lean_ctor_set_uint8(v___x_2766_, sizeof(void*)*7, v___x_2765_);
v___x_2767_ = l_Std_Mutex_new___redArg(v___x_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_2757_ = stack[0].m_obj;
lean_object* v_res_2768_;
v_res_2768_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2757_);
stack->m_obj
 = v_res_2768_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(lean_object* v_capacity_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2769_);
return v_res_2771_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_object* v_00_u03b1_2772_, lean_object* v_capacity_2773_, lean_object* v_hcap_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_2773_);
return v___x_2776_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_2773_ = stack[1].m_obj;
lean_object* v_res_2777_;
v_res_2777_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(lean_box(0), v_capacity_2773_, lean_box(0));
stack->m_obj
 = v_res_2777_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_capacity_2779_, lean_object* v_hcap_2780_, lean_object* v_a_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(v_00_u03b1_2778_, v_capacity_2779_, v_hcap_2780_);
return v_res_2782_;
}
}
lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_object* v_00_u03b1_2783_, lean_object* v_00_u03b2_2784_, lean_object* v_n_2785_, lean_object* v_f_2786_, lean_object* v_xs_2787_, lean_object* v_k_2788_, lean_object* v_h_2789_, lean_object* v_acc_2790_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_2785_, v_f_2786_, v_xs_2787_, v_k_2788_, v_acc_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT void l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_2785_ = stack[2].m_obj;
lean_object* v_f_2786_ = stack[3].m_obj;
lean_object* v_xs_2787_ = stack[4].m_obj;
lean_object* v_k_2788_ = stack[5].m_obj;
lean_object* v_acc_2790_ = stack[7].m_obj;
lean_object* v_res_2793_;
v_res_2793_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(lean_box(0), lean_box(0), v_n_2785_, v_f_2786_, v_xs_2787_, v_k_2788_, lean_box(0), v_acc_2790_);
stack->m_obj
 = v_res_2793_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_2794_, lean_object* v_00_u03b2_2795_, lean_object* v_n_2796_, lean_object* v_f_2797_, lean_object* v_xs_2798_, lean_object* v_k_2799_, lean_object* v_h_2800_, lean_object* v_acc_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_2794_, v_00_u03b2_2795_, v_n_2796_, v_f_2797_, v_xs_2798_, v_k_2799_, v_h_2800_, v_acc_2801_);
lean_dec_ref(v_xs_2798_);
lean_dec(v_n_2796_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(lean_object* v_idx_2804_, lean_object* v_cap_2805_){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; 
v___x_2806_ = lean_unsigned_to_nat(1u);
v___x_2807_ = lean_nat_add(v_idx_2804_, v___x_2806_);
v___x_2808_ = lean_nat_dec_eq(v___x_2807_, v_cap_2805_);
if (v___x_2808_ == 0)
{
return v___x_2807_;
}
else
{
lean_object* v___x_2809_; 
lean_dec(v___x_2807_);
v___x_2809_ = lean_unsigned_to_nat(0u);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(lean_object* v_idx_2810_, lean_object* v_cap_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(v_idx_2810_, v_cap_2811_);
lean_dec(v_cap_2811_);
lean_dec(v_idx_2810_);
return v_res_2812_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(lean_object* v_v_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v_st_2817_; lean_object* v___y_2818_; lean_object* v___x_2821_; lean_object* v_producers_2822_; lean_object* v_consumers_2823_; lean_object* v_capacity_2824_; lean_object* v_buf_2825_; lean_object* v_bufCount_2826_; lean_object* v_sendIdx_2827_; lean_object* v_recvIdx_2828_; uint8_t v_closed_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2855_; 
v___x_2821_ = lean_st_ref_get(v_a_2814_);
v_producers_2822_ = lean_ctor_get(v___x_2821_, 0);
v_consumers_2823_ = lean_ctor_get(v___x_2821_, 1);
v_capacity_2824_ = lean_ctor_get(v___x_2821_, 2);
v_buf_2825_ = lean_ctor_get(v___x_2821_, 3);
v_bufCount_2826_ = lean_ctor_get(v___x_2821_, 4);
v_sendIdx_2827_ = lean_ctor_get(v___x_2821_, 5);
v_recvIdx_2828_ = lean_ctor_get(v___x_2821_, 6);
v_closed_2829_ = lean_ctor_get_uint8(v___x_2821_, sizeof(void*)*7);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2831_ = v___x_2821_;
v_isShared_2832_ = v_isSharedCheck_2855_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_recvIdx_2828_);
lean_inc(v_sendIdx_2827_);
lean_inc(v_bufCount_2826_);
lean_inc(v_buf_2825_);
lean_inc(v_capacity_2824_);
lean_inc(v_consumers_2823_);
lean_inc(v_producers_2822_);
lean_dec(v___x_2821_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2855_;
goto v_resetjp_2830_;
}
v___jp_2816_:
{
lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = lean_st_ref_swap(v___y_2818_, v_st_2817_);
lean_dec(v___x_2819_);
v___x_2820_ = 1;
return v___x_2820_;
}
v_resetjp_2830_:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_nat_dec_eq(v_bufCount_2826_, v_capacity_2824_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___y_2840_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2834_ = lean_array_fget_borrowed(v_buf_2825_, v_sendIdx_2827_);
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_v_2813_);
v___x_2836_ = lean_st_ref_swap(v___x_2834_, v___x_2835_);
lean_dec(v___x_2836_);
v___x_2837_ = lean_unsigned_to_nat(1u);
v___x_2838_ = lean_nat_add(v_bufCount_2826_, v___x_2837_);
lean_dec(v_bufCount_2826_);
v___x_2851_ = lean_nat_add(v_sendIdx_2827_, v___x_2837_);
lean_dec(v_sendIdx_2827_);
v___x_2852_ = lean_nat_dec_eq(v___x_2851_, v_capacity_2824_);
if (v___x_2852_ == 0)
{
v___y_2840_ = v___x_2851_;
goto v___jp_2839_;
}
else
{
lean_object* v___x_2853_; 
lean_dec(v___x_2851_);
v___x_2853_ = lean_unsigned_to_nat(0u);
v___y_2840_ = v___x_2853_;
goto v___jp_2839_;
}
v___jp_2839_:
{
lean_object* v___x_2842_; 
lean_inc(v_recvIdx_2828_);
lean_inc(v___y_2840_);
lean_inc(v___x_2838_);
lean_inc_ref(v_buf_2825_);
lean_inc(v_capacity_2824_);
lean_inc_ref(v_consumers_2823_);
lean_inc_ref(v_producers_2822_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 5, v___y_2840_);
lean_ctor_set(v___x_2831_, 4, v___x_2838_);
v___x_2842_ = v___x_2831_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_producers_2822_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_consumers_2823_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_capacity_2824_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_buf_2825_);
lean_ctor_set(v_reuseFailAlloc_2850_, 4, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2850_, 5, v___y_2840_);
lean_ctor_set(v_reuseFailAlloc_2850_, 6, v_recvIdx_2828_);
lean_ctor_set_uint8(v_reuseFailAlloc_2850_, sizeof(void*)*7, v_closed_2829_);
v___x_2842_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; 
v___x_2843_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_2823_);
if (lean_obj_tag(v___x_2843_) == 1)
{
lean_object* v_val_2844_; lean_object* v_fst_2845_; lean_object* v_snd_2846_; uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
lean_dec_ref(v___x_2842_);
v_val_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_val_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v_fst_2845_ = lean_ctor_get(v_val_2844_, 0);
lean_inc(v_fst_2845_);
v_snd_2846_ = lean_ctor_get(v_val_2844_, 1);
lean_inc(v_snd_2846_);
lean_dec(v_val_2844_);
v___x_2847_ = 1;
v___x_2848_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_2845_, v___x_2847_);
lean_dec(v_fst_2845_);
v___x_2849_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_2849_, 0, v_producers_2822_);
lean_ctor_set(v___x_2849_, 1, v_snd_2846_);
lean_ctor_set(v___x_2849_, 2, v_capacity_2824_);
lean_ctor_set(v___x_2849_, 3, v_buf_2825_);
lean_ctor_set(v___x_2849_, 4, v___x_2838_);
lean_ctor_set(v___x_2849_, 5, v___y_2840_);
lean_ctor_set(v___x_2849_, 6, v_recvIdx_2828_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7, v_closed_2829_);
v_st_2817_ = v___x_2849_;
v___y_2818_ = v_a_2814_;
goto v___jp_2816_;
}
else
{
lean_dec(v___x_2843_);
lean_dec(v___y_2840_);
lean_dec(v___x_2838_);
lean_dec(v_recvIdx_2828_);
lean_dec_ref(v_buf_2825_);
lean_dec(v_capacity_2824_);
lean_dec_ref(v_producers_2822_);
v_st_2817_ = v___x_2842_;
v___y_2818_ = v_a_2814_;
goto v___jp_2816_;
}
}
}
}
else
{
uint8_t v___x_2854_; 
lean_del_object(v___x_2831_);
lean_dec(v_recvIdx_2828_);
lean_dec(v_sendIdx_2827_);
lean_dec(v_bufCount_2826_);
lean_dec_ref(v_buf_2825_);
lean_dec(v_capacity_2824_);
lean_dec_ref(v_consumers_2823_);
lean_dec_ref(v_producers_2822_);
lean_dec(v_v_2813_);
v___x_2854_ = 0;
return v___x_2854_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_2813_ = stack[0].m_obj;
lean_object* v_a_2814_ = stack[1].m_obj;
uint8_t v_res_2856_;
v_res_2856_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2813_, v_a_2814_);
stack->m_num = v_res_2856_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_){
_start:
{
uint8_t v_res_2860_; lean_object* v_r_2861_; 
v_res_2860_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2857_, v_a_2858_);
lean_dec(v_a_2858_);
v_r_2861_ = lean_box(v_res_2860_);
return v_r_2861_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_object* v_00_u03b1_2862_, lean_object* v_v_2863_, lean_object* v_a_2864_){
_start:
{
uint8_t v___x_2866_; 
v___x_2866_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2863_, v_a_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_2863_ = stack[1].m_obj;
lean_object* v_a_2864_ = stack[2].m_obj;
uint8_t v_res_2867_;
v_res_2867_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(lean_box(0), v_v_2863_, v_a_2864_);
stack->m_num = v_res_2867_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_2868_, lean_object* v_v_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_){
_start:
{
uint8_t v_res_2872_; lean_object* v_r_2873_; 
v_res_2872_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(v_00_u03b1_2868_, v_v_2869_, v_a_2870_);
lean_dec(v_a_2870_);
v_r_2873_ = lean_box(v_res_2872_);
return v_r_2873_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(lean_object* v_v_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; uint8_t v_closed_2878_; 
v___x_2877_ = lean_st_ref_get(v___y_2875_);
v_closed_2878_ = lean_ctor_get_uint8(v___x_2877_, sizeof(void*)*7);
lean_dec(v___x_2877_);
if (v_closed_2878_ == 0)
{
uint8_t v___x_2879_; 
v___x_2879_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2874_, v___y_2875_);
return v___x_2879_;
}
else
{
uint8_t v___x_2880_; 
lean_dec(v_v_2874_);
v___x_2880_ = 0;
return v___x_2880_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_2874_ = stack[0].m_obj;
lean_object* v___y_2875_ = stack[1].m_obj;
uint8_t v_res_2881_;
v_res_2881_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2874_, v___y_2875_);
stack->m_num = v_res_2881_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
uint8_t v_res_2885_; lean_object* v_r_2886_; 
v_res_2885_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(v_v_2882_, v___y_2883_);
lean_dec(v___y_2883_);
v_r_2886_ = lean_box(v_res_2885_);
return v_r_2886_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(lean_object* v_ch_2887_, lean_object* v_v_2888_){
_start:
{
lean_object* v___f_2890_; lean_object* v___x_2891_; 
v___f_2890_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2890_, 0, v_v_2888_);
v___x_2891_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2887_, v___f_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2887_ = stack[0].m_obj;
lean_object* v_v_2888_ = stack[1].m_obj;
lean_object* v_res_2892_;
v_res_2892_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2887_, v_v_2888_);
stack->m_obj
 = v_res_2892_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(lean_object* v_ch_2893_, lean_object* v_v_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2893_, v_v_2894_);
return v_res_2896_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_object* v_00_u03b1_2897_, lean_object* v_ch_2898_, lean_object* v_v_2899_){
_start:
{
lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_2898_, v_v_2899_);
v___x_2902_ = lean_unbox(v___x_2901_);
lean_dec(v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2898_ = stack[1].m_obj;
lean_object* v_v_2899_ = stack[2].m_obj;
uint8_t v_res_2903_;
v_res_2903_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(lean_box(0), v_ch_2898_, v_v_2899_);
stack->m_num = v_res_2903_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(lean_object* v_00_u03b1_2904_, lean_object* v_ch_2905_, lean_object* v_v_2906_, lean_object* v_a_2907_){
_start:
{
uint8_t v_res_2908_; lean_object* v_r_2909_; 
v_res_2908_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(v_00_u03b1_2904_, v_ch_2905_, v_v_2906_);
v_r_2909_ = lean_box(v_res_2908_);
return v_r_2909_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(lean_object* v_v_2910_, lean_object* v___f_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2914_; uint8_t v_closed_2915_; 
v___x_2914_ = lean_st_ref_get(v___y_2912_);
v_closed_2915_ = lean_ctor_get_uint8(v___x_2914_, sizeof(void*)*7);
lean_dec(v___x_2914_);
if (v_closed_2915_ == 0)
{
uint8_t v___x_2916_; 
v___x_2916_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_2910_, v___y_2912_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v_producers_2919_; lean_object* v_consumers_2920_; lean_object* v_capacity_2921_; lean_object* v_buf_2922_; lean_object* v_bufCount_2923_; lean_object* v_sendIdx_2924_; lean_object* v_recvIdx_2925_; uint8_t v_closed_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2938_; 
v___x_2917_ = lean_io_promise_new();
v___x_2918_ = lean_st_ref_take(v___y_2912_);
v_producers_2919_ = lean_ctor_get(v___x_2918_, 0);
v_consumers_2920_ = lean_ctor_get(v___x_2918_, 1);
v_capacity_2921_ = lean_ctor_get(v___x_2918_, 2);
v_buf_2922_ = lean_ctor_get(v___x_2918_, 3);
v_bufCount_2923_ = lean_ctor_get(v___x_2918_, 4);
v_sendIdx_2924_ = lean_ctor_get(v___x_2918_, 5);
v_recvIdx_2925_ = lean_ctor_get(v___x_2918_, 6);
v_closed_2926_ = lean_ctor_get_uint8(v___x_2918_, sizeof(void*)*7);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2928_ = v___x_2918_;
v_isShared_2929_ = v_isSharedCheck_2938_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_recvIdx_2925_);
lean_inc(v_sendIdx_2924_);
lean_inc(v_bufCount_2923_);
lean_inc(v_buf_2922_);
lean_inc(v_capacity_2921_);
lean_inc(v_consumers_2920_);
lean_inc(v_producers_2919_);
lean_dec(v___x_2918_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2938_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
lean_inc(v___x_2917_);
v___x_2930_ = l_Std_Queue_enqueue___redArg(v___x_2917_, v_producers_2919_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 0, v___x_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_consumers_2920_);
lean_ctor_set(v_reuseFailAlloc_2937_, 2, v_capacity_2921_);
lean_ctor_set(v_reuseFailAlloc_2937_, 3, v_buf_2922_);
lean_ctor_set(v_reuseFailAlloc_2937_, 4, v_bufCount_2923_);
lean_ctor_set(v_reuseFailAlloc_2937_, 5, v_sendIdx_2924_);
lean_ctor_set(v_reuseFailAlloc_2937_, 6, v_recvIdx_2925_);
lean_ctor_set_uint8(v_reuseFailAlloc_2937_, sizeof(void*)*7, v_closed_2926_);
v___x_2932_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2933_ = lean_st_ref_put(v___y_2912_, v___x_2932_);
v___x_2934_ = lean_io_promise_result_opt(v___x_2917_);
lean_dec(v___x_2917_);
v___x_2935_ = lean_unsigned_to_nat(0u);
v___x_2936_ = lean_io_bind_task(v___x_2934_, v___f_2911_, v___x_2935_, v___x_2916_);
return v___x_2936_;
}
}
}
else
{
lean_object* v___x_2939_; 
lean_dec_ref(v___f_2911_);
v___x_2939_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
return v___x_2939_;
}
}
else
{
lean_object* v___x_2940_; 
lean_dec_ref(v___f_2911_);
lean_dec(v_v_2910_);
v___x_2940_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2940_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_2910_ = stack[0].m_obj;
lean_object* v___f_2911_ = stack[1].m_obj;
lean_object* v___y_2912_ = stack[2].m_obj;
lean_object* v_res_2941_;
v_res_2941_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2910_, v___f_2911_, v___y_2912_);
stack->m_obj
 = v_res_2941_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_2942_, lean_object* v___f_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(v_v_2942_, v___f_2943_, v___y_2944_);
lean_dec(v___y_2944_);
return v_res_2946_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(lean_object* v_ch_2947_, lean_object* v_v_2948_, lean_object* v_res_2949_){
_start:
{
if (lean_obj_tag(v_res_2949_) == 0)
{
lean_dec(v_v_2948_);
lean_dec_ref(v_ch_2947_);
goto v___jp_2951_;
}
else
{
lean_object* v_val_2953_; uint8_t v___x_2954_; 
v_val_2953_ = lean_ctor_get(v_res_2949_, 0);
v___x_2954_ = lean_unbox(v_val_2953_);
if (v___x_2954_ == 0)
{
lean_dec(v_v_2948_);
lean_dec_ref(v_ch_2947_);
goto v___jp_2951_;
}
else
{
lean_object* v___x_2955_; 
v___x_2955_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2947_, v_v_2948_);
return v___x_2955_;
}
}
v___jp_2951_:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
return v___x_2952_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2947_ = stack[0].m_obj;
lean_object* v_v_2948_ = stack[1].m_obj;
lean_object* v_res_2949_ = stack[2].m_obj;
lean_object* v_res_2956_;
v_res_2956_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2947_, v_v_2948_, v_res_2949_);
stack->m_obj
 = v_res_2956_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_2957_, lean_object* v_v_2958_, lean_object* v_res_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(v_ch_2957_, v_v_2958_, v_res_2959_);
lean_dec(v_res_2959_);
return v_res_2961_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(lean_object* v_ch_2962_, lean_object* v_v_2963_){
_start:
{
lean_object* v___f_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; 
lean_inc(v_v_2963_);
lean_inc_ref(v_ch_2962_);
v___f_2965_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2965_, 0, v_ch_2962_);
lean_closure_set(v___f_2965_, 1, v_v_2963_);
v___f_2966_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2966_, 0, v_v_2963_);
lean_closure_set(v___f_2966_, 1, v___f_2965_);
v___x_2967_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_2962_, v___f_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2962_ = stack[0].m_obj;
lean_object* v_v_2963_ = stack[1].m_obj;
lean_object* v_res_2968_;
v_res_2968_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2962_, v_v_2963_);
stack->m_obj
 = v_res_2968_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(lean_object* v_ch_2969_, lean_object* v_v_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2969_, v_v_2970_);
return v_res_2972_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_object* v_00_u03b1_2973_, lean_object* v_ch_2974_, lean_object* v_v_2975_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_2974_, v_v_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_2974_ = stack[1].m_obj;
lean_object* v_v_2975_ = stack[2].m_obj;
lean_object* v_res_2978_;
v_res_2978_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(lean_box(0), v_ch_2974_, v_v_2975_);
stack->m_obj
 = v_res_2978_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(lean_object* v_00_u03b1_2979_, lean_object* v_ch_2980_, lean_object* v_v_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(v_00_u03b1_2979_, v_ch_2980_, v_v_2981_);
return v_res_2983_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(uint8_t v___x_2984_, lean_object* v_as_2985_, size_t v_sz_2986_, size_t v_i_2987_, lean_object* v_b_2988_){
_start:
{
uint8_t v___x_2990_; 
v___x_2990_ = lean_usize_dec_lt(v_i_2987_, v_sz_2986_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_b_2988_);
return v___x_2991_;
}
else
{
lean_object* v___x_2992_; lean_object* v_a_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; size_t v___x_2996_; size_t v___x_2997_; 
v___x_2992_ = lean_box(0);
v_a_2993_ = lean_array_uget_borrowed(v_as_2985_, v_i_2987_);
v___x_2994_ = lean_box(v___x_2984_);
v___x_2995_ = lean_io_promise_resolve(v___x_2994_, v_a_2993_);
v___x_2996_ = ((size_t)1ULL);
v___x_2997_ = lean_usize_add(v_i_2987_, v___x_2996_);
v_i_2987_ = v___x_2997_;
v_b_2988_ = v___x_2992_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2984_ = stack[0].m_num;
lean_object* v_as_2985_ = stack[1].m_obj;
size_t v_sz_2986_ = stack[2].m_num;
size_t v_i_2987_ = stack[3].m_num;
lean_object* v_b_2988_ = stack[4].m_obj;
lean_object* v_res_2999_;
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v___x_2984_, v_as_2985_, v_sz_2986_, v_i_2987_, v_b_2988_);
stack->m_obj
 = v_res_2999_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg___boxed(lean_object* v___x_3000_, lean_object* v_as_3001_, lean_object* v_sz_3002_, lean_object* v_i_3003_, lean_object* v_b_3004_, lean_object* v___y_3005_){
_start:
{
uint8_t v___x_1818__boxed_3006_; size_t v_sz_boxed_3007_; size_t v_i_boxed_3008_; lean_object* v_res_3009_; 
v___x_1818__boxed_3006_ = lean_unbox(v___x_3000_);
v_sz_boxed_3007_ = lean_unbox_usize(v_sz_3002_);
lean_dec(v_sz_3002_);
v_i_boxed_3008_ = lean_unbox_usize(v_i_3003_);
lean_dec(v_i_3003_);
v_res_3009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v___x_1818__boxed_3006_, v_as_3001_, v_sz_boxed_3007_, v_i_boxed_3008_, v_b_3004_);
lean_dec_ref(v_as_3001_);
return v_res_3009_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(uint8_t v___x_3010_, lean_object* v_as_3011_, size_t v_sz_3012_, size_t v_i_3013_, lean_object* v_b_3014_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_lt(v_i_3013_, v_sz_3012_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_b_3014_);
return v___x_3017_;
}
else
{
lean_object* v___x_3018_; lean_object* v_a_3019_; lean_object* v___x_3020_; size_t v___x_3021_; size_t v___x_3022_; 
v___x_3018_ = lean_box(0);
v_a_3019_ = lean_array_uget_borrowed(v_as_3011_, v_i_3013_);
v___x_3020_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_3019_, v___x_3010_);
v___x_3021_ = ((size_t)1ULL);
v___x_3022_ = lean_usize_add(v_i_3013_, v___x_3021_);
v_i_3013_ = v___x_3022_;
v_b_3014_ = v___x_3018_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3010_ = stack[0].m_num;
lean_object* v_as_3011_ = stack[1].m_obj;
size_t v_sz_3012_ = stack[2].m_num;
size_t v_i_3013_ = stack[3].m_num;
lean_object* v_b_3014_ = stack[4].m_obj;
lean_object* v_res_3024_;
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_3010_, v_as_3011_, v_sz_3012_, v_i_3013_, v_b_3014_);
stack->m_obj
 = v_res_3024_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_3025_, lean_object* v_as_3026_, lean_object* v_sz_3027_, lean_object* v_i_3028_, lean_object* v_b_3029_, lean_object* v___y_3030_){
_start:
{
uint8_t v___x_1852__boxed_3031_; size_t v_sz_boxed_3032_; size_t v_i_boxed_3033_; lean_object* v_res_3034_; 
v___x_1852__boxed_3031_ = lean_unbox(v___x_3025_);
v_sz_boxed_3032_ = lean_unbox_usize(v_sz_3027_);
lean_dec(v_sz_3027_);
v_i_boxed_3033_ = lean_unbox_usize(v_i_3028_);
lean_dec(v_i_3028_);
v_res_3034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1852__boxed_3031_, v_as_3026_, v_sz_boxed_3032_, v_i_boxed_3033_, v_b_3029_);
lean_dec_ref(v_as_3026_);
return v_res_3034_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(lean_object* v___y_3035_){
_start:
{
lean_object* v___x_3037_; uint8_t v_closed_3038_; 
v___x_3037_ = lean_st_ref_get(v___y_3035_);
v_closed_3038_ = lean_ctor_get_uint8(v___x_3037_, sizeof(void*)*7);
if (v_closed_3038_ == 0)
{
lean_object* v_producers_3039_; lean_object* v_consumers_3040_; lean_object* v_capacity_3041_; lean_object* v_buf_3042_; lean_object* v_bufCount_3043_; lean_object* v_sendIdx_3044_; lean_object* v_recvIdx_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3071_; 
v_producers_3039_ = lean_ctor_get(v___x_3037_, 0);
v_consumers_3040_ = lean_ctor_get(v___x_3037_, 1);
v_capacity_3041_ = lean_ctor_get(v___x_3037_, 2);
v_buf_3042_ = lean_ctor_get(v___x_3037_, 3);
v_bufCount_3043_ = lean_ctor_get(v___x_3037_, 4);
v_sendIdx_3044_ = lean_ctor_get(v___x_3037_, 5);
v_recvIdx_3045_ = lean_ctor_get(v___x_3037_, 6);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3047_ = v___x_3037_;
v_isShared_3048_ = v_isSharedCheck_3071_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_recvIdx_3045_);
lean_inc(v_sendIdx_3044_);
lean_inc(v_bufCount_3043_);
lean_inc(v_buf_3042_);
lean_inc(v_capacity_3041_);
lean_inc(v_consumers_3040_);
lean_inc(v_producers_3039_);
lean_dec(v___x_3037_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3071_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; size_t v_sz_3051_; size_t v___x_3052_; lean_object* v___x_3053_; 
v___x_3049_ = l_Std_Queue_toArray___redArg(v_consumers_3040_);
v___x_3050_ = lean_box(0);
v_sz_3051_ = lean_array_size(v___x_3049_);
v___x_3052_ = ((size_t)0ULL);
v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_3038_, v___x_3049_, v_sz_3051_, v___x_3052_, v___x_3050_);
lean_dec_ref(v___x_3049_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v___x_3054_; size_t v_sz_3055_; lean_object* v___x_3056_; 
lean_dec_ref_known(v___x_3053_, 1);
v___x_3054_ = l_Std_Queue_toArray___redArg(v_producers_3039_);
v_sz_3055_ = lean_array_size(v___x_3054_);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v_closed_3038_, v___x_3054_, v_sz_3055_, v___x_3052_, v___x_3050_);
lean_dec_ref(v___x_3054_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3069_; 
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; 
v_unused_3070_ = lean_ctor_get(v___x_3056_, 0);
lean_dec(v_unused_3070_);
v___x_3058_ = v___x_3056_;
v_isShared_3059_ = v_isSharedCheck_3069_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v___x_3056_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3069_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; uint8_t v___x_3061_; lean_object* v___x_3063_; 
v___x_3060_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
v___x_3061_ = 1;
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v___x_3060_);
lean_ctor_set(v___x_3047_, 0, v___x_3060_);
v___x_3063_ = v___x_3047_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_capacity_3041_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_buf_3042_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_bufCount_3043_);
lean_ctor_set(v_reuseFailAlloc_3068_, 5, v_sendIdx_3044_);
lean_ctor_set(v_reuseFailAlloc_3068_, 6, v_recvIdx_3045_);
v___x_3063_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3064_; lean_object* v___x_3066_; 
lean_ctor_set_uint8(v___x_3063_, sizeof(void*)*7, v___x_3061_);
v___x_3064_ = lean_st_ref_swap(v___y_3035_, v___x_3063_);
lean_dec(v___x_3064_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3050_);
v___x_3066_ = v___x_3058_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3050_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
else
{
lean_del_object(v___x_3047_);
lean_dec(v_recvIdx_3045_);
lean_dec(v_sendIdx_3044_);
lean_dec(v_bufCount_3043_);
lean_dec_ref(v_buf_3042_);
lean_dec(v_capacity_3041_);
return v___x_3056_;
}
}
else
{
lean_del_object(v___x_3047_);
lean_dec(v_recvIdx_3045_);
lean_dec(v_sendIdx_3044_);
lean_dec(v_bufCount_3043_);
lean_dec_ref(v_buf_3042_);
lean_dec(v_capacity_3041_);
lean_dec_ref(v_producers_3039_);
return v___x_3053_;
}
}
}
else
{
uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec(v___x_3037_);
v___x_3072_ = 1;
v___x_3073_ = lean_box(v___x_3072_);
v___x_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3035_ = stack[0].m_obj;
lean_object* v_res_3075_;
v_res_3075_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_3035_);
stack->m_obj
 = v_res_3075_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(v___y_3076_);
lean_dec(v___y_3076_);
return v_res_3078_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(lean_object* v_ch_3080_){
_start:
{
lean_object* v___f_3082_; lean_object* v___x_3083_; 
v___f_3082_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0));
v___x_3083_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_3080_, v___f_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3080_ = stack[0].m_obj;
lean_object* v_res_3084_;
v_res_3084_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_3080_);
stack->m_obj
 = v_res_3084_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(lean_object* v_ch_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_3085_);
return v_res_3087_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_object* v_00_u03b1_3088_, lean_object* v_ch_3089_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_3089_);
return v___x_3091_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3089_ = stack[1].m_obj;
lean_object* v_res_3092_;
v_res_3092_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(lean_box(0), v_ch_3089_);
stack->m_obj
 = v_res_3092_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(lean_object* v_00_u03b1_3093_, lean_object* v_ch_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(v_00_u03b1_3093_, v_ch_3094_);
return v_res_3096_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_object* v_00_u03b1_3097_, uint8_t v___x_3098_, lean_object* v_as_3099_, size_t v_sz_3100_, size_t v_i_3101_, lean_object* v_b_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_3098_, v_as_3099_, v_sz_3100_, v_i_3101_, v_b_3102_);
return v___x_3105_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3098_ = stack[1].m_num;
lean_object* v_as_3099_ = stack[2].m_obj;
size_t v_sz_3100_ = stack[3].m_num;
size_t v_i_3101_ = stack[4].m_num;
lean_object* v_b_3102_ = stack[5].m_obj;
lean_object* v___y_3103_ = stack[6].m_obj;
lean_object* v_res_3106_;
v_res_3106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(lean_box(0), v___x_3098_, v_as_3099_, v_sz_3100_, v_i_3101_, v_b_3102_, v___y_3103_);
stack->m_obj
 = v_res_3106_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_3107_, lean_object* v___x_3108_, lean_object* v_as_3109_, lean_object* v_sz_3110_, lean_object* v_i_3111_, lean_object* v_b_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
uint8_t v___x_2005__boxed_3115_; size_t v_sz_boxed_3116_; size_t v_i_boxed_3117_; lean_object* v_res_3118_; 
v___x_2005__boxed_3115_ = lean_unbox(v___x_3108_);
v_sz_boxed_3116_ = lean_unbox_usize(v_sz_3110_);
lean_dec(v_sz_3110_);
v_i_boxed_3117_ = lean_unbox_usize(v_i_3111_);
lean_dec(v_i_3111_);
v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_3107_, v___x_2005__boxed_3115_, v_as_3109_, v_sz_boxed_3116_, v_i_boxed_3117_, v_b_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v_as_3109_);
return v_res_3118_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1(lean_object* v_00_u03b1_3119_, uint8_t v___x_3120_, lean_object* v_as_3121_, size_t v_sz_3122_, size_t v_i_3123_, lean_object* v_b_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___redArg(v___x_3120_, v_as_3121_, v_sz_3122_, v_i_3123_, v_b_3124_);
return v___x_3127_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3120_ = stack[1].m_num;
lean_object* v_as_3121_ = stack[2].m_obj;
size_t v_sz_3122_ = stack[3].m_num;
size_t v_i_3123_ = stack[4].m_num;
lean_object* v_b_3124_ = stack[5].m_obj;
lean_object* v___y_3125_ = stack[6].m_obj;
lean_object* v_res_3128_;
v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1(lean_box(0), v___x_3120_, v_as_3121_, v_sz_3122_, v_i_3123_, v_b_3124_, v___y_3125_);
stack->m_obj
 = v_res_3128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_3129_, lean_object* v___x_3130_, lean_object* v_as_3131_, lean_object* v_sz_3132_, lean_object* v_i_3133_, lean_object* v_b_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v___x_2023__boxed_3137_; size_t v_sz_boxed_3138_; size_t v_i_boxed_3139_; lean_object* v_res_3140_; 
v___x_2023__boxed_3137_ = lean_unbox(v___x_3130_);
v_sz_boxed_3138_ = lean_unbox_usize(v_sz_3132_);
lean_dec(v_sz_3132_);
v_i_boxed_3139_ = lean_unbox_usize(v_i_3133_);
lean_dec(v_i_3133_);
v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__1(v_00_u03b1_3129_, v___x_2023__boxed_3137_, v_as_3131_, v_sz_boxed_3138_, v_i_boxed_3139_, v_b_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v_as_3131_);
return v_res_3140_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(lean_object* v___y_3141_){
_start:
{
lean_object* v___x_3143_; uint8_t v_closed_3144_; 
v___x_3143_ = lean_st_ref_get(v___y_3141_);
v_closed_3144_ = lean_ctor_get_uint8(v___x_3143_, sizeof(void*)*7);
lean_dec(v___x_3143_);
return v_closed_3144_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3141_ = stack[0].m_obj;
uint8_t v_res_3145_;
v_res_3145_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_3141_);
stack->m_num = v_res_3145_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
uint8_t v_res_3148_; lean_object* v_r_3149_; 
v_res_3148_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(v___y_3146_);
lean_dec(v___y_3146_);
v_r_3149_ = lean_box(v_res_3148_);
return v_r_3149_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(lean_object* v_ch_3151_){
_start:
{
lean_object* v___f_3153_; lean_object* v___x_3154_; 
v___f_3153_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0));
v___x_3154_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3151_, v___f_3153_);
return v___x_3154_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3151_ = stack[0].m_obj;
lean_object* v_res_3155_;
v_res_3155_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3151_);
stack->m_obj
 = v_res_3155_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(lean_object* v_ch_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3156_);
return v_res_3158_;
}
}
uint8_t l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_object* v_00_u03b1_3159_, lean_object* v_ch_3160_){
_start:
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_3160_);
v___x_3163_ = lean_unbox(v___x_3162_);
lean_dec(v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3160_ = stack[1].m_obj;
uint8_t v_res_3164_;
v_res_3164_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(lean_box(0), v_ch_3160_);
stack->m_num = v_res_3164_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(lean_object* v_00_u03b1_3165_, lean_object* v_ch_3166_, lean_object* v_a_3167_){
_start:
{
uint8_t v_res_3168_; lean_object* v_r_3169_; 
v_res_3168_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(v_00_u03b1_3165_, v_ch_3166_);
v_r_3169_ = lean_box(v_res_3168_);
return v_r_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(lean_object* v_toApplicative_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
lean_object* v_toPure_3173_; lean_object* v___x_3174_; 
v_toPure_3173_ = lean_ctor_get(v_toApplicative_3170_, 1);
lean_inc(v_toPure_3173_);
lean_dec_ref(v_toApplicative_3170_);
v___x_3174_ = lean_apply_2(v_toPure_3173_, lean_box(0), v_a_3171_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(lean_object* v_inst_3175_, lean_object* v_toBind_3176_, lean_object* v___f_3177_, lean_object* v_____r_3178_, lean_object* v_st_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
lean_inc(v___y_3180_);
v___x_3181_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_3181_, 0, lean_box(0));
lean_closure_set(v___x_3181_, 1, lean_box(0));
lean_closure_set(v___x_3181_, 2, v___y_3180_);
lean_closure_set(v___x_3181_, 3, v_st_3179_);
v___x_3182_ = lean_apply_2(v_inst_3175_, lean_box(0), v___x_3181_);
v___x_3183_ = lean_apply_4(v_toBind_3176_, lean_box(0), lean_box(0), v___x_3182_, v___f_3177_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_inst_3184_, lean_object* v_toBind_3185_, lean_object* v___f_3186_, lean_object* v_____r_3187_, lean_object* v_st_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3184_, v_toBind_3185_, v___f_3186_, v_____r_3187_, v_st_3188_, v___y_3189_);
lean_dec(v___y_3189_);
return v_res_3190_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(lean_object* v_snd_3191_, lean_object* v_consumers_3192_, lean_object* v_capacity_3193_, lean_object* v_buf_3194_, lean_object* v___x_3195_, lean_object* v_sendIdx_3196_, lean_object* v___y_3197_, uint8_t v_closed_3198_, lean_object* v___f_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3202_, 0, v_snd_3191_);
lean_ctor_set(v___x_3202_, 1, v_consumers_3192_);
lean_ctor_set(v___x_3202_, 2, v_capacity_3193_);
lean_ctor_set(v___x_3202_, 3, v_buf_3194_);
lean_ctor_set(v___x_3202_, 4, v___x_3195_);
lean_ctor_set(v___x_3202_, 5, v_sendIdx_3196_);
lean_ctor_set(v___x_3202_, 6, v___y_3197_);
lean_ctor_set_uint8(v___x_3202_, sizeof(void*)*7, v_closed_3198_);
v___x_3203_ = lean_box(0);
lean_inc(v_a_3200_);
v___x_3204_ = lean_apply_3(v___f_3199_, v___x_3203_, v___x_3202_, v_a_3200_);
return v___x_3204_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_3191_ = stack[0].m_obj;
lean_object* v_consumers_3192_ = stack[1].m_obj;
lean_object* v_capacity_3193_ = stack[2].m_obj;
lean_object* v_buf_3194_ = stack[3].m_obj;
lean_object* v___x_3195_ = stack[4].m_obj;
lean_object* v_sendIdx_3196_ = stack[5].m_obj;
lean_object* v___y_3197_ = stack[6].m_obj;
uint8_t v_closed_3198_ = stack[7].m_num;
lean_object* v___f_3199_ = stack[8].m_obj;
lean_object* v_a_3200_ = stack[9].m_obj;
lean_object* v_a_3201_ = stack[10].m_obj;
lean_object* v_res_3205_;
v_res_3205_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3191_, v_consumers_3192_, v_capacity_3193_, v_buf_3194_, v___x_3195_, v_sendIdx_3196_, v___y_3197_, v_closed_3198_, v___f_3199_, v_a_3200_, v_a_3201_);
stack->m_obj
 = v_res_3205_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(lean_object* v_snd_3206_, lean_object* v_consumers_3207_, lean_object* v_capacity_3208_, lean_object* v_buf_3209_, lean_object* v___x_3210_, lean_object* v_sendIdx_3211_, lean_object* v___y_3212_, lean_object* v_closed_3213_, lean_object* v___f_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
uint8_t v_closed_boxed_3217_; lean_object* v_res_3218_; 
v_closed_boxed_3217_ = lean_unbox(v_closed_3213_);
v_res_3218_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(v_snd_3206_, v_consumers_3207_, v_capacity_3208_, v_buf_3209_, v___x_3210_, v_sendIdx_3211_, v___y_3212_, v_closed_boxed_3217_, v___f_3214_, v_a_3215_, v_a_3216_);
lean_dec(v_a_3215_);
return v_res_3218_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(lean_object* v_toApplicative_3219_, lean_object* v_inst_3220_, lean_object* v_toBind_3221_, lean_object* v_bufCount_3222_, lean_object* v_producers_3223_, lean_object* v_consumers_3224_, lean_object* v_capacity_3225_, lean_object* v_buf_3226_, lean_object* v_sendIdx_3227_, uint8_t v_closed_3228_, lean_object* v_a_3229_, uint8_t v___x_3230_, lean_object* v_inst_3231_, lean_object* v_recvIdx_3232_, lean_object* v___x_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v___f_3235_; lean_object* v___f_3236_; lean_object* v___y_3238_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___f_3235_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3235_, 0, v_toApplicative_3219_);
lean_closure_set(v___f_3235_, 1, v_a_3234_);
lean_inc_ref(v___f_3235_);
lean_inc(v_toBind_3221_);
lean_inc(v_inst_3220_);
v___f_3236_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3236_, 0, v_inst_3220_);
lean_closure_set(v___f_3236_, 1, v_toBind_3221_);
lean_closure_set(v___f_3236_, 2, v___f_3235_);
v___x_3254_ = lean_unsigned_to_nat(1u);
v___x_3255_ = lean_nat_add(v_recvIdx_3232_, v___x_3254_);
v___x_3256_ = lean_nat_dec_eq(v___x_3255_, v_capacity_3225_);
if (v___x_3256_ == 0)
{
lean_dec(v___x_3233_);
v___y_3238_ = v___x_3255_;
goto v___jp_3237_;
}
else
{
lean_dec(v___x_3255_);
v___y_3238_ = v___x_3233_;
goto v___jp_3237_;
}
v___jp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3239_ = lean_unsigned_to_nat(1u);
v___x_3240_ = lean_nat_sub(v_bufCount_3222_, v___x_3239_);
lean_inc(v___y_3238_);
lean_inc(v_sendIdx_3227_);
lean_inc(v___x_3240_);
lean_inc_ref(v_buf_3226_);
lean_inc(v_capacity_3225_);
lean_inc_ref(v_consumers_3224_);
lean_inc_ref(v_producers_3223_);
v___x_3241_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3241_, 0, v_producers_3223_);
lean_ctor_set(v___x_3241_, 1, v_consumers_3224_);
lean_ctor_set(v___x_3241_, 2, v_capacity_3225_);
lean_ctor_set(v___x_3241_, 3, v_buf_3226_);
lean_ctor_set(v___x_3241_, 4, v___x_3240_);
lean_ctor_set(v___x_3241_, 5, v_sendIdx_3227_);
lean_ctor_set(v___x_3241_, 6, v___y_3238_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*7, v_closed_3228_);
v___x_3242_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3223_);
if (lean_obj_tag(v___x_3242_) == 1)
{
lean_object* v_val_3243_; lean_object* v_fst_3244_; lean_object* v_snd_3245_; lean_object* v___x_3246_; lean_object* v___f_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec_ref_known(v___x_3241_, 7);
lean_dec_ref(v___f_3235_);
lean_dec(v_inst_3220_);
v_val_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_val_3243_);
lean_dec_ref_known(v___x_3242_, 1);
v_fst_3244_ = lean_ctor_get(v_val_3243_, 0);
lean_inc(v_fst_3244_);
v_snd_3245_ = lean_ctor_get(v_val_3243_, 1);
lean_inc(v_snd_3245_);
lean_dec(v_val_3243_);
v___x_3246_ = lean_box(v_closed_3228_);
lean_inc(v_a_3229_);
v___f_3247_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_3247_, 0, v_snd_3245_);
lean_closure_set(v___f_3247_, 1, v_consumers_3224_);
lean_closure_set(v___f_3247_, 2, v_capacity_3225_);
lean_closure_set(v___f_3247_, 3, v_buf_3226_);
lean_closure_set(v___f_3247_, 4, v___x_3240_);
lean_closure_set(v___f_3247_, 5, v_sendIdx_3227_);
lean_closure_set(v___f_3247_, 6, v___y_3238_);
lean_closure_set(v___f_3247_, 7, v___x_3246_);
lean_closure_set(v___f_3247_, 8, v___f_3236_);
lean_closure_set(v___f_3247_, 9, v_a_3229_);
v___x_3248_ = lean_box(v___x_3230_);
v___x_3249_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_3249_, 0, lean_box(0));
lean_closure_set(v___x_3249_, 1, v___x_3248_);
lean_closure_set(v___x_3249_, 2, v_fst_3244_);
v___x_3250_ = lean_apply_2(v_inst_3231_, lean_box(0), v___x_3249_);
v___x_3251_ = lean_apply_4(v_toBind_3221_, lean_box(0), lean_box(0), v___x_3250_, v___f_3247_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v___x_3242_);
lean_dec(v___x_3240_);
lean_dec(v___y_3238_);
lean_dec_ref(v___f_3236_);
lean_dec(v_inst_3231_);
lean_dec(v_sendIdx_3227_);
lean_dec_ref(v_buf_3226_);
lean_dec(v_capacity_3225_);
lean_dec_ref(v_consumers_3224_);
v___x_3252_ = lean_box(0);
v___x_3253_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_3220_, v_toBind_3221_, v___f_3235_, v___x_3252_, v___x_3241_, v_a_3229_);
return v___x_3253_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_3219_ = stack[0].m_obj;
lean_object* v_inst_3220_ = stack[1].m_obj;
lean_object* v_toBind_3221_ = stack[2].m_obj;
lean_object* v_bufCount_3222_ = stack[3].m_obj;
lean_object* v_producers_3223_ = stack[4].m_obj;
lean_object* v_consumers_3224_ = stack[5].m_obj;
lean_object* v_capacity_3225_ = stack[6].m_obj;
lean_object* v_buf_3226_ = stack[7].m_obj;
lean_object* v_sendIdx_3227_ = stack[8].m_obj;
uint8_t v_closed_3228_ = stack[9].m_num;
lean_object* v_a_3229_ = stack[10].m_obj;
uint8_t v___x_3230_ = stack[11].m_num;
lean_object* v_inst_3231_ = stack[12].m_obj;
lean_object* v_recvIdx_3232_ = stack[13].m_obj;
lean_object* v___x_3233_ = stack[14].m_obj;
lean_object* v_a_3234_ = stack[15].m_obj;
lean_object* v_res_3257_;
v_res_3257_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3219_, v_inst_3220_, v_toBind_3221_, v_bufCount_3222_, v_producers_3223_, v_consumers_3224_, v_capacity_3225_, v_buf_3226_, v_sendIdx_3227_, v_closed_3228_, v_a_3229_, v___x_3230_, v_inst_3231_, v_recvIdx_3232_, v___x_3233_, v_a_3234_);
stack->m_obj
 = v_res_3257_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(lean_object* v_toApplicative_3258_, lean_object* v_inst_3259_, lean_object* v_toBind_3260_, lean_object* v_bufCount_3261_, lean_object* v_producers_3262_, lean_object* v_consumers_3263_, lean_object* v_capacity_3264_, lean_object* v_buf_3265_, lean_object* v_sendIdx_3266_, lean_object* v_closed_3267_, lean_object* v_a_3268_, lean_object* v___x_3269_, lean_object* v_inst_3270_, lean_object* v_recvIdx_3271_, lean_object* v___x_3272_, lean_object* v_a_3273_){
_start:
{
uint8_t v_closed_boxed_3274_; uint8_t v___x_566__boxed_3275_; lean_object* v_res_3276_; 
v_closed_boxed_3274_ = lean_unbox(v_closed_3267_);
v___x_566__boxed_3275_ = lean_unbox(v___x_3269_);
v_res_3276_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(v_toApplicative_3258_, v_inst_3259_, v_toBind_3260_, v_bufCount_3261_, v_producers_3262_, v_consumers_3263_, v_capacity_3264_, v_buf_3265_, v_sendIdx_3266_, v_closed_boxed_3274_, v_a_3268_, v___x_566__boxed_3275_, v_inst_3270_, v_recvIdx_3271_, v___x_3272_, v_a_3273_);
lean_dec(v_recvIdx_3271_);
lean_dec(v_a_3268_);
lean_dec(v_bufCount_3261_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_3277_, lean_object* v_inst_3278_, lean_object* v_toBind_3279_, lean_object* v_a_3280_, lean_object* v_inst_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v_producers_3283_; lean_object* v_consumers_3284_; lean_object* v_capacity_3285_; lean_object* v_buf_3286_; lean_object* v_bufCount_3287_; lean_object* v_sendIdx_3288_; lean_object* v_recvIdx_3289_; uint8_t v_closed_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v_producers_3283_ = lean_ctor_get(v_a_3282_, 0);
lean_inc_ref(v_producers_3283_);
v_consumers_3284_ = lean_ctor_get(v_a_3282_, 1);
lean_inc_ref(v_consumers_3284_);
v_capacity_3285_ = lean_ctor_get(v_a_3282_, 2);
lean_inc(v_capacity_3285_);
v_buf_3286_ = lean_ctor_get(v_a_3282_, 3);
lean_inc_ref(v_buf_3286_);
v_bufCount_3287_ = lean_ctor_get(v_a_3282_, 4);
lean_inc(v_bufCount_3287_);
v_sendIdx_3288_ = lean_ctor_get(v_a_3282_, 5);
lean_inc(v_sendIdx_3288_);
v_recvIdx_3289_ = lean_ctor_get(v_a_3282_, 6);
lean_inc(v_recvIdx_3289_);
v_closed_3290_ = lean_ctor_get_uint8(v_a_3282_, sizeof(void*)*7);
lean_dec_ref(v_a_3282_);
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = lean_nat_dec_eq(v_bufCount_3287_, v___x_3291_);
if (v___x_3292_ == 0)
{
uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___f_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3293_ = 1;
v___x_3294_ = lean_box(v_closed_3290_);
v___x_3295_ = lean_box(v___x_3293_);
lean_inc(v_recvIdx_3289_);
lean_inc(v_a_3280_);
lean_inc_ref(v_buf_3286_);
lean_inc(v_toBind_3279_);
lean_inc(v_inst_3278_);
v___f_3296_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed), 16, 15);
lean_closure_set(v___f_3296_, 0, v_toApplicative_3277_);
lean_closure_set(v___f_3296_, 1, v_inst_3278_);
lean_closure_set(v___f_3296_, 2, v_toBind_3279_);
lean_closure_set(v___f_3296_, 3, v_bufCount_3287_);
lean_closure_set(v___f_3296_, 4, v_producers_3283_);
lean_closure_set(v___f_3296_, 5, v_consumers_3284_);
lean_closure_set(v___f_3296_, 6, v_capacity_3285_);
lean_closure_set(v___f_3296_, 7, v_buf_3286_);
lean_closure_set(v___f_3296_, 8, v_sendIdx_3288_);
lean_closure_set(v___f_3296_, 9, v___x_3294_);
lean_closure_set(v___f_3296_, 10, v_a_3280_);
lean_closure_set(v___f_3296_, 11, v___x_3295_);
lean_closure_set(v___f_3296_, 12, v_inst_3281_);
lean_closure_set(v___f_3296_, 13, v_recvIdx_3289_);
lean_closure_set(v___f_3296_, 14, v___x_3291_);
v___x_3297_ = lean_array_fget(v_buf_3286_, v_recvIdx_3289_);
lean_dec(v_recvIdx_3289_);
lean_dec_ref(v_buf_3286_);
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_swap___boxed), 5, 4);
lean_closure_set(v___x_3299_, 0, lean_box(0));
lean_closure_set(v___x_3299_, 1, lean_box(0));
lean_closure_set(v___x_3299_, 2, v___x_3297_);
lean_closure_set(v___x_3299_, 3, v___x_3298_);
v___x_3300_ = lean_apply_2(v_inst_3278_, lean_box(0), v___x_3299_);
v___x_3301_ = lean_apply_4(v_toBind_3279_, lean_box(0), lean_box(0), v___x_3300_, v___f_3296_);
return v___x_3301_;
}
else
{
lean_object* v_toPure_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec(v_recvIdx_3289_);
lean_dec(v_sendIdx_3288_);
lean_dec(v_bufCount_3287_);
lean_dec_ref(v_buf_3286_);
lean_dec(v_capacity_3285_);
lean_dec_ref(v_consumers_3284_);
lean_dec_ref(v_producers_3283_);
lean_dec(v_inst_3281_);
lean_dec(v_toBind_3279_);
lean_dec(v_inst_3278_);
v_toPure_3302_ = lean_ctor_get(v_toApplicative_3277_, 1);
lean_inc(v_toPure_3302_);
lean_dec_ref(v_toApplicative_3277_);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_apply_2(v_toPure_3302_, lean_box(0), v___x_3303_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_3305_, lean_object* v_inst_3306_, lean_object* v_toBind_3307_, lean_object* v_a_3308_, lean_object* v_inst_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(v_toApplicative_3305_, v_inst_3306_, v_toBind_3307_, v_a_3308_, v_inst_3309_, v_a_3310_);
lean_dec(v_a_3308_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_toApplicative_3316_; lean_object* v_toBind_3317_; lean_object* v___f_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_toApplicative_3316_ = lean_ctor_get(v_inst_3312_, 0);
lean_inc_ref(v_toApplicative_3316_);
v_toBind_3317_ = lean_ctor_get(v_inst_3312_, 1);
lean_inc_n(v_toBind_3317_, 2);
lean_dec_ref(v_inst_3312_);
lean_inc_n(v_a_3315_, 2);
lean_inc(v_inst_3313_);
v___f_3318_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_3318_, 0, v_toApplicative_3316_);
lean_closure_set(v___f_3318_, 1, v_inst_3313_);
lean_closure_set(v___f_3318_, 2, v_toBind_3317_);
lean_closure_set(v___f_3318_, 3, v_a_3315_);
lean_closure_set(v___f_3318_, 4, v_inst_3314_);
v___x_3319_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3319_, 0, lean_box(0));
lean_closure_set(v___x_3319_, 1, lean_box(0));
lean_closure_set(v___x_3319_, 2, v_a_3315_);
v___x_3320_ = lean_apply_2(v_inst_3313_, lean_box(0), v___x_3319_);
v___x_3321_ = lean_apply_4(v_toBind_3317_, lean_box(0), lean_box(0), v___x_3320_, v___f_3318_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_inst_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3322_, v_inst_3323_, v_inst_3324_, v_a_3325_);
lean_dec(v_a_3325_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(lean_object* v_m_3327_, lean_object* v_00_u03b1_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(v_inst_3329_, v_inst_3330_, v_inst_3331_, v_a_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(lean_object* v_m_3334_, lean_object* v_00_u03b1_3335_, lean_object* v_inst_3336_, lean_object* v_inst_3337_, lean_object* v_inst_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(v_m_3334_, v_00_u03b1_3335_, v_inst_3336_, v_inst_3337_, v_inst_3338_, v_a_3339_);
lean_dec(v_a_3339_);
return v_res_3340_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(lean_object* v_a_3341_){
_start:
{
lean_object* v___x_3343_; lean_object* v_producers_3344_; lean_object* v_consumers_3345_; lean_object* v_capacity_3346_; lean_object* v_buf_3347_; lean_object* v_bufCount_3348_; lean_object* v_sendIdx_3349_; lean_object* v_recvIdx_3350_; uint8_t v_closed_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3383_; 
v___x_3343_ = lean_st_ref_get(v_a_3341_);
v_producers_3344_ = lean_ctor_get(v___x_3343_, 0);
v_consumers_3345_ = lean_ctor_get(v___x_3343_, 1);
v_capacity_3346_ = lean_ctor_get(v___x_3343_, 2);
v_buf_3347_ = lean_ctor_get(v___x_3343_, 3);
v_bufCount_3348_ = lean_ctor_get(v___x_3343_, 4);
v_sendIdx_3349_ = lean_ctor_get(v___x_3343_, 5);
v_recvIdx_3350_ = lean_ctor_get(v___x_3343_, 6);
v_closed_3351_ = lean_ctor_get_uint8(v___x_3343_, sizeof(void*)*7);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3353_ = v___x_3343_;
v_isShared_3354_ = v_isSharedCheck_3383_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_recvIdx_3350_);
lean_inc(v_sendIdx_3349_);
lean_inc(v_bufCount_3348_);
lean_inc(v_buf_3347_);
lean_inc(v_capacity_3346_);
lean_inc(v_consumers_3345_);
lean_inc(v_producers_3344_);
lean_dec(v___x_3343_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3383_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; uint8_t v___x_3356_; 
v___x_3355_ = lean_unsigned_to_nat(0u);
v___x_3356_ = lean_nat_dec_eq(v_bufCount_3348_, v___x_3355_);
if (v___x_3356_ == 0)
{
uint8_t v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v_st_3362_; lean_object* v___y_3363_; lean_object* v___y_3366_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3357_ = 1;
v___x_3358_ = lean_array_fget_borrowed(v_buf_3347_, v_recvIdx_3350_);
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_st_ref_swap(v___x_3358_, v___x_3359_);
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = lean_nat_add(v_recvIdx_3350_, v___x_3379_);
lean_dec(v_recvIdx_3350_);
v___x_3381_ = lean_nat_dec_eq(v___x_3380_, v_capacity_3346_);
if (v___x_3381_ == 0)
{
v___y_3366_ = v___x_3380_;
goto v___jp_3365_;
}
else
{
lean_dec(v___x_3380_);
v___y_3366_ = v___x_3355_;
goto v___jp_3365_;
}
v___jp_3361_:
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_st_ref_swap(v___y_3363_, v_st_3362_);
lean_dec(v___x_3364_);
return v___x_3360_;
}
v___jp_3365_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3367_ = lean_unsigned_to_nat(1u);
v___x_3368_ = lean_nat_sub(v_bufCount_3348_, v___x_3367_);
lean_dec(v_bufCount_3348_);
lean_inc(v___y_3366_);
lean_inc(v_sendIdx_3349_);
lean_inc(v___x_3368_);
lean_inc_ref(v_buf_3347_);
lean_inc(v_capacity_3346_);
lean_inc_ref(v_consumers_3345_);
lean_inc_ref(v_producers_3344_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 6, v___y_3366_);
lean_ctor_set(v___x_3353_, 4, v___x_3368_);
v___x_3370_ = v___x_3353_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_producers_3344_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_consumers_3345_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_capacity_3346_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_buf_3347_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3378_, 5, v_sendIdx_3349_);
lean_ctor_set(v_reuseFailAlloc_3378_, 6, v___y_3366_);
lean_ctor_set_uint8(v_reuseFailAlloc_3378_, sizeof(void*)*7, v_closed_3351_);
v___x_3370_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3344_);
if (lean_obj_tag(v___x_3371_) == 1)
{
lean_object* v_val_3372_; lean_object* v_fst_3373_; lean_object* v_snd_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec_ref(v___x_3370_);
v_val_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_val_3372_);
lean_dec_ref_known(v___x_3371_, 1);
v_fst_3373_ = lean_ctor_get(v_val_3372_, 0);
lean_inc(v_fst_3373_);
v_snd_3374_ = lean_ctor_get(v_val_3372_, 1);
lean_inc(v_snd_3374_);
lean_dec(v_val_3372_);
v___x_3375_ = lean_box(v___x_3357_);
v___x_3376_ = lean_io_promise_resolve(v___x_3375_, v_fst_3373_);
lean_dec(v_fst_3373_);
v___x_3377_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3377_, 0, v_snd_3374_);
lean_ctor_set(v___x_3377_, 1, v_consumers_3345_);
lean_ctor_set(v___x_3377_, 2, v_capacity_3346_);
lean_ctor_set(v___x_3377_, 3, v_buf_3347_);
lean_ctor_set(v___x_3377_, 4, v___x_3368_);
lean_ctor_set(v___x_3377_, 5, v_sendIdx_3349_);
lean_ctor_set(v___x_3377_, 6, v___y_3366_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*7, v_closed_3351_);
v_st_3362_ = v___x_3377_;
v___y_3363_ = v_a_3341_;
goto v___jp_3361_;
}
else
{
lean_dec(v___x_3371_);
lean_dec(v___x_3368_);
lean_dec(v___y_3366_);
lean_dec(v_sendIdx_3349_);
lean_dec_ref(v_buf_3347_);
lean_dec(v_capacity_3346_);
lean_dec_ref(v_consumers_3345_);
v_st_3362_ = v___x_3370_;
v___y_3363_ = v_a_3341_;
goto v___jp_3361_;
}
}
}
}
else
{
lean_object* v___x_3382_; 
lean_del_object(v___x_3353_);
lean_dec(v_recvIdx_3350_);
lean_dec(v_sendIdx_3349_);
lean_dec(v_bufCount_3348_);
lean_dec_ref(v_buf_3347_);
lean_dec(v_capacity_3346_);
lean_dec_ref(v_consumers_3345_);
lean_dec_ref(v_producers_3344_);
v___x_3382_ = lean_box(0);
return v___x_3382_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3341_ = stack[0].m_obj;
lean_object* v_res_3384_;
v_res_3384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3341_);
stack->m_obj
 = v_res_3384_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(lean_object* v_a_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3385_);
lean_dec(v_a_3385_);
return v_res_3387_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_object* v_00_u03b1_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_3389_);
return v___x_3391_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3389_ = stack[1].m_obj;
lean_object* v_res_3392_;
v_res_3392_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(lean_box(0), v_a_3389_);
stack->m_obj
 = v_res_3392_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_a_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_3393_, v_a_3394_);
lean_dec(v_a_3394_);
return v_res_3396_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(lean_object* v_ch_3398_){
_start:
{
lean_object* v___f_3400_; lean_object* v___x_3401_; 
v___f_3400_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0));
v___x_3401_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3398_, v___f_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3398_ = stack[0].m_obj;
lean_object* v_res_3402_;
v_res_3402_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3398_);
stack->m_obj
 = v_res_3402_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(lean_object* v_ch_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3403_);
return v_res_3405_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_object* v_00_u03b1_3406_, lean_object* v_ch_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_3407_);
return v___x_3409_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3407_ = stack[1].m_obj;
lean_object* v_res_3410_;
v_res_3410_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(lean_box(0), v_ch_3407_);
stack->m_obj
 = v_res_3410_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(lean_object* v_00_u03b1_3411_, lean_object* v_ch_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(v_00_u03b1_3411_, v_ch_3412_);
return v_res_3414_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(lean_object* v___f_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_3416_);
if (lean_obj_tag(v___x_3418_) == 1)
{
lean_object* v___x_3419_; 
lean_dec_ref(v___f_3415_);
v___x_3419_ = lean_task_pure(v___x_3418_);
return v___x_3419_;
}
else
{
lean_object* v___x_3420_; uint8_t v_closed_3421_; 
lean_dec(v___x_3418_);
v___x_3420_ = lean_st_ref_get(v___y_3416_);
v_closed_3421_ = lean_ctor_get_uint8(v___x_3420_, sizeof(void*)*7);
lean_dec(v___x_3420_);
if (v_closed_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v_producers_3424_; lean_object* v_consumers_3425_; lean_object* v_capacity_3426_; lean_object* v_buf_3427_; lean_object* v_bufCount_3428_; lean_object* v_sendIdx_3429_; lean_object* v_recvIdx_3430_; uint8_t v_closed_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3445_; 
v___x_3422_ = lean_io_promise_new();
v___x_3423_ = lean_st_ref_take(v___y_3416_);
v_producers_3424_ = lean_ctor_get(v___x_3423_, 0);
v_consumers_3425_ = lean_ctor_get(v___x_3423_, 1);
v_capacity_3426_ = lean_ctor_get(v___x_3423_, 2);
v_buf_3427_ = lean_ctor_get(v___x_3423_, 3);
v_bufCount_3428_ = lean_ctor_get(v___x_3423_, 4);
v_sendIdx_3429_ = lean_ctor_get(v___x_3423_, 5);
v_recvIdx_3430_ = lean_ctor_get(v___x_3423_, 6);
v_closed_3431_ = lean_ctor_get_uint8(v___x_3423_, sizeof(void*)*7);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3433_ = v___x_3423_;
v_isShared_3434_ = v_isSharedCheck_3445_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_recvIdx_3430_);
lean_inc(v_sendIdx_3429_);
lean_inc(v_bufCount_3428_);
lean_inc(v_buf_3427_);
lean_inc(v_capacity_3426_);
lean_inc(v_consumers_3425_);
lean_inc(v_producers_3424_);
lean_dec(v___x_3423_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3445_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3439_; 
v___x_3435_ = lean_box(0);
lean_inc(v___x_3422_);
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3422_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = l_Std_Queue_enqueue___redArg(v___x_3436_, v_consumers_3425_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3437_);
v___x_3439_ = v___x_3433_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_producers_3424_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_capacity_3426_);
lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_buf_3427_);
lean_ctor_set(v_reuseFailAlloc_3444_, 4, v_bufCount_3428_);
lean_ctor_set(v_reuseFailAlloc_3444_, 5, v_sendIdx_3429_);
lean_ctor_set(v_reuseFailAlloc_3444_, 6, v_recvIdx_3430_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, sizeof(void*)*7, v_closed_3431_);
v___x_3439_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3440_ = lean_st_ref_put(v___y_3416_, v___x_3439_);
v___x_3441_ = lean_io_promise_result_opt(v___x_3422_);
lean_dec(v___x_3422_);
v___x_3442_ = lean_unsigned_to_nat(0u);
v___x_3443_ = lean_io_bind_task(v___x_3441_, v___f_3415_, v___x_3442_, v_closed_3421_);
return v___x_3443_;
}
}
}
else
{
lean_object* v___x_3446_; 
lean_dec_ref(v___f_3415_);
v___x_3446_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3446_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3415_ = stack[0].m_obj;
lean_object* v___y_3416_ = stack[1].m_obj;
lean_object* v_res_3447_;
v_res_3447_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3415_, v___y_3416_);
stack->m_obj
 = v_res_3447_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(lean_object* v___f_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(v___f_3448_, v___y_3449_);
lean_dec(v___y_3449_);
return v_res_3451_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(lean_object* v_ch_3452_, lean_object* v_res_3453_){
_start:
{
if (lean_obj_tag(v_res_3453_) == 0)
{
lean_dec_ref(v_ch_3452_);
goto v___jp_3455_;
}
else
{
lean_object* v_val_3457_; uint8_t v___x_3458_; 
v_val_3457_ = lean_ctor_get(v_res_3453_, 0);
v___x_3458_ = lean_unbox(v_val_3457_);
if (v___x_3458_ == 0)
{
lean_dec_ref(v_ch_3452_);
goto v___jp_3455_;
}
else
{
lean_object* v___x_3459_; 
v___x_3459_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3452_);
return v___x_3459_;
}
}
v___jp_3455_:
{
lean_object* v___x_3456_; 
v___x_3456_ = lean_obj_once(&l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
return v___x_3456_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3452_ = stack[0].m_obj;
lean_object* v_res_3453_ = stack[1].m_obj;
lean_object* v_res_3460_;
v_res_3460_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3452_, v_res_3453_);
stack->m_obj
 = v_res_3460_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(lean_object* v_ch_3461_, lean_object* v_res_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(v_ch_3461_, v_res_3462_);
lean_dec(v_res_3462_);
return v_res_3464_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(lean_object* v_ch_3465_){
_start:
{
lean_object* v___f_3467_; lean_object* v___f_3468_; lean_object* v___x_3469_; 
lean_inc_ref(v_ch_3465_);
v___f_3467_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3467_, 0, v_ch_3465_);
v___f_3468_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3468_, 0, v___f_3467_);
v___x_3469_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_3465_, v___f_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3465_ = stack[0].m_obj;
lean_object* v_res_3470_;
v_res_3470_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3465_);
stack->m_obj
 = v_res_3470_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(lean_object* v_ch_3471_, lean_object* v_a_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3471_);
return v_res_3473_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_object* v_00_u03b1_3474_, lean_object* v_ch_3475_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_3475_);
return v___x_3477_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3475_ = stack[1].m_obj;
lean_object* v_res_3478_;
v_res_3478_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(lean_box(0), v_ch_3475_);
stack->m_obj
 = v_res_3478_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_ch_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(v_00_u03b1_3479_, v_ch_3480_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(lean_object* v_toApplicative_3483_, lean_object* v_a_3484_){
_start:
{
uint8_t v___y_3486_; lean_object* v_bufCount_3490_; uint8_t v_closed_3491_; lean_object* v___x_3492_; uint8_t v___x_3493_; 
v_bufCount_3490_ = lean_ctor_get(v_a_3484_, 4);
v_closed_3491_ = lean_ctor_get_uint8(v_a_3484_, sizeof(void*)*7);
v___x_3492_ = lean_unsigned_to_nat(0u);
v___x_3493_ = lean_nat_dec_eq(v_bufCount_3490_, v___x_3492_);
if (v___x_3493_ == 0)
{
uint8_t v___x_3494_; 
v___x_3494_ = 1;
v___y_3486_ = v___x_3494_;
goto v___jp_3485_;
}
else
{
v___y_3486_ = v_closed_3491_;
goto v___jp_3485_;
}
v___jp_3485_:
{
lean_object* v_toPure_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_toPure_3487_ = lean_ctor_get(v_toApplicative_3483_, 1);
lean_inc(v_toPure_3487_);
lean_dec_ref(v_toApplicative_3483_);
v___x_3488_ = lean_box(v___y_3486_);
v___x_3489_ = lean_apply_2(v_toPure_3487_, lean_box(0), v___x_3488_);
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(lean_object* v_toApplicative_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_3495_, v_a_3496_);
lean_dec_ref(v_a_3496_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_a_3500_){
_start:
{
lean_object* v_toApplicative_3501_; lean_object* v_toBind_3502_; lean_object* v___f_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_toApplicative_3501_ = lean_ctor_get(v_inst_3498_, 0);
lean_inc_ref(v_toApplicative_3501_);
v_toBind_3502_ = lean_ctor_get(v_inst_3498_, 1);
lean_inc(v_toBind_3502_);
lean_dec_ref(v_inst_3498_);
v___f_3503_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3503_, 0, v_toApplicative_3501_);
lean_inc(v_a_3500_);
v___x_3504_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3504_, 0, lean_box(0));
lean_closure_set(v___x_3504_, 1, lean_box(0));
lean_closure_set(v___x_3504_, 2, v_a_3500_);
v___x_3505_ = lean_apply_2(v_inst_3499_, lean_box(0), v___x_3504_);
v___x_3506_ = lean_apply_4(v_toBind_3502_, lean_box(0), lean_box(0), v___x_3505_, v___f_3503_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(lean_object* v_inst_3507_, lean_object* v_inst_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(v_inst_3507_, v_inst_3508_, v_a_3509_);
lean_dec(v_a_3509_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(lean_object* v_m_3511_, lean_object* v_00_u03b1_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_toApplicative_3516_; lean_object* v_toBind_3517_; lean_object* v___f_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_toApplicative_3516_ = lean_ctor_get(v_inst_3513_, 0);
lean_inc_ref(v_toApplicative_3516_);
v_toBind_3517_ = lean_ctor_get(v_inst_3513_, 1);
lean_inc(v_toBind_3517_);
lean_dec_ref(v_inst_3513_);
v___f_3518_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3518_, 0, v_toApplicative_3516_);
lean_inc(v_a_3515_);
v___x_3519_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3519_, 0, lean_box(0));
lean_closure_set(v___x_3519_, 1, lean_box(0));
lean_closure_set(v___x_3519_, 2, v_a_3515_);
v___x_3520_ = lean_apply_2(v_inst_3514_, lean_box(0), v___x_3519_);
v___x_3521_ = lean_apply_4(v_toBind_3517_, lean_box(0), lean_box(0), v___x_3520_, v___f_3518_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(lean_object* v_m_3522_, lean_object* v_00_u03b1_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(v_m_3522_, v_00_u03b1_3523_, v_inst_3524_, v_inst_3525_, v_a_3526_);
lean_dec(v_a_3526_);
return v_res_3527_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(lean_object* v_a_3528_){
_start:
{
lean_object* v___x_3530_; lean_object* v_producers_3531_; lean_object* v_consumers_3532_; lean_object* v_capacity_3533_; lean_object* v_buf_3534_; lean_object* v_bufCount_3535_; lean_object* v_sendIdx_3536_; lean_object* v_recvIdx_3537_; uint8_t v_closed_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3572_; 
v___x_3530_ = lean_st_ref_get(v_a_3528_);
v_producers_3531_ = lean_ctor_get(v___x_3530_, 0);
v_consumers_3532_ = lean_ctor_get(v___x_3530_, 1);
v_capacity_3533_ = lean_ctor_get(v___x_3530_, 2);
v_buf_3534_ = lean_ctor_get(v___x_3530_, 3);
v_bufCount_3535_ = lean_ctor_get(v___x_3530_, 4);
v_sendIdx_3536_ = lean_ctor_get(v___x_3530_, 5);
v_recvIdx_3537_ = lean_ctor_get(v___x_3530_, 6);
v_closed_3538_ = lean_ctor_get_uint8(v___x_3530_, sizeof(void*)*7);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3540_ = v___x_3530_;
v_isShared_3541_ = v_isSharedCheck_3572_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_recvIdx_3537_);
lean_inc(v_sendIdx_3536_);
lean_inc(v_bufCount_3535_);
lean_inc(v_buf_3534_);
lean_inc(v_capacity_3533_);
lean_inc(v_consumers_3532_);
lean_inc(v_producers_3531_);
lean_dec(v___x_3530_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3572_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3542_ = lean_unsigned_to_nat(0u);
v___x_3543_ = lean_nat_dec_eq(v_bufCount_3535_, v___x_3542_);
if (v___x_3543_ == 0)
{
uint8_t v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v_st_3549_; lean_object* v___y_3550_; lean_object* v___y_3554_; lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v___x_3544_ = 1;
v___x_3545_ = lean_array_fget_borrowed(v_buf_3534_, v_recvIdx_3537_);
v___x_3546_ = lean_box(0);
v___x_3547_ = lean_st_ref_swap(v___x_3545_, v___x_3546_);
v___x_3567_ = lean_unsigned_to_nat(1u);
v___x_3568_ = lean_nat_add(v_recvIdx_3537_, v___x_3567_);
lean_dec(v_recvIdx_3537_);
v___x_3569_ = lean_nat_dec_eq(v___x_3568_, v_capacity_3533_);
if (v___x_3569_ == 0)
{
v___y_3554_ = v___x_3568_;
goto v___jp_3553_;
}
else
{
lean_dec(v___x_3568_);
v___y_3554_ = v___x_3542_;
goto v___jp_3553_;
}
v___jp_3548_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = lean_st_ref_swap(v___y_3550_, v_st_3549_);
lean_dec(v___x_3551_);
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3547_);
return v___x_3552_;
}
v___jp_3553_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3555_ = lean_unsigned_to_nat(1u);
v___x_3556_ = lean_nat_sub(v_bufCount_3535_, v___x_3555_);
lean_dec(v_bufCount_3535_);
lean_inc(v___y_3554_);
lean_inc(v_sendIdx_3536_);
lean_inc(v___x_3556_);
lean_inc_ref(v_buf_3534_);
lean_inc(v_capacity_3533_);
lean_inc_ref(v_consumers_3532_);
lean_inc_ref(v_producers_3531_);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 6, v___y_3554_);
lean_ctor_set(v___x_3540_, 4, v___x_3556_);
v___x_3558_ = v___x_3540_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_producers_3531_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_consumers_3532_);
lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_capacity_3533_);
lean_ctor_set(v_reuseFailAlloc_3566_, 3, v_buf_3534_);
lean_ctor_set(v_reuseFailAlloc_3566_, 4, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3566_, 5, v_sendIdx_3536_);
lean_ctor_set(v_reuseFailAlloc_3566_, 6, v___y_3554_);
lean_ctor_set_uint8(v_reuseFailAlloc_3566_, sizeof(void*)*7, v_closed_3538_);
v___x_3558_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3531_);
if (lean_obj_tag(v___x_3559_) == 1)
{
lean_object* v_val_3560_; lean_object* v_fst_3561_; lean_object* v_snd_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec_ref(v___x_3558_);
v_val_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_val_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v_fst_3561_ = lean_ctor_get(v_val_3560_, 0);
lean_inc(v_fst_3561_);
v_snd_3562_ = lean_ctor_get(v_val_3560_, 1);
lean_inc(v_snd_3562_);
lean_dec(v_val_3560_);
v___x_3563_ = lean_box(v___x_3544_);
v___x_3564_ = lean_io_promise_resolve(v___x_3563_, v_fst_3561_);
lean_dec(v_fst_3561_);
v___x_3565_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3565_, 0, v_snd_3562_);
lean_ctor_set(v___x_3565_, 1, v_consumers_3532_);
lean_ctor_set(v___x_3565_, 2, v_capacity_3533_);
lean_ctor_set(v___x_3565_, 3, v_buf_3534_);
lean_ctor_set(v___x_3565_, 4, v___x_3556_);
lean_ctor_set(v___x_3565_, 5, v_sendIdx_3536_);
lean_ctor_set(v___x_3565_, 6, v___y_3554_);
lean_ctor_set_uint8(v___x_3565_, sizeof(void*)*7, v_closed_3538_);
v_st_3549_ = v___x_3565_;
v___y_3550_ = v_a_3528_;
goto v___jp_3548_;
}
else
{
lean_dec(v___x_3559_);
lean_dec(v___x_3556_);
lean_dec(v___y_3554_);
lean_dec(v_sendIdx_3536_);
lean_dec_ref(v_buf_3534_);
lean_dec(v_capacity_3533_);
lean_dec_ref(v_consumers_3532_);
v_st_3549_ = v___x_3558_;
v___y_3550_ = v_a_3528_;
goto v___jp_3548_;
}
}
}
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_del_object(v___x_3540_);
lean_dec(v_recvIdx_3537_);
lean_dec(v_sendIdx_3536_);
lean_dec(v_bufCount_3535_);
lean_dec_ref(v_buf_3534_);
lean_dec(v_capacity_3533_);
lean_dec_ref(v_consumers_3532_);
lean_dec_ref(v_producers_3531_);
v___x_3570_ = lean_box(0);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
return v___x_3571_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3528_ = stack[0].m_obj;
lean_object* v_res_3573_;
v_res_3573_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3528_);
stack->m_obj
 = v_res_3573_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_a_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3574_);
lean_dec(v_a_3574_);
return v_res_3576_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_3578_);
return v___x_3580_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3578_ = stack[1].m_obj;
lean_object* v_res_3581_;
v_res_3581_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(lean_box(0), v_a_3578_);
stack->m_obj
 = v_res_3581_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3582_, lean_object* v_a_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_3582_, v_a_3583_);
lean_dec(v_a_3583_);
return v_res_3585_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(lean_object* v_w_3586_, lean_object* v_lose_3587_){
_start:
{
lean_object* v_finished_3589_; lean_object* v_promise_3590_; lean_object* v___x_3591_; uint8_t v___y_3593_; uint8_t v___x_3601_; 
v_finished_3589_ = lean_ctor_get(v_w_3586_, 0);
v_promise_3590_ = lean_ctor_get(v_w_3586_, 1);
v___x_3591_ = lean_st_ref_take(v_finished_3589_);
v___x_3601_ = lean_unbox(v___x_3591_);
lean_dec(v___x_3591_);
if (v___x_3601_ == 0)
{
uint8_t v___x_3602_; 
v___x_3602_ = 1;
v___y_3593_ = v___x_3602_;
goto v___jp_3592_;
}
else
{
uint8_t v___x_3603_; 
v___x_3603_ = 0;
v___y_3593_ = v___x_3603_;
goto v___jp_3592_;
}
v___jp_3592_:
{
uint8_t v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = 1;
v___x_3595_ = lean_box(v___x_3594_);
v___x_3596_ = lean_st_ref_put(v_finished_3589_, v___x_3595_);
if (v___y_3593_ == 0)
{
lean_object* v___x_3597_; 
v___x_3597_ = lean_apply_1(v_lose_3587_, lean_box(0));
return v___x_3597_;
}
else
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_dec_ref(v_lose_3587_);
v___x_3598_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__2));
v___x_3599_ = lean_io_promise_resolve(v___x_3598_, v_promise_3590_);
v___x_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
return v___x_3600_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_3586_ = stack[0].m_obj;
lean_object* v_lose_3587_ = stack[1].m_obj;
lean_object* v_res_3604_;
v_res_3604_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3586_, v_lose_3587_);
stack->m_obj
 = v_res_3604_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_w_3605_, lean_object* v_lose_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3605_, v_lose_3606_);
lean_dec_ref(v_w_3605_);
return v_res_3608_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3609_, lean_object* v_w_3610_, lean_object* v_lose_3611_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_3610_, v_lose_3611_);
return v___x_3613_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_3610_ = stack[1].m_obj;
lean_object* v_lose_3611_ = stack[2].m_obj;
lean_object* v_res_3614_;
v_res_3614_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(lean_box(0), v_w_3610_, v_lose_3611_);
stack->m_obj
 = v_res_3614_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3615_, lean_object* v_w_3616_, lean_object* v_lose_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_3615_, v_w_3616_, v_lose_3617_);
lean_dec_ref(v_w_3616_);
return v_res_3619_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(lean_object* v_w_3620_, lean_object* v_lose_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v_finished_3624_; lean_object* v_promise_3625_; lean_object* v___x_3626_; uint8_t v___y_3628_; uint8_t v___x_3644_; 
v_finished_3624_ = lean_ctor_get(v_w_3620_, 0);
v_promise_3625_ = lean_ctor_get(v_w_3620_, 1);
v___x_3626_ = lean_st_ref_take(v_finished_3624_);
v___x_3644_ = lean_unbox(v___x_3626_);
lean_dec(v___x_3626_);
if (v___x_3644_ == 0)
{
uint8_t v___x_3645_; 
v___x_3645_ = 1;
v___y_3628_ = v___x_3645_;
goto v___jp_3627_;
}
else
{
uint8_t v___x_3646_; 
v___x_3646_ = 0;
v___y_3628_ = v___x_3646_;
goto v___jp_3627_;
}
v___jp_3627_:
{
uint8_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = 1;
v___x_3630_ = lean_box(v___x_3629_);
v___x_3631_ = lean_st_ref_put(v_finished_3624_, v___x_3630_);
if (v___y_3628_ == 0)
{
lean_object* v___x_3632_; 
lean_inc(v___y_3622_);
v___x_3632_ = lean_apply_2(v_lose_3621_, v___y_3622_, lean_box(0));
return v___x_3632_;
}
else
{
lean_object* v___x_3633_; lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3643_; 
lean_dec_ref(v_lose_3621_);
v___x_3633_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_3622_);
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3636_ = v___x_3633_;
v_isShared_3637_ = v_isSharedCheck_3643_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3633_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3643_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_a_3634_);
v___x_3639_ = lean_io_promise_resolve(v___x_3638_, v_promise_3625_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3639_);
v___x_3641_ = v___x_3636_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_3620_ = stack[0].m_obj;
lean_object* v_lose_3621_ = stack[1].m_obj;
lean_object* v___y_3622_ = stack[2].m_obj;
lean_object* v_res_3647_;
v_res_3647_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3620_, v_lose_3621_, v___y_3622_);
stack->m_obj
 = v_res_3647_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v_w_3648_, lean_object* v_lose_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3648_, v_lose_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v_w_3648_);
return v_res_3652_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3653_, lean_object* v_w_3654_, lean_object* v_lose_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_3654_, v_lose_3655_, v___y_3656_);
return v___x_3658_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_3654_ = stack[1].m_obj;
lean_object* v_lose_3655_ = stack[2].m_obj;
lean_object* v___y_3656_ = stack[3].m_obj;
lean_object* v_res_3659_;
v_res_3659_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(lean_box(0), v_w_3654_, v_lose_3655_, v___y_3656_);
stack->m_obj
 = v_res_3659_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3660_, lean_object* v_w_3661_, lean_object* v_lose_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_3660_, v_w_3661_, v_lose_3662_, v___y_3663_);
lean_dec(v___y_3663_);
lean_dec_ref(v_w_3661_);
return v_res_3665_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(lean_object* v_mutex_3666_, lean_object* v_k_3667_){
_start:
{
lean_object* v_ref_3669_; lean_object* v_mutex_3670_; lean_object* v___x_3671_; lean_object* v_r_3672_; 
v_ref_3669_ = lean_ctor_get(v_mutex_3666_, 0);
lean_inc(v_ref_3669_);
v_mutex_3670_ = lean_ctor_get(v_mutex_3666_, 1);
lean_inc(v_mutex_3670_);
lean_dec_ref(v_mutex_3666_);
v___x_3671_ = lean_io_basemutex_lock(v_mutex_3670_);
v_r_3672_ = lean_apply_2(v_k_3667_, v_ref_3669_, lean_box(0));
if (lean_obj_tag(v_r_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3681_; 
v_a_3673_ = lean_ctor_get(v_r_3672_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_r_3672_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3675_ = v_r_3672_;
v_isShared_3676_ = v_isSharedCheck_3681_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v_r_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3681_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3677_ = lean_io_basemutex_unlock(v_mutex_3670_);
lean_dec(v_mutex_3670_);
if (v_isShared_3676_ == 0)
{
v___x_3679_ = v___x_3675_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3673_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3690_; 
v_a_3682_ = lean_ctor_get(v_r_3672_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_r_3672_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3684_ = v_r_3672_;
v_isShared_3685_ = v_isSharedCheck_3690_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v_r_3672_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3690_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3686_ = lean_io_basemutex_unlock(v_mutex_3670_);
lean_dec(v_mutex_3670_);
if (v_isShared_3685_ == 0)
{
v___x_3688_ = v___x_3684_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3682_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_3666_ = stack[0].m_obj;
lean_object* v_k_3667_ = stack[1].m_obj;
lean_object* v_res_3691_;
v_res_3691_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3666_, v_k_3667_);
stack->m_obj
 = v_res_3691_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(lean_object* v_mutex_3692_, lean_object* v_k_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3692_, v_k_3693_);
return v_res_3695_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_object* v_00_u03b1_3696_, lean_object* v_00_u03b2_3697_, lean_object* v_mutex_3698_, lean_object* v_k_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_3698_, v_k_3699_);
return v___x_3701_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_3698_ = stack[2].m_obj;
lean_object* v_k_3699_ = stack[3].m_obj;
lean_object* v_res_3702_;
v_res_3702_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(lean_box(0), lean_box(0), v_mutex_3698_, v_k_3699_);
stack->m_obj
 = v_res_3702_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(lean_object* v_00_u03b1_3703_, lean_object* v_00_u03b2_3704_, lean_object* v_mutex_3705_, lean_object* v_k_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_3703_, v_00_u03b2_3704_, v_mutex_3705_, v_k_3706_);
return v_res_3708_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3709_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3709_);
return v___x_3711_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3709_ = stack[0].m_obj;
lean_object* v_res_3712_;
v_res_3712_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3709_);
stack->m_obj
 = v_res_3712_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_3713_);
return v_res_3715_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; lean_object* v_producers_3720_; lean_object* v_consumers_3721_; lean_object* v_capacity_3722_; lean_object* v_buf_3723_; lean_object* v_bufCount_3724_; lean_object* v_sendIdx_3725_; lean_object* v_recvIdx_3726_; uint8_t v_closed_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3750_; 
v___x_3719_ = lean_st_ref_get(v___y_3717_);
v_producers_3720_ = lean_ctor_get(v___x_3719_, 0);
v_consumers_3721_ = lean_ctor_get(v___x_3719_, 1);
v_capacity_3722_ = lean_ctor_get(v___x_3719_, 2);
v_buf_3723_ = lean_ctor_get(v___x_3719_, 3);
v_bufCount_3724_ = lean_ctor_get(v___x_3719_, 4);
v_sendIdx_3725_ = lean_ctor_get(v___x_3719_, 5);
v_recvIdx_3726_ = lean_ctor_get(v___x_3719_, 6);
v_closed_3727_ = lean_ctor_get_uint8(v___x_3719_, sizeof(void*)*7);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3729_ = v___x_3719_;
v_isShared_3730_ = v_isSharedCheck_3750_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_recvIdx_3726_);
lean_inc(v_sendIdx_3725_);
lean_inc(v_bufCount_3724_);
lean_inc(v_buf_3723_);
lean_inc(v_capacity_3722_);
lean_inc(v_consumers_3721_);
lean_inc(v_producers_3720_);
lean_dec(v___x_3719_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3750_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_3721_);
if (lean_obj_tag(v___x_3731_) == 1)
{
lean_object* v_val_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3747_; 
v_val_3732_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3734_ = v___x_3731_;
v_isShared_3735_ = v_isSharedCheck_3747_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_val_3732_);
lean_dec(v___x_3731_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3747_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v_fst_3736_; lean_object* v_snd_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
v_fst_3736_ = lean_ctor_get(v_val_3732_, 0);
lean_inc(v_fst_3736_);
v_snd_3737_ = lean_ctor_get(v_val_3732_, 1);
lean_inc(v_snd_3737_);
lean_dec(v_val_3732_);
v___x_3738_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_3736_, v_____do__lift_3716_);
lean_dec(v_fst_3736_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 1, v_snd_3737_);
v___x_3740_ = v___x_3729_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_producers_3720_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_snd_3737_);
lean_ctor_set(v_reuseFailAlloc_3746_, 2, v_capacity_3722_);
lean_ctor_set(v_reuseFailAlloc_3746_, 3, v_buf_3723_);
lean_ctor_set(v_reuseFailAlloc_3746_, 4, v_bufCount_3724_);
lean_ctor_set(v_reuseFailAlloc_3746_, 5, v_sendIdx_3725_);
lean_ctor_set(v_reuseFailAlloc_3746_, 6, v_recvIdx_3726_);
lean_ctor_set_uint8(v_reuseFailAlloc_3746_, sizeof(void*)*7, v_closed_3727_);
v___x_3740_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3744_; 
v___x_3741_ = lean_box(0);
v___x_3742_ = lean_st_ref_swap(v___y_3717_, v___x_3740_);
lean_dec(v___x_3742_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set_tag(v___x_3734_, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3741_);
v___x_3744_ = v___x_3734_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3741_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
lean_dec(v___x_3731_);
lean_del_object(v___x_3729_);
lean_dec(v_recvIdx_3726_);
lean_dec(v_sendIdx_3725_);
lean_dec(v_bufCount_3724_);
lean_dec_ref(v_buf_3723_);
lean_dec(v_capacity_3722_);
lean_dec_ref(v_producers_3720_);
v___x_3748_ = lean_box(0);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_3716_ = stack[0].m_num;
lean_object* v___y_3717_ = stack[1].m_obj;
lean_object* v_res_3751_;
v_res_3751_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3716_, v___y_3717_);
stack->m_obj
 = v_res_3751_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
uint8_t v_____do__lift_3671__boxed_3755_; lean_object* v_res_3756_; 
v_____do__lift_3671__boxed_3755_ = lean_unbox(v_____do__lift_3752_);
v_res_3756_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3671__boxed_3755_, v___y_3753_);
lean_dec(v___y_3753_);
return v_res_3756_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3757_, lean_object* v___f_3758_, uint8_t v_____do__lift_3759_, lean_object* v___y_3760_){
_start:
{
if (v_____do__lift_3759_ == 0)
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v_producers_3764_; lean_object* v_consumers_3765_; lean_object* v_capacity_3766_; lean_object* v_buf_3767_; lean_object* v_bufCount_3768_; lean_object* v_sendIdx_3769_; lean_object* v_recvIdx_3770_; uint8_t v_closed_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3785_; 
v___x_3762_ = lean_io_promise_new();
v___x_3763_ = lean_st_ref_take(v___y_3760_);
v_producers_3764_ = lean_ctor_get(v___x_3763_, 0);
v_consumers_3765_ = lean_ctor_get(v___x_3763_, 1);
v_capacity_3766_ = lean_ctor_get(v___x_3763_, 2);
v_buf_3767_ = lean_ctor_get(v___x_3763_, 3);
v_bufCount_3768_ = lean_ctor_get(v___x_3763_, 4);
v_sendIdx_3769_ = lean_ctor_get(v___x_3763_, 5);
v_recvIdx_3770_ = lean_ctor_get(v___x_3763_, 6);
v_closed_3771_ = lean_ctor_get_uint8(v___x_3763_, sizeof(void*)*7);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3773_ = v___x_3763_;
v_isShared_3774_ = v_isSharedCheck_3785_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_recvIdx_3770_);
lean_inc(v_sendIdx_3769_);
lean_inc(v_bufCount_3768_);
lean_inc(v_buf_3767_);
lean_inc(v_capacity_3766_);
lean_inc(v_consumers_3765_);
lean_inc(v_producers_3764_);
lean_dec(v___x_3763_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3785_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3779_; 
v___x_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3775_, 0, v_waiter_3757_);
lean_inc(v___x_3762_);
v___x_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3762_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = l_Std_Queue_enqueue___redArg(v___x_3776_, v_consumers_3765_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 1, v___x_3777_);
v___x_3779_ = v___x_3773_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_producers_3764_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3777_);
lean_ctor_set(v_reuseFailAlloc_3784_, 2, v_capacity_3766_);
lean_ctor_set(v_reuseFailAlloc_3784_, 3, v_buf_3767_);
lean_ctor_set(v_reuseFailAlloc_3784_, 4, v_bufCount_3768_);
lean_ctor_set(v_reuseFailAlloc_3784_, 5, v_sendIdx_3769_);
lean_ctor_set(v_reuseFailAlloc_3784_, 6, v_recvIdx_3770_);
lean_ctor_set_uint8(v_reuseFailAlloc_3784_, sizeof(void*)*7, v_closed_3771_);
v___x_3779_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3780_ = lean_st_ref_put(v___y_3760_, v___x_3779_);
v___x_3781_ = lean_io_promise_result_opt(v___x_3762_);
lean_dec(v___x_3762_);
v___x_3782_ = lean_unsigned_to_nat(0u);
v___x_3783_ = l_EIO_chainTask___redArg(v___x_3781_, v___f_3758_, v___x_3782_, v_____do__lift_3759_);
return v___x_3783_;
}
}
}
else
{
lean_object* v___x_3786_; lean_object* v_lose_3787_; lean_object* v___x_3788_; 
lean_dec_ref(v___f_3758_);
v___x_3786_ = lean_box(v_____do__lift_3759_);
v_lose_3787_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3787_, 0, v___x_3786_);
v___x_3788_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_3757_, v_lose_3787_, v___y_3760_);
lean_dec_ref(v_waiter_3757_);
return v___x_3788_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_3757_ = stack[0].m_obj;
lean_object* v___f_3758_ = stack[1].m_obj;
uint8_t v_____do__lift_3759_ = stack[2].m_num;
lean_object* v___y_3760_ = stack[3].m_obj;
lean_object* v_res_3789_;
v_res_3789_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3757_, v___f_3758_, v_____do__lift_3759_, v___y_3760_);
stack->m_obj
 = v_res_3789_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3790_, lean_object* v___f_3791_, lean_object* v_____do__lift_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
uint8_t v_____do__lift_3759__boxed_3795_; lean_object* v_res_3796_; 
v_____do__lift_3759__boxed_3795_ = lean_unbox(v_____do__lift_3792_);
v_res_3796_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_3790_, v___f_3791_, v_____do__lift_3759__boxed_3795_, v___y_3793_);
lean_dec(v___y_3793_);
return v_res_3796_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(lean_object* v___f_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; lean_object* v_bufCount_3801_; uint8_t v_closed_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3800_ = lean_st_ref_get(v___y_3798_);
v_bufCount_3801_ = lean_ctor_get(v___x_3800_, 4);
lean_inc(v_bufCount_3801_);
v_closed_3802_ = lean_ctor_get_uint8(v___x_3800_, sizeof(void*)*7);
lean_dec(v___x_3800_);
v___x_3803_ = lean_unsigned_to_nat(0u);
v___x_3804_ = lean_nat_dec_eq(v_bufCount_3801_, v___x_3803_);
lean_dec(v_bufCount_3801_);
if (v___x_3804_ == 0)
{
uint8_t v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3805_ = 1;
v___x_3806_ = lean_box(v___x_3805_);
lean_inc(v___y_3798_);
v___x_3807_ = lean_apply_3(v___f_3797_, v___x_3806_, v___y_3798_, lean_box(0));
return v___x_3807_;
}
else
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3808_ = lean_box(v_closed_3802_);
lean_inc(v___y_3798_);
v___x_3809_ = lean_apply_3(v___f_3797_, v___x_3808_, v___y_3798_, lean_box(0));
return v___x_3809_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3797_ = stack[0].m_obj;
lean_object* v___y_3798_ = stack[1].m_obj;
lean_object* v_res_3810_;
v_res_3810_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3797_, v___y_3798_);
stack->m_obj
 = v_res_3810_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v___f_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_3811_, v___y_3812_);
lean_dec(v___y_3812_);
return v_res_3814_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3817_, lean_object* v_ch_3818_, lean_object* v_x_3819_){
_start:
{
if (lean_obj_tag(v_x_3819_) == 0)
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
lean_dec_ref(v_ch_3818_);
lean_dec_ref(v_waiter_3817_);
v___x_3821_ = lean_box(0);
v___x_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
return v___x_3822_;
}
else
{
lean_object* v_val_3823_; uint8_t v___x_3824_; 
v_val_3823_ = lean_ctor_get(v_x_3819_, 0);
v___x_3824_ = lean_unbox(v_val_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___f_3825_; lean_object* v___x_3826_; 
lean_dec_ref(v_ch_3818_);
v___f_3825_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3826_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_3817_, v___f_3825_);
lean_dec_ref(v_waiter_3817_);
return v___x_3826_;
}
else
{
lean_object* v___x_3827_; 
v___x_3827_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3818_, v_waiter_3817_);
return v___x_3827_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_3817_ = stack[0].m_obj;
lean_object* v_ch_3818_ = stack[1].m_obj;
lean_object* v_x_3819_ = stack[2].m_obj;
lean_object* v_res_3828_;
v_res_3828_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3817_, v_ch_3818_, v_x_3819_);
stack->m_obj
 = v_res_3828_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3829_, lean_object* v_ch_3830_, lean_object* v_x_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_3829_, v_ch_3830_, v_x_3831_);
lean_dec(v_x_3831_);
return v_res_3833_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(lean_object* v_ch_3834_, lean_object* v_waiter_3835_){
_start:
{
lean_object* v___f_3837_; lean_object* v___f_3838_; lean_object* v___f_3839_; lean_object* v___x_3840_; 
lean_inc_ref(v_ch_3834_);
lean_inc_ref(v_waiter_3835_);
v___f_3837_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3837_, 0, v_waiter_3835_);
lean_closure_set(v___f_3837_, 1, v_ch_3834_);
v___f_3838_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_3838_, 0, v_waiter_3835_);
lean_closure_set(v___f_3838_, 1, v___f_3837_);
v___f_3839_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_3839_, 0, v___f_3838_);
v___x_3840_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_3834_, v___f_3839_);
return v___x_3840_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3834_ = stack[0].m_obj;
lean_object* v_waiter_3835_ = stack[1].m_obj;
lean_object* v_res_3841_;
v_res_3841_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3834_, v_waiter_3835_);
stack->m_obj
 = v_res_3841_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3842_, lean_object* v_waiter_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3842_, v_waiter_3843_);
return v_res_3845_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_object* v_00_u03b1_3846_, lean_object* v_ch_3847_, lean_object* v_waiter_3848_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_3847_, v_waiter_3848_);
return v___x_3850_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3847_ = stack[1].m_obj;
lean_object* v_waiter_3848_ = stack[2].m_obj;
lean_object* v_res_3851_;
v_res_3851_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(lean_box(0), v_ch_3847_, v_waiter_3848_);
stack->m_obj
 = v_res_3851_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3852_, lean_object* v_ch_3853_, lean_object* v_waiter_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(v_00_u03b1_3852_, v_ch_3853_, v_waiter_3854_);
return v_res_3856_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_3857_, lean_object* v_x_3858_){
_start:
{
if (lean_obj_tag(v_x_3858_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_x_3857_);
v_a_3860_ = lean_ctor_get(v_x_3858_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v_x_3858_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3862_ = v_x_3858_;
v_isShared_3863_ = v_isSharedCheck_3868_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v_x_3858_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3868_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
return v___x_3866_;
}
}
}
else
{
lean_object* v___x_3869_; 
lean_dec_ref_known(v_x_3858_, 1);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v_x_3857_);
return v___x_3869_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3857_ = stack[0].m_obj;
lean_object* v_x_3858_ = stack[1].m_obj;
lean_object* v_res_3870_;
v_res_3870_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3857_, v_x_3858_);
stack->m_obj
 = v_res_3870_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_3871_, lean_object* v_x_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_3871_, v_x_3872_);
return v_res_3874_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(lean_object* v___x_3875_, uint8_t v___x_3876_, lean_object* v___f_3877_, lean_object* v_____r_3878_, lean_object* v_st_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3882_ = lean_st_ref_swap(v___y_3880_, v_st_3879_);
lean_dec(v___x_3882_);
v___x_3883_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_3884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3875_, v___x_3876_, v___x_3883_, v___f_3877_);
return v___x_3884_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3875_ = stack[0].m_obj;
uint8_t v___x_3876_ = stack[1].m_num;
lean_object* v___f_3877_ = stack[2].m_obj;
lean_object* v_____r_3878_ = stack[3].m_obj;
lean_object* v_st_3879_ = stack[4].m_obj;
lean_object* v___y_3880_ = stack[5].m_obj;
lean_object* v_res_3885_;
v_res_3885_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3875_, v___x_3876_, v___f_3877_, v_____r_3878_, v_st_3879_, v___y_3880_);
stack->m_obj
 = v_res_3885_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v___x_3886_, lean_object* v___x_3887_, lean_object* v___f_3888_, lean_object* v_____r_3889_, lean_object* v_st_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v___x_6382__boxed_3893_; lean_object* v_res_3894_; 
v___x_6382__boxed_3893_ = lean_unbox(v___x_3887_);
v_res_3894_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3886_, v___x_6382__boxed_3893_, v___f_3888_, v_____r_3889_, v_st_3890_, v___y_3891_);
lean_dec(v___y_3891_);
return v_res_3894_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(lean_object* v_snd_3895_, lean_object* v_consumers_3896_, lean_object* v_capacity_3897_, lean_object* v_buf_3898_, lean_object* v___x_3899_, lean_object* v_sendIdx_3900_, lean_object* v___y_3901_, uint8_t v_closed_3902_, lean_object* v___f_3903_, lean_object* v_a_3904_, lean_object* v_x_3905_){
_start:
{
if (lean_obj_tag(v_x_3905_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v___f_3903_);
lean_dec(v___y_3901_);
lean_dec(v_sendIdx_3900_);
lean_dec(v___x_3899_);
lean_dec_ref(v_buf_3898_);
lean_dec(v_capacity_3897_);
lean_dec_ref(v_consumers_3896_);
lean_dec_ref(v_snd_3895_);
v_a_3907_ = lean_ctor_get(v_x_3905_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_x_3905_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3909_ = v_x_3905_;
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v_x_3905_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3915_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
return v___x_3913_;
}
}
}
else
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_dec_ref_known(v_x_3905_, 1);
v___x_3916_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3916_, 0, v_snd_3895_);
lean_ctor_set(v___x_3916_, 1, v_consumers_3896_);
lean_ctor_set(v___x_3916_, 2, v_capacity_3897_);
lean_ctor_set(v___x_3916_, 3, v_buf_3898_);
lean_ctor_set(v___x_3916_, 4, v___x_3899_);
lean_ctor_set(v___x_3916_, 5, v_sendIdx_3900_);
lean_ctor_set(v___x_3916_, 6, v___y_3901_);
lean_ctor_set_uint8(v___x_3916_, sizeof(void*)*7, v_closed_3902_);
v___x_3917_ = lean_box(0);
lean_inc(v_a_3904_);
v___x_3918_ = lean_apply_4(v___f_3903_, v___x_3917_, v___x_3916_, v_a_3904_, lean_box(0));
return v___x_3918_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_3895_ = stack[0].m_obj;
lean_object* v_consumers_3896_ = stack[1].m_obj;
lean_object* v_capacity_3897_ = stack[2].m_obj;
lean_object* v_buf_3898_ = stack[3].m_obj;
lean_object* v___x_3899_ = stack[4].m_obj;
lean_object* v_sendIdx_3900_ = stack[5].m_obj;
lean_object* v___y_3901_ = stack[6].m_obj;
uint8_t v_closed_3902_ = stack[7].m_num;
lean_object* v___f_3903_ = stack[8].m_obj;
lean_object* v_a_3904_ = stack[9].m_obj;
lean_object* v_x_3905_ = stack[10].m_obj;
lean_object* v_res_3919_;
v_res_3919_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3895_, v_consumers_3896_, v_capacity_3897_, v_buf_3898_, v___x_3899_, v_sendIdx_3900_, v___y_3901_, v_closed_3902_, v___f_3903_, v_a_3904_, v_x_3905_);
stack->m_obj
 = v_res_3919_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_snd_3920_, lean_object* v_consumers_3921_, lean_object* v_capacity_3922_, lean_object* v_buf_3923_, lean_object* v___x_3924_, lean_object* v_sendIdx_3925_, lean_object* v___y_3926_, lean_object* v_closed_3927_, lean_object* v___f_3928_, lean_object* v_a_3929_, lean_object* v_x_3930_, lean_object* v___y_3931_){
_start:
{
uint8_t v_closed_boxed_3932_; lean_object* v_res_3933_; 
v_closed_boxed_3932_ = lean_unbox(v_closed_3927_);
v_res_3933_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_3920_, v_consumers_3921_, v_capacity_3922_, v_buf_3923_, v___x_3924_, v_sendIdx_3925_, v___y_3926_, v_closed_boxed_3932_, v___f_3928_, v_a_3929_, v_x_3930_);
lean_dec(v_a_3929_);
return v_res_3933_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(lean_object* v___x_3934_, uint8_t v___x_3935_, lean_object* v_bufCount_3936_, lean_object* v_producers_3937_, lean_object* v_consumers_3938_, lean_object* v_capacity_3939_, lean_object* v_buf_3940_, lean_object* v_sendIdx_3941_, uint8_t v_closed_3942_, lean_object* v_a_3943_, uint8_t v___x_3944_, lean_object* v_recvIdx_3945_, lean_object* v_x_3946_){
_start:
{
if (lean_obj_tag(v_x_3946_) == 0)
{
lean_object* v___x_3948_; 
lean_dec(v_sendIdx_3941_);
lean_dec_ref(v_buf_3940_);
lean_dec(v_capacity_3939_);
lean_dec_ref(v_consumers_3938_);
lean_dec_ref(v_producers_3937_);
lean_dec(v___x_3934_);
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_x_3946_);
return v___x_3948_;
}
else
{
lean_object* v___f_3949_; lean_object* v___x_3950_; lean_object* v___f_3951_; lean_object* v___y_3953_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___f_3949_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3949_, 0, v_x_3946_);
v___x_3950_ = lean_box(v___x_3935_);
lean_inc_ref(v___f_3949_);
lean_inc(v___x_3934_);
v___f_3951_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_3951_, 0, v___x_3934_);
lean_closure_set(v___f_3951_, 1, v___x_3950_);
lean_closure_set(v___f_3951_, 2, v___f_3949_);
v___x_3976_ = lean_unsigned_to_nat(1u);
v___x_3977_ = lean_nat_add(v_recvIdx_3945_, v___x_3976_);
v___x_3978_ = lean_nat_dec_eq(v___x_3977_, v_capacity_3939_);
if (v___x_3978_ == 0)
{
v___y_3953_ = v___x_3977_;
goto v___jp_3952_;
}
else
{
lean_dec(v___x_3977_);
lean_inc(v___x_3934_);
v___y_3953_ = v___x_3934_;
goto v___jp_3952_;
}
v___jp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3954_ = lean_unsigned_to_nat(1u);
v___x_3955_ = lean_nat_sub(v_bufCount_3936_, v___x_3954_);
lean_inc(v___y_3953_);
lean_inc(v_sendIdx_3941_);
lean_inc(v___x_3955_);
lean_inc_ref(v_buf_3940_);
lean_inc(v_capacity_3939_);
lean_inc_ref(v_consumers_3938_);
lean_inc_ref(v_producers_3937_);
v___x_3956_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_3956_, 0, v_producers_3937_);
lean_ctor_set(v___x_3956_, 1, v_consumers_3938_);
lean_ctor_set(v___x_3956_, 2, v_capacity_3939_);
lean_ctor_set(v___x_3956_, 3, v_buf_3940_);
lean_ctor_set(v___x_3956_, 4, v___x_3955_);
lean_ctor_set(v___x_3956_, 5, v_sendIdx_3941_);
lean_ctor_set(v___x_3956_, 6, v___y_3953_);
lean_ctor_set_uint8(v___x_3956_, sizeof(void*)*7, v_closed_3942_);
v___x_3957_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3937_);
if (lean_obj_tag(v___x_3957_) == 1)
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3973_; 
lean_dec_ref_known(v___x_3956_, 7);
lean_dec_ref(v___f_3949_);
v_val_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_3973_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3973_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_fst_3962_; lean_object* v_snd_3963_; lean_object* v___x_3964_; lean_object* v___f_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v_fst_3962_ = lean_ctor_get(v_val_3958_, 0);
lean_inc(v_fst_3962_);
v_snd_3963_ = lean_ctor_get(v_val_3958_, 1);
lean_inc(v_snd_3963_);
lean_dec(v_val_3958_);
v___x_3964_ = lean_box(v_closed_3942_);
lean_inc(v_a_3943_);
v___f_3965_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3965_, 0, v_snd_3963_);
lean_closure_set(v___f_3965_, 1, v_consumers_3938_);
lean_closure_set(v___f_3965_, 2, v_capacity_3939_);
lean_closure_set(v___f_3965_, 3, v_buf_3940_);
lean_closure_set(v___f_3965_, 4, v___x_3955_);
lean_closure_set(v___f_3965_, 5, v_sendIdx_3941_);
lean_closure_set(v___f_3965_, 6, v___y_3953_);
lean_closure_set(v___f_3965_, 7, v___x_3964_);
lean_closure_set(v___f_3965_, 8, v___f_3951_);
lean_closure_set(v___f_3965_, 9, v_a_3943_);
v___x_3966_ = lean_box(v___x_3944_);
v___x_3967_ = lean_io_promise_resolve(v___x_3966_, v_fst_3962_);
lean_dec(v_fst_3962_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3967_);
v___x_3969_ = v___x_3960_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
v___x_3971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3934_, v___x_3935_, v___x_3970_, v___f_3965_);
return v___x_3971_;
}
}
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
lean_dec(v___x_3957_);
lean_dec(v___x_3955_);
lean_dec(v___y_3953_);
lean_dec_ref(v___f_3951_);
lean_dec(v_sendIdx_3941_);
lean_dec_ref(v_buf_3940_);
lean_dec(v_capacity_3939_);
lean_dec_ref(v_consumers_3938_);
v___x_3974_ = lean_box(0);
v___x_3975_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_3934_, v___x_3935_, v___f_3949_, v___x_3974_, v___x_3956_, v_a_3943_);
return v___x_3975_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3934_ = stack[0].m_obj;
uint8_t v___x_3935_ = stack[1].m_num;
lean_object* v_bufCount_3936_ = stack[2].m_obj;
lean_object* v_producers_3937_ = stack[3].m_obj;
lean_object* v_consumers_3938_ = stack[4].m_obj;
lean_object* v_capacity_3939_ = stack[5].m_obj;
lean_object* v_buf_3940_ = stack[6].m_obj;
lean_object* v_sendIdx_3941_ = stack[7].m_obj;
uint8_t v_closed_3942_ = stack[8].m_num;
lean_object* v_a_3943_ = stack[9].m_obj;
uint8_t v___x_3944_ = stack[10].m_num;
lean_object* v_recvIdx_3945_ = stack[11].m_obj;
lean_object* v_x_3946_ = stack[12].m_obj;
lean_object* v_res_3979_;
v_res_3979_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3934_, v___x_3935_, v_bufCount_3936_, v_producers_3937_, v_consumers_3938_, v_capacity_3939_, v_buf_3940_, v_sendIdx_3941_, v_closed_3942_, v_a_3943_, v___x_3944_, v_recvIdx_3945_, v_x_3946_);
stack->m_obj
 = v_res_3979_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(lean_object* v___x_3980_, lean_object* v___x_3981_, lean_object* v_bufCount_3982_, lean_object* v_producers_3983_, lean_object* v_consumers_3984_, lean_object* v_capacity_3985_, lean_object* v_buf_3986_, lean_object* v_sendIdx_3987_, lean_object* v_closed_3988_, lean_object* v_a_3989_, lean_object* v___x_3990_, lean_object* v_recvIdx_3991_, lean_object* v_x_3992_, lean_object* v___y_3993_){
_start:
{
uint8_t v___x_6490__boxed_3994_; uint8_t v_closed_boxed_3995_; uint8_t v___x_6491__boxed_3996_; lean_object* v_res_3997_; 
v___x_6490__boxed_3994_ = lean_unbox(v___x_3981_);
v_closed_boxed_3995_ = lean_unbox(v_closed_3988_);
v___x_6491__boxed_3996_ = lean_unbox(v___x_3990_);
v_res_3997_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_3980_, v___x_6490__boxed_3994_, v_bufCount_3982_, v_producers_3983_, v_consumers_3984_, v_capacity_3985_, v_buf_3986_, v_sendIdx_3987_, v_closed_boxed_3995_, v_a_3989_, v___x_6491__boxed_3996_, v_recvIdx_3991_, v_x_3992_);
lean_dec(v_recvIdx_3991_);
lean_dec(v_a_3989_);
lean_dec(v_bufCount_3982_);
return v_res_3997_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(lean_object* v_a_3998_, lean_object* v_x_3999_){
_start:
{
if (lean_obj_tag(v_x_3999_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4009_; 
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
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4038_; 
v_a_4010_ = lean_ctor_get(v_x_3999_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_x_3999_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4012_ = v_x_3999_;
v_isShared_4013_ = v_isSharedCheck_4038_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v_x_3999_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4038_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v_producers_4014_; lean_object* v_consumers_4015_; lean_object* v_capacity_4016_; lean_object* v_buf_4017_; lean_object* v_bufCount_4018_; lean_object* v_sendIdx_4019_; lean_object* v_recvIdx_4020_; uint8_t v_closed_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v_producers_4014_ = lean_ctor_get(v_a_4010_, 0);
lean_inc_ref(v_producers_4014_);
v_consumers_4015_ = lean_ctor_get(v_a_4010_, 1);
lean_inc_ref(v_consumers_4015_);
v_capacity_4016_ = lean_ctor_get(v_a_4010_, 2);
lean_inc(v_capacity_4016_);
v_buf_4017_ = lean_ctor_get(v_a_4010_, 3);
lean_inc_ref(v_buf_4017_);
v_bufCount_4018_ = lean_ctor_get(v_a_4010_, 4);
lean_inc(v_bufCount_4018_);
v_sendIdx_4019_ = lean_ctor_get(v_a_4010_, 5);
lean_inc(v_sendIdx_4019_);
v_recvIdx_4020_ = lean_ctor_get(v_a_4010_, 6);
lean_inc(v_recvIdx_4020_);
v_closed_4021_ = lean_ctor_get_uint8(v_a_4010_, sizeof(void*)*7);
lean_dec(v_a_4010_);
v___x_4022_ = lean_unsigned_to_nat(0u);
v___x_4023_ = lean_nat_dec_eq(v_bufCount_4018_, v___x_4022_);
if (v___x_4023_ == 0)
{
uint8_t v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___f_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4033_; 
v___x_4024_ = 1;
v___x_4025_ = lean_box(v___x_4023_);
v___x_4026_ = lean_box(v_closed_4021_);
v___x_4027_ = lean_box(v___x_4024_);
lean_inc(v_recvIdx_4020_);
lean_inc(v_a_3998_);
lean_inc_ref(v_buf_4017_);
v___f_4028_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed), 14, 12);
lean_closure_set(v___f_4028_, 0, v___x_4022_);
lean_closure_set(v___f_4028_, 1, v___x_4025_);
lean_closure_set(v___f_4028_, 2, v_bufCount_4018_);
lean_closure_set(v___f_4028_, 3, v_producers_4014_);
lean_closure_set(v___f_4028_, 4, v_consumers_4015_);
lean_closure_set(v___f_4028_, 5, v_capacity_4016_);
lean_closure_set(v___f_4028_, 6, v_buf_4017_);
lean_closure_set(v___f_4028_, 7, v_sendIdx_4019_);
lean_closure_set(v___f_4028_, 8, v___x_4026_);
lean_closure_set(v___f_4028_, 9, v_a_3998_);
lean_closure_set(v___f_4028_, 10, v___x_4027_);
lean_closure_set(v___f_4028_, 11, v_recvIdx_4020_);
v___x_4029_ = lean_array_fget(v_buf_4017_, v_recvIdx_4020_);
lean_dec(v_recvIdx_4020_);
lean_dec_ref(v_buf_4017_);
v___x_4030_ = lean_box(0);
v___x_4031_ = lean_st_ref_swap(v___x_4029_, v___x_4030_);
lean_dec(v___x_4029_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4031_);
v___x_4033_ = v___x_4012_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
v___x_4035_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4022_, v___x_4023_, v___x_4034_, v___f_4028_);
return v___x_4035_;
}
}
else
{
lean_object* v___x_4037_; 
lean_dec(v_recvIdx_4020_);
lean_dec(v_sendIdx_4019_);
lean_dec(v_bufCount_4018_);
lean_dec_ref(v_buf_4017_);
lean_dec(v_capacity_4016_);
lean_dec_ref(v_consumers_4015_);
lean_dec_ref(v_producers_4014_);
lean_del_object(v___x_4012_);
v___x_4037_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__3));
return v___x_4037_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3998_ = stack[0].m_obj;
lean_object* v_x_3999_ = stack[1].m_obj;
lean_object* v_res_4039_;
v_res_4039_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_3998_, v_x_3999_);
stack->m_obj
 = v_res_4039_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(lean_object* v_a_4040_, lean_object* v_x_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_4040_, v_x_4041_);
lean_dec(v_a_4040_);
return v_res_4043_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(lean_object* v_a_4044_){
_start:
{
lean_object* v___f_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_inc(v_a_4044_);
v___f_4046_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_4046_, 0, v_a_4044_);
v___x_4047_ = lean_unsigned_to_nat(0u);
v___x_4048_ = 0;
v___x_4049_ = lean_st_ref_get(v_a_4044_);
v___x_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
v___x_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
v___x_4052_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4047_, v___x_4048_, v___x_4051_, v___f_4046_);
return v___x_4052_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4044_ = stack[0].m_obj;
lean_object* v_res_4053_;
v_res_4053_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_4044_);
stack->m_obj
 = v_res_4053_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(lean_object* v_a_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_4054_);
lean_dec(v_a_4054_);
return v_res_4056_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_object* v_00_u03b1_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4058_ = stack[1].m_obj;
lean_object* v_res_4061_;
v_res_4061_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(lean_box(0), v_a_4058_);
stack->m_obj
 = v_res_4061_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4062_, lean_object* v_a_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_4062_, v_a_4063_);
lean_dec(v_a_4063_);
return v_res_4065_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(lean_object* v_ch_4066_, lean_object* v_x_4067_){
_start:
{
lean_object* v_val_4070_; lean_object* v___x_4072_; 
v___x_4072_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_4066_, v_x_4067_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
lean_ctor_set_tag(v___x_4075_, 1);
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
v_val_4070_ = v___x_4078_;
goto v___jp_4069_;
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
v_a_4081_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4072_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4072_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
lean_ctor_set_tag(v___x_4083_, 0);
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
v_val_4070_ = v___x_4086_;
goto v___jp_4069_;
}
}
}
v___jp_4069_:
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4071_, 0, v_val_4070_);
return v___x_4071_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4066_ = stack[0].m_obj;
lean_object* v_x_4067_ = stack[1].m_obj;
lean_object* v_res_4089_;
v_res_4089_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_4066_, v_x_4067_);
stack->m_obj
 = v_res_4089_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(lean_object* v_ch_4090_, lean_object* v_x_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(v_ch_4090_, v_x_4091_);
return v_res_4093_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(lean_object* v___y_4094_, lean_object* v___f_4095_, lean_object* v_x_4096_){
_start:
{
if (lean_obj_tag(v_x_4096_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4106_; 
lean_dec_ref(v___f_4095_);
v_a_4098_ = lean_ctor_get(v_x_4096_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_x_4096_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4100_ = v_x_4096_;
v_isShared_4101_ = v_isSharedCheck_4106_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v_x_4096_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4106_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
return v___x_4104_;
}
}
}
else
{
lean_object* v_a_4107_; uint8_t v___x_4108_; 
v_a_4107_ = lean_ctor_get(v_x_4096_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v_x_4096_, 1);
v___x_4108_ = lean_unbox(v_a_4107_);
lean_dec(v_a_4107_);
if (v___x_4108_ == 0)
{
lean_object* v___x_4109_; 
lean_dec_ref(v___f_4095_);
v___x_4109_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1));
return v___x_4109_;
}
else
{
lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4110_ = lean_unsigned_to_nat(0u);
v___x_4111_ = 0;
v___x_4112_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_4094_);
v___x_4113_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4110_, v___x_4111_, v___x_4112_, v___f_4095_);
return v___x_4113_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4094_ = stack[0].m_obj;
lean_object* v___f_4095_ = stack[1].m_obj;
lean_object* v_x_4096_ = stack[2].m_obj;
lean_object* v_res_4114_;
v_res_4114_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v___y_4094_, v___f_4095_, v_x_4096_);
stack->m_obj
 = v_res_4114_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(lean_object* v___y_4115_, lean_object* v___f_4116_, lean_object* v_x_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(v___y_4115_, v___f_4116_, v_x_4117_);
lean_dec(v___y_4115_);
return v_res_4119_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(lean_object* v___x_4120_, lean_object* v_x_4121_){
_start:
{
uint8_t v___y_4124_; 
if (lean_obj_tag(v_x_4121_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4136_; 
v_a_4128_ = lean_ctor_get(v_x_4121_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_x_4121_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4130_ = v_x_4121_;
v_isShared_4131_ = v_isSharedCheck_4136_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v_x_4121_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4136_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
lean_object* v___x_4134_; 
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
return v___x_4134_;
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v_bufCount_4138_; uint8_t v_closed_4139_; uint8_t v___x_4140_; 
v_a_4137_ = lean_ctor_get(v_x_4121_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v_x_4121_, 1);
v_bufCount_4138_ = lean_ctor_get(v_a_4137_, 4);
lean_inc(v_bufCount_4138_);
v_closed_4139_ = lean_ctor_get_uint8(v_a_4137_, sizeof(void*)*7);
lean_dec(v_a_4137_);
v___x_4140_ = lean_nat_dec_eq(v_bufCount_4138_, v___x_4120_);
lean_dec(v_bufCount_4138_);
if (v___x_4140_ == 0)
{
uint8_t v___x_4141_; 
v___x_4141_ = 1;
v___y_4124_ = v___x_4141_;
goto v___jp_4123_;
}
else
{
v___y_4124_ = v_closed_4139_;
goto v___jp_4123_;
}
}
v___jp_4123_:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = lean_box(v___y_4124_);
v___x_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
return v___x_4127_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4120_ = stack[0].m_obj;
lean_object* v_x_4121_ = stack[1].m_obj;
lean_object* v_res_4142_;
v_res_4142_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___x_4120_, v_x_4121_);
stack->m_obj
 = v_res_4142_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(lean_object* v___x_4143_, lean_object* v_x_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(v___x_4143_, v_x_4144_);
lean_dec(v___x_4143_);
return v_res_4146_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(lean_object* v___f_4149_, lean_object* v___y_4150_){
_start:
{
lean_object* v___f_4152_; lean_object* v___x_4153_; lean_object* v___f_4154_; uint8_t v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_inc(v___y_4150_);
v___f_4152_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4152_, 0, v___y_4150_);
lean_closure_set(v___f_4152_, 1, v___f_4149_);
v___x_4153_ = lean_unsigned_to_nat(0u);
v___f_4154_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___closed__0));
v___x_4155_ = 0;
v___x_4156_ = lean_st_ref_get(v___y_4150_);
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
v___x_4159_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4153_, v___x_4155_, v___x_4158_, v___f_4154_);
v___x_4160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4153_, v___x_4155_, v___x_4159_, v___f_4152_);
return v___x_4160_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4149_ = stack[0].m_obj;
lean_object* v___y_4150_ = stack[1].m_obj;
lean_object* v_res_4161_;
v_res_4161_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_4149_, v___y_4150_);
stack->m_obj
 = v_res_4161_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(lean_object* v___f_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(v___f_4162_, v___y_4163_);
lean_dec(v___y_4163_);
return v_res_4165_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(lean_object* v_producers_4166_, lean_object* v_capacity_4167_, lean_object* v_buf_4168_, lean_object* v_bufCount_4169_, lean_object* v_sendIdx_4170_, lean_object* v_recvIdx_4171_, uint8_t v_closed_4172_, lean_object* v___y_4173_, lean_object* v_x_4174_){
_start:
{
if (lean_obj_tag(v_x_4174_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4184_; 
lean_dec(v_recvIdx_4171_);
lean_dec(v_sendIdx_4170_);
lean_dec(v_bufCount_4169_);
lean_dec_ref(v_buf_4168_);
lean_dec(v_capacity_4167_);
lean_dec_ref(v_producers_4166_);
v_a_4176_ = lean_ctor_get(v_x_4174_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_x_4174_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4178_ = v_x_4174_;
v_isShared_4179_ = v_isSharedCheck_4184_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v_x_4174_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4184_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4182_; 
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
return v___x_4182_;
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v_a_4185_ = lean_ctor_get(v_x_4174_, 0);
lean_inc(v_a_4185_);
lean_dec_ref_known(v_x_4174_, 1);
v___x_4186_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_4186_, 0, v_producers_4166_);
lean_ctor_set(v___x_4186_, 1, v_a_4185_);
lean_ctor_set(v___x_4186_, 2, v_capacity_4167_);
lean_ctor_set(v___x_4186_, 3, v_buf_4168_);
lean_ctor_set(v___x_4186_, 4, v_bufCount_4169_);
lean_ctor_set(v___x_4186_, 5, v_sendIdx_4170_);
lean_ctor_set(v___x_4186_, 6, v_recvIdx_4171_);
lean_ctor_set_uint8(v___x_4186_, sizeof(void*)*7, v_closed_4172_);
v___x_4187_ = lean_st_ref_swap(v___y_4173_, v___x_4186_);
lean_dec(v___x_4187_);
v___x_4188_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4188_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_producers_4166_ = stack[0].m_obj;
lean_object* v_capacity_4167_ = stack[1].m_obj;
lean_object* v_buf_4168_ = stack[2].m_obj;
lean_object* v_bufCount_4169_ = stack[3].m_obj;
lean_object* v_sendIdx_4170_ = stack[4].m_obj;
lean_object* v_recvIdx_4171_ = stack[5].m_obj;
uint8_t v_closed_4172_ = stack[6].m_num;
lean_object* v___y_4173_ = stack[7].m_obj;
lean_object* v_x_4174_ = stack[8].m_obj;
lean_object* v_res_4189_;
v_res_4189_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_4166_, v_capacity_4167_, v_buf_4168_, v_bufCount_4169_, v_sendIdx_4170_, v_recvIdx_4171_, v_closed_4172_, v___y_4173_, v_x_4174_);
stack->m_obj
 = v_res_4189_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(lean_object* v_producers_4190_, lean_object* v_capacity_4191_, lean_object* v_buf_4192_, lean_object* v_bufCount_4193_, lean_object* v_sendIdx_4194_, lean_object* v_recvIdx_4195_, lean_object* v_closed_4196_, lean_object* v___y_4197_, lean_object* v_x_4198_, lean_object* v___y_4199_){
_start:
{
uint8_t v_closed_boxed_4200_; lean_object* v_res_4201_; 
v_closed_boxed_4200_ = lean_unbox(v_closed_4196_);
v_res_4201_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(v_producers_4190_, v_capacity_4191_, v_buf_4192_, v_bufCount_4193_, v_sendIdx_4194_, v_recvIdx_4195_, v_closed_boxed_4200_, v___y_4197_, v_x_4198_);
lean_dec(v___y_4197_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_4202_, lean_object* v_x_4203_, lean_object* v_head_4204_, lean_object* v_x_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_4202_, v_x_4203_, v_head_4204_, v_x_4205_);
return v_res_4207_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(lean_object* v_x_4208_, lean_object* v_x_4209_){
_start:
{
if (lean_obj_tag(v_x_4208_) == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4211_, 0, v_x_4209_);
v___x_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4211_);
return v___x_4212_;
}
else
{
lean_object* v_head_4213_; lean_object* v_tail_4214_; lean_object* v_waiter_4215_; lean_object* v___f_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v_head_4213_ = lean_ctor_get(v_x_4208_, 0);
lean_inc(v_head_4213_);
v_tail_4214_ = lean_ctor_get(v_x_4208_, 1);
lean_inc(v_tail_4214_);
lean_dec_ref_known(v_x_4208_, 2);
v_waiter_4215_ = lean_ctor_get(v_head_4213_, 1);
lean_inc(v_waiter_4215_);
v___f_4216_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4216_, 0, v_tail_4214_);
lean_closure_set(v___f_4216_, 1, v_x_4209_);
lean_closure_set(v___f_4216_, 2, v_head_4213_);
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = 0;
if (lean_obj_tag(v_waiter_4215_) == 0)
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1));
v___x_4220_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4217_, v___x_4218_, v___x_4219_, v___f_4216_);
return v___x_4220_;
}
else
{
lean_object* v_val_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4234_; 
v_val_4221_ = lean_ctor_get(v_waiter_4215_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_waiter_4215_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4223_ = v_waiter_4215_;
v_isShared_4224_ = v_isSharedCheck_4234_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_val_4221_);
lean_dec(v_waiter_4215_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4234_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v_finished_4225_; lean_object* v___f_4226_; lean_object* v___x_4227_; lean_object* v___x_4229_; 
v_finished_4225_ = lean_ctor_get(v_val_4221_, 0);
lean_inc(v_finished_4225_);
lean_dec(v_val_4221_);
v___f_4226_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2));
v___x_4227_ = lean_st_ref_get(v_finished_4225_);
lean_dec(v_finished_4225_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v___x_4227_);
v___x_4229_ = v___x_4223_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4229_);
v___x_4231_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4217_, v___x_4218_, v___x_4230_, v___f_4226_);
v___x_4232_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4217_, v___x_4218_, v___x_4231_, v___f_4216_);
return v___x_4232_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4208_ = stack[0].m_obj;
lean_object* v_x_4209_ = stack[1].m_obj;
lean_object* v_res_4235_;
v_res_4235_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4208_, v_x_4209_);
stack->m_obj
 = v_res_4235_;
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_4236_, lean_object* v_x_4237_, lean_object* v_head_4238_, lean_object* v_x_4239_){
_start:
{
if (lean_obj_tag(v_x_4239_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref(v_head_4238_);
lean_dec(v_x_4237_);
lean_dec(v_tail_4236_);
v_a_4241_ = lean_ctor_get(v_x_4239_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v_x_4239_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4243_ = v_x_4239_;
v_isShared_4244_ = v_isSharedCheck_4249_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v_x_4239_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4249_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4247_; 
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
return v___x_4247_;
}
}
}
else
{
lean_object* v_a_4250_; uint8_t v___x_4251_; 
v_a_4250_ = lean_ctor_get(v_x_4239_, 0);
lean_inc(v_a_4250_);
lean_dec_ref_known(v_x_4239_, 1);
v___x_4251_ = lean_unbox(v_a_4250_);
lean_dec(v_a_4250_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; 
lean_dec_ref(v_head_4238_);
v___x_4252_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4236_, v_x_4237_);
return v___x_4252_;
}
else
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4253_, 0, v_head_4238_);
lean_ctor_set(v___x_4253_, 1, v_x_4237_);
v___x_4254_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_4236_, v___x_4253_);
return v___x_4254_;
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_4236_ = stack[0].m_obj;
lean_object* v_x_4237_ = stack[1].m_obj;
lean_object* v_head_4238_ = stack[2].m_obj;
lean_object* v_x_4239_ = stack[3].m_obj;
lean_object* v_res_4255_;
v_res_4255_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_4236_, v_x_4237_, v_head_4238_, v_x_4239_);
stack->m_obj
 = v_res_4255_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(lean_object* v_x_4256_, lean_object* v_x_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4256_, v_x_4257_);
return v_res_4259_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(lean_object* v_x_4260_){
_start:
{
if (lean_obj_tag(v_x_4260_) == 0)
{
lean_object* v___x_4262_; 
v___x_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4262_, 0, v_x_4260_);
return v___x_4262_;
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4272_; 
v_a_4263_ = lean_ctor_get(v_x_4260_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_x_4260_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4265_ = v_x_4260_;
v_isShared_4266_ = v_isSharedCheck_4272_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v_x_4260_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4272_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4267_; lean_object* v___x_4269_; 
v___x_4267_ = l_List_reverse___redArg(v_a_4263_);
if (v_isShared_4266_ == 0)
{
lean_ctor_set(v___x_4265_, 0, v___x_4267_);
v___x_4269_ = v___x_4265_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4267_);
v___x_4269_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4270_; 
v___x_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4269_);
return v___x_4270_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4260_ = stack[0].m_obj;
lean_object* v_res_4273_;
v_res_4273_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4260_);
stack->m_obj
 = v_res_4273_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_x_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_4274_);
return v_res_4276_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(lean_object* v_a_4277_, lean_object* v___x_4278_, lean_object* v_x_4279_){
_start:
{
if (lean_obj_tag(v_x_4279_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4289_; 
lean_dec(v___x_4278_);
lean_dec(v_a_4277_);
v_a_4281_ = lean_ctor_get(v_x_4279_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v_x_4279_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4283_ = v_x_4279_;
v_isShared_4284_ = v_isSharedCheck_4289_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v_x_4279_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4289_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v___x_4287_; 
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
return v___x_4287_;
}
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4306_; 
v_a_4290_ = lean_ctor_get(v_x_4279_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_x_4279_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4292_ = v_x_4279_;
v_isShared_4293_ = v_isSharedCheck_4306_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v_x_4279_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4306_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
uint8_t v___x_4294_; 
v___x_4294_ = l_List_isEmpty___redArg(v_a_4277_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4297_; 
lean_dec(v___x_4278_);
v___x_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4295_, 0, v_a_4290_);
lean_ctor_set(v___x_4295_, 1, v_a_4277_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v___x_4295_);
v___x_4297_ = v___x_4292_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4295_);
v___x_4297_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
lean_object* v___x_4298_; 
v___x_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
return v___x_4298_;
}
}
else
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4303_; 
lean_dec(v_a_4277_);
v___x_4300_ = l_List_reverse___redArg(v_a_4290_);
v___x_4301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4278_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
if (v_isShared_4293_ == 0)
{
lean_ctor_set(v___x_4292_, 0, v___x_4301_);
v___x_4303_ = v___x_4292_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4301_);
v___x_4303_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
lean_object* v___x_4304_; 
v___x_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
return v___x_4304_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4277_ = stack[0].m_obj;
lean_object* v___x_4278_ = stack[1].m_obj;
lean_object* v_x_4279_ = stack[2].m_obj;
lean_object* v_res_4307_;
v_res_4307_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4277_, v___x_4278_, v_x_4279_);
stack->m_obj
 = v_res_4307_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(lean_object* v_a_4308_, lean_object* v___x_4309_, lean_object* v_x_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_4308_, v___x_4309_, v_x_4310_);
return v_res_4312_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(lean_object* v___x_4313_, lean_object* v_eList_4314_, lean_object* v___f_4315_, lean_object* v_x_4316_){
_start:
{
if (lean_obj_tag(v_x_4316_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4326_; 
lean_dec_ref(v___f_4315_);
lean_dec(v_eList_4314_);
lean_dec(v___x_4313_);
v_a_4318_ = lean_ctor_get(v_x_4316_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v_x_4316_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4320_ = v_x_4316_;
v_isShared_4321_ = v_isSharedCheck_4326_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v_x_4316_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4326_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4324_; 
v___x_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
return v___x_4324_;
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___f_4328_; lean_object* v___x_4329_; uint8_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v_a_4327_ = lean_ctor_get(v_x_4316_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v_x_4316_, 1);
lean_inc(v___x_4313_);
v___f_4328_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4328_, 0, v_a_4327_);
lean_closure_set(v___f_4328_, 1, v___x_4313_);
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = 0;
v___x_4331_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_4314_, v___x_4313_);
v___x_4332_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4329_, v___x_4330_, v___x_4331_, v___f_4315_);
v___x_4333_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4329_, v___x_4330_, v___x_4332_, v___f_4328_);
return v___x_4333_;
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4313_ = stack[0].m_obj;
lean_object* v_eList_4314_ = stack[1].m_obj;
lean_object* v___f_4315_ = stack[2].m_obj;
lean_object* v_x_4316_ = stack[3].m_obj;
lean_object* v_res_4334_;
v_res_4334_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v___x_4313_, v_eList_4314_, v___f_4315_, v_x_4316_);
stack->m_obj
 = v_res_4334_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(lean_object* v___x_4335_, lean_object* v_eList_4336_, lean_object* v___f_4337_, lean_object* v_x_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v___x_4335_, v_eList_4336_, v___f_4337_, v_x_4338_);
return v_res_4340_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(lean_object* v_q_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v_eList_4345_; lean_object* v_dList_4346_; lean_object* v___f_4347_; lean_object* v___x_4348_; lean_object* v___f_4349_; lean_object* v___x_4350_; uint8_t v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v_eList_4345_ = lean_ctor_get(v_q_4342_, 0);
lean_inc(v_eList_4345_);
v_dList_4346_ = lean_ctor_get(v_q_4342_, 1);
lean_inc(v_dList_4346_);
lean_dec_ref(v_q_4342_);
v___f_4347_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0));
v___x_4348_ = lean_box(0);
v___f_4349_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4349_, 0, v___x_4348_);
lean_closure_set(v___f_4349_, 1, v_eList_4345_);
lean_closure_set(v___f_4349_, 2, v___f_4347_);
v___x_4350_ = lean_unsigned_to_nat(0u);
v___x_4351_ = 0;
v___x_4352_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_4346_, v___x_4348_);
v___x_4353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4350_, v___x_4351_, v___x_4352_, v___f_4347_);
v___x_4354_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4350_, v___x_4351_, v___x_4353_, v___f_4349_);
return v___x_4354_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_4342_ = stack[0].m_obj;
lean_object* v___y_4343_ = stack[1].m_obj;
lean_object* v_res_4355_;
v_res_4355_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4342_, v___y_4343_);
stack->m_obj
 = v_res_4355_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(lean_object* v_q_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4356_, v___y_4357_);
lean_dec(v___y_4357_);
return v_res_4359_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(lean_object* v___y_4360_, lean_object* v_x_4361_){
_start:
{
if (lean_obj_tag(v_x_4361_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4371_; 
v_a_4363_ = lean_ctor_get(v_x_4361_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v_x_4361_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4365_ = v_x_4361_;
v_isShared_4366_ = v_isSharedCheck_4371_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v_x_4361_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4371_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_object* v___x_4369_; 
v___x_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
return v___x_4369_;
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v_producers_4373_; lean_object* v_consumers_4374_; lean_object* v_capacity_4375_; lean_object* v_buf_4376_; lean_object* v_bufCount_4377_; lean_object* v_sendIdx_4378_; lean_object* v_recvIdx_4379_; uint8_t v_closed_4380_; lean_object* v___x_4381_; lean_object* v___f_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v_a_4372_ = lean_ctor_get(v_x_4361_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v_x_4361_, 1);
v_producers_4373_ = lean_ctor_get(v_a_4372_, 0);
lean_inc_ref(v_producers_4373_);
v_consumers_4374_ = lean_ctor_get(v_a_4372_, 1);
lean_inc_ref(v_consumers_4374_);
v_capacity_4375_ = lean_ctor_get(v_a_4372_, 2);
lean_inc(v_capacity_4375_);
v_buf_4376_ = lean_ctor_get(v_a_4372_, 3);
lean_inc_ref(v_buf_4376_);
v_bufCount_4377_ = lean_ctor_get(v_a_4372_, 4);
lean_inc(v_bufCount_4377_);
v_sendIdx_4378_ = lean_ctor_get(v_a_4372_, 5);
lean_inc(v_sendIdx_4378_);
v_recvIdx_4379_ = lean_ctor_get(v_a_4372_, 6);
lean_inc(v_recvIdx_4379_);
v_closed_4380_ = lean_ctor_get_uint8(v_a_4372_, sizeof(void*)*7);
lean_dec(v_a_4372_);
v___x_4381_ = lean_box(v_closed_4380_);
lean_inc(v___y_4360_);
v___f_4382_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_4382_, 0, v_producers_4373_);
lean_closure_set(v___f_4382_, 1, v_capacity_4375_);
lean_closure_set(v___f_4382_, 2, v_buf_4376_);
lean_closure_set(v___f_4382_, 3, v_bufCount_4377_);
lean_closure_set(v___f_4382_, 4, v_sendIdx_4378_);
lean_closure_set(v___f_4382_, 5, v_recvIdx_4379_);
lean_closure_set(v___f_4382_, 6, v___x_4381_);
lean_closure_set(v___f_4382_, 7, v___y_4360_);
v___x_4383_ = lean_unsigned_to_nat(0u);
v___x_4384_ = 0;
v___x_4385_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_4374_, v___y_4360_);
v___x_4386_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4383_, v___x_4384_, v___x_4385_, v___f_4382_);
return v___x_4386_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4360_ = stack[0].m_obj;
lean_object* v_x_4361_ = stack[1].m_obj;
lean_object* v_res_4387_;
v_res_4387_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4360_, v_x_4361_);
stack->m_obj
 = v_res_4387_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(lean_object* v___y_4388_, lean_object* v_x_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(v___y_4388_, v_x_4389_);
lean_dec(v___y_4388_);
return v_res_4391_;
}
}
lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(lean_object* v___y_4392_){
_start:
{
lean_object* v___f_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
lean_inc(v___y_4392_);
v___f_4394_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4394_, 0, v___y_4392_);
v___x_4395_ = lean_unsigned_to_nat(0u);
v___x_4396_ = 0;
v___x_4397_ = lean_st_ref_get(v___y_4392_);
v___x_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
v___x_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4398_);
v___x_4400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4395_, v___x_4396_, v___x_4399_, v___f_4394_);
return v___x_4400_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4392_ = stack[0].m_obj;
lean_object* v_res_4401_;
v_res_4401_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4392_);
stack->m_obj
 = v_res_4401_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(v___y_4402_);
lean_dec(v___y_4402_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(lean_object* v_ch_4408_){
_start:
{
lean_object* v___f_4409_; lean_object* v___f_4410_; lean_object* v___f_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
lean_inc_ref_n(v_ch_4408_, 2);
v___f_4409_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4409_, 0, v_ch_4408_);
v___f_4410_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0));
v___f_4411_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1));
v___x_4412_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4412_, 0, lean_box(0));
lean_closure_set(v___x_4412_, 1, lean_box(0));
lean_closure_set(v___x_4412_, 2, v_ch_4408_);
lean_closure_set(v___x_4412_, 3, v___f_4410_);
v___x_4413_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4413_, 0, lean_box(0));
lean_closure_set(v___x_4413_, 1, lean_box(0));
lean_closure_set(v___x_4413_, 2, v_ch_4408_);
lean_closure_set(v___x_4413_, 3, v___f_4411_);
v___x_4414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___f_4409_);
lean_ctor_set(v___x_4414_, 2, v___x_4413_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(lean_object* v_00_u03b1_4415_, lean_object* v_ch_4416_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4416_);
return v___x_4417_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_object* v_00_u03b1_4418_, lean_object* v_q_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_4419_, v___y_4420_);
return v___x_4422_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_4419_ = stack[1].m_obj;
lean_object* v___y_4420_ = stack[2].m_obj;
lean_object* v_res_4423_;
v_res_4423_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(lean_box(0), v_q_4419_, v___y_4420_);
stack->m_obj
 = v_res_4423_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_4424_, lean_object* v_q_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_4424_, v_q_4425_, v___y_4426_);
lean_dec(v___y_4426_);
return v_res_4428_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_object* v_00_u03b1_4429_, lean_object* v_x_4430_, lean_object* v_x_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_4430_, v_x_4431_);
return v___x_4434_;
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4430_ = stack[1].m_obj;
lean_object* v_x_4431_ = stack[2].m_obj;
lean_object* v___y_4432_ = stack[3].m_obj;
lean_object* v_res_4435_;
v_res_4435_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(lean_box(0), v_x_4430_, v_x_4431_, v___y_4432_);
stack->m_obj
 = v_res_4435_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(lean_object* v_00_u03b1_4436_, lean_object* v_x_4437_, lean_object* v_x_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_4436_, v_x_4437_, v_x_4438_, v___y_4439_);
lean_dec(v___y_4439_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___redArg(lean_object* v_x_4442_){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = lean_obj_tag_nat(v_x_4442_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___redArg___boxed(lean_object* v_x_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Std_CloseableChannel_Flavors_ctorIdx___impl___redArg(v_x_4444_);
lean_dec_ref(v_x_4444_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl(lean_object* v_00_u03b1_4446_, lean_object* v_x_4447_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = lean_obj_tag_nat(v_x_4447_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorIdx___impl___boxed(lean_object* v_00_u03b1_4449_, lean_object* v_x_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Std_CloseableChannel_Flavors_ctorIdx___impl(v_00_u03b1_4449_, v_x_4450_);
lean_dec_ref(v_x_4450_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___redArg(lean_object* v_t_4452_, lean_object* v_k_4453_){
_start:
{
lean_object* v_ch_4454_; lean_object* v___x_4455_; 
v_ch_4454_ = lean_ctor_get(v_t_4452_, 0);
lean_inc_ref(v_ch_4454_);
lean_dec_ref(v_t_4452_);
v___x_4455_ = lean_apply_1(v_k_4453_, v_ch_4454_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim(lean_object* v_00_u03b1_4456_, lean_object* v_motive_4457_, lean_object* v_ctorIdx_4458_, lean_object* v_t_4459_, lean_object* v_h_4460_, lean_object* v_k_4461_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4459_, v_k_4461_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_ctorElim___boxed(lean_object* v_00_u03b1_4463_, lean_object* v_motive_4464_, lean_object* v_ctorIdx_4465_, lean_object* v_t_4466_, lean_object* v_h_4467_, lean_object* v_k_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Std_CloseableChannel_Flavors_ctorElim(v_00_u03b1_4463_, v_motive_4464_, v_ctorIdx_4465_, v_t_4466_, v_h_4467_, v_k_4468_);
lean_dec(v_ctorIdx_4465_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(lean_object* v_t_4470_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4471_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4470_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4471_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_unbounded_elim(lean_object* v_00_u03b1_4473_, lean_object* v_motive_4474_, lean_object* v_t_4475_, lean_object* v_h_4476_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4477_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4475_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_4477_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim___redArg(lean_object* v_t_4479_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4480_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4479_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_zero_elim(lean_object* v_00_u03b1_4482_, lean_object* v_motive_4483_, lean_object* v_t_4484_, lean_object* v_h_4485_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4486_){
_start:
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4484_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_4486_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim___redArg(lean_object* v_t_4488_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4489_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4488_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4489_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Flavors_bounded_elim(lean_object* v_00_u03b1_4491_, lean_object* v_motive_4492_, lean_object* v_t_4493_, lean_object* v_h_4494_, lean_object* v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4495_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_4493_, v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_4495_);
return v___x_4496_;
}
}
lean_object* l_Std_CloseableChannel_new___redArg(lean_object* v_capacity_4497_){
_start:
{
if (lean_obj_tag(v_capacity_4497_) == 0)
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4499_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
return v___x_4500_;
}
else
{
lean_object* v_val_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4518_; 
v_val_4501_ = lean_ctor_get(v_capacity_4497_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v_capacity_4497_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4503_ = v_capacity_4497_;
v_isShared_4504_ = v_isSharedCheck_4518_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_val_4501_);
lean_dec(v_capacity_4497_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4518_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v_zero_4505_; uint8_t v_isZero_4506_; 
v_zero_4505_ = lean_unsigned_to_nat(0u);
v_isZero_4506_ = lean_nat_dec_eq(v_val_4501_, v_zero_4505_);
if (v_isZero_4506_ == 1)
{
lean_object* v___x_4507_; lean_object* v___x_4509_; 
lean_dec(v_val_4501_);
v___x_4507_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 0, v___x_4507_);
v___x_4509_ = v___x_4503_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
else
{
lean_object* v_one_4511_; lean_object* v_n_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4516_; 
v_one_4511_ = lean_unsigned_to_nat(1u);
v_n_4512_ = lean_nat_sub(v_val_4501_, v_one_4511_);
lean_dec(v_val_4501_);
v___x_4513_ = lean_nat_add(v_n_4512_, v_one_4511_);
lean_dec(v_n_4512_);
v___x_4514_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v___x_4513_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set_tag(v___x_4503_, 2);
lean_ctor_set(v___x_4503_, 0, v___x_4514_);
v___x_4516_ = v___x_4503_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4514_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_4497_ = stack[0].m_obj;
lean_object* v_res_4519_;
v_res_4519_ = l_Std_CloseableChannel_new___redArg(v_capacity_4497_);
stack->m_obj
 = v_res_4519_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___redArg___boxed(lean_object* v_capacity_4520_, lean_object* v_a_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Std_CloseableChannel_new___redArg(v_capacity_4520_);
return v_res_4522_;
}
}
lean_object* l_Std_CloseableChannel_new(lean_object* v_00_u03b1_4523_, lean_object* v_capacity_4524_){
_start:
{
lean_object* v___x_4526_; 
v___x_4526_ = l_Std_CloseableChannel_new___redArg(v_capacity_4524_);
return v___x_4526_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_4524_ = stack[1].m_obj;
lean_object* v_res_4527_;
v_res_4527_ = l_Std_CloseableChannel_new(lean_box(0), v_capacity_4524_);
stack->m_obj
 = v_res_4527_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_new___boxed(lean_object* v_00_u03b1_4528_, lean_object* v_capacity_4529_, lean_object* v_a_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Std_CloseableChannel_new(v_00_u03b1_4528_, v_capacity_4529_);
return v_res_4531_;
}
}
uint8_t l_Std_CloseableChannel_trySend___redArg(lean_object* v_ch_4532_, lean_object* v_v_4533_){
_start:
{
switch(lean_obj_tag(v_ch_4532_))
{
case 0:
{
lean_object* v_ch_4535_; uint8_t v___x_4536_; 
v_ch_4535_ = lean_ctor_get(v_ch_4532_, 0);
lean_inc_ref(v_ch_4535_);
lean_dec_ref_known(v_ch_4532_, 1);
v___x_4536_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(v_ch_4535_, v_v_4533_);
return v___x_4536_;
}
case 1:
{
lean_object* v_ch_4537_; lean_object* v___x_4538_; uint8_t v___x_4539_; 
v_ch_4537_ = lean_ctor_get(v_ch_4532_, 0);
lean_inc_ref(v_ch_4537_);
lean_dec_ref_known(v_ch_4532_, 1);
v___x_4538_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(v_ch_4537_, v_v_4533_);
v___x_4539_ = lean_unbox(v___x_4538_);
lean_dec(v___x_4538_);
return v___x_4539_;
}
default: 
{
lean_object* v_ch_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v_ch_4540_ = lean_ctor_get(v_ch_4532_, 0);
lean_inc_ref(v_ch_4540_);
lean_dec_ref_known(v_ch_4532_, 1);
v___x_4541_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(v_ch_4540_, v_v_4533_);
v___x_4542_ = lean_unbox(v___x_4541_);
lean_dec(v___x_4541_);
return v___x_4542_;
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4532_ = stack[0].m_obj;
lean_object* v_v_4533_ = stack[1].m_obj;
uint8_t v_res_4543_;
v_res_4543_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4532_, v_v_4533_);
stack->m_num = v_res_4543_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___redArg___boxed(lean_object* v_ch_4544_, lean_object* v_v_4545_, lean_object* v_a_4546_){
_start:
{
uint8_t v_res_4547_; lean_object* v_r_4548_; 
v_res_4547_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4544_, v_v_4545_);
v_r_4548_ = lean_box(v_res_4547_);
return v_r_4548_;
}
}
uint8_t l_Std_CloseableChannel_trySend(lean_object* v_00_u03b1_4549_, lean_object* v_ch_4550_, lean_object* v_v_4551_){
_start:
{
uint8_t v___x_4553_; 
v___x_4553_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4550_, v_v_4551_);
return v___x_4553_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4550_ = stack[1].m_obj;
lean_object* v_v_4551_ = stack[2].m_obj;
uint8_t v_res_4554_;
v_res_4554_ = l_Std_CloseableChannel_trySend(lean_box(0), v_ch_4550_, v_v_4551_);
stack->m_num = v_res_4554_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_trySend___boxed(lean_object* v_00_u03b1_4555_, lean_object* v_ch_4556_, lean_object* v_v_4557_, lean_object* v_a_4558_){
_start:
{
uint8_t v_res_4559_; lean_object* v_r_4560_; 
v_res_4559_ = l_Std_CloseableChannel_trySend(v_00_u03b1_4555_, v_ch_4556_, v_v_4557_);
v_r_4560_ = lean_box(v_res_4559_);
return v_r_4560_;
}
}
lean_object* l_Std_CloseableChannel_send___redArg(lean_object* v_ch_4561_, lean_object* v_v_4562_){
_start:
{
switch(lean_obj_tag(v_ch_4561_))
{
case 0:
{
lean_object* v_ch_4564_; lean_object* v___x_4565_; 
v_ch_4564_ = lean_ctor_get(v_ch_4561_, 0);
lean_inc_ref(v_ch_4564_);
lean_dec_ref_known(v_ch_4561_, 1);
v___x_4565_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(v_ch_4564_, v_v_4562_);
return v___x_4565_;
}
case 1:
{
lean_object* v_ch_4566_; lean_object* v___x_4567_; 
v_ch_4566_ = lean_ctor_get(v_ch_4561_, 0);
lean_inc_ref(v_ch_4566_);
lean_dec_ref_known(v_ch_4561_, 1);
v___x_4567_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(v_ch_4566_, v_v_4562_);
return v___x_4567_;
}
default: 
{
lean_object* v_ch_4568_; lean_object* v___x_4569_; 
v_ch_4568_ = lean_ctor_get(v_ch_4561_, 0);
lean_inc_ref(v_ch_4568_);
lean_dec_ref_known(v_ch_4561_, 1);
v___x_4569_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_4568_, v_v_4562_);
return v___x_4569_;
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4561_ = stack[0].m_obj;
lean_object* v_v_4562_ = stack[1].m_obj;
lean_object* v_res_4570_;
v_res_4570_ = l_Std_CloseableChannel_send___redArg(v_ch_4561_, v_v_4562_);
stack->m_obj
 = v_res_4570_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___redArg___boxed(lean_object* v_ch_4571_, lean_object* v_v_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_res_4574_; 
v_res_4574_ = l_Std_CloseableChannel_send___redArg(v_ch_4571_, v_v_4572_);
return v_res_4574_;
}
}
lean_object* l_Std_CloseableChannel_send(lean_object* v_00_u03b1_4575_, lean_object* v_ch_4576_, lean_object* v_v_4577_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Std_CloseableChannel_send___redArg(v_ch_4576_, v_v_4577_);
return v___x_4579_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4576_ = stack[1].m_obj;
lean_object* v_v_4577_ = stack[2].m_obj;
lean_object* v_res_4580_;
v_res_4580_ = l_Std_CloseableChannel_send(lean_box(0), v_ch_4576_, v_v_4577_);
stack->m_obj
 = v_res_4580_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_send___boxed(lean_object* v_00_u03b1_4581_, lean_object* v_ch_4582_, lean_object* v_v_4583_, lean_object* v_a_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_Std_CloseableChannel_send(v_00_u03b1_4581_, v_ch_4582_, v_v_4583_);
return v_res_4585_;
}
}
lean_object* l_Std_CloseableChannel_close___redArg(lean_object* v_ch_4586_){
_start:
{
switch(lean_obj_tag(v_ch_4586_))
{
case 0:
{
lean_object* v_ch_4588_; lean_object* v___x_4589_; 
v_ch_4588_ = lean_ctor_get(v_ch_4586_, 0);
lean_inc_ref(v_ch_4588_);
lean_dec_ref_known(v_ch_4586_, 1);
v___x_4589_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_4588_);
return v___x_4589_;
}
case 1:
{
lean_object* v_ch_4590_; lean_object* v___x_4591_; 
v_ch_4590_ = lean_ctor_get(v_ch_4586_, 0);
lean_inc_ref(v_ch_4590_);
lean_dec_ref_known(v_ch_4586_, 1);
v___x_4591_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_4590_);
return v___x_4591_;
}
default: 
{
lean_object* v_ch_4592_; lean_object* v___x_4593_; 
v_ch_4592_ = lean_ctor_get(v_ch_4586_, 0);
lean_inc_ref(v_ch_4592_);
lean_dec_ref_known(v_ch_4586_, 1);
v___x_4593_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_4592_);
return v___x_4593_;
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4586_ = stack[0].m_obj;
lean_object* v_res_4594_;
v_res_4594_ = l_Std_CloseableChannel_close___redArg(v_ch_4586_);
stack->m_obj
 = v_res_4594_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___redArg___boxed(lean_object* v_ch_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_Std_CloseableChannel_close___redArg(v_ch_4595_);
return v_res_4597_;
}
}
lean_object* l_Std_CloseableChannel_close(lean_object* v_00_u03b1_4598_, lean_object* v_ch_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Std_CloseableChannel_close___redArg(v_ch_4599_);
return v___x_4601_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4599_ = stack[1].m_obj;
lean_object* v_res_4602_;
v_res_4602_ = l_Std_CloseableChannel_close(lean_box(0), v_ch_4599_);
stack->m_obj
 = v_res_4602_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_close___boxed(lean_object* v_00_u03b1_4603_, lean_object* v_ch_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Std_CloseableChannel_close(v_00_u03b1_4603_, v_ch_4604_);
return v_res_4606_;
}
}
uint8_t l_Std_CloseableChannel_isClosed___redArg(lean_object* v_ch_4607_){
_start:
{
switch(lean_obj_tag(v_ch_4607_))
{
case 0:
{
lean_object* v_ch_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; 
v_ch_4609_ = lean_ctor_get(v_ch_4607_, 0);
lean_inc_ref(v_ch_4609_);
lean_dec_ref_known(v_ch_4607_, 1);
v___x_4610_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(v_ch_4609_);
v___x_4611_ = lean_unbox(v___x_4610_);
lean_dec(v___x_4610_);
return v___x_4611_;
}
case 1:
{
lean_object* v_ch_4612_; lean_object* v___x_4613_; uint8_t v___x_4614_; 
v_ch_4612_ = lean_ctor_get(v_ch_4607_, 0);
lean_inc_ref(v_ch_4612_);
lean_dec_ref_known(v_ch_4607_, 1);
v___x_4613_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_4612_);
v___x_4614_ = lean_unbox(v___x_4613_);
lean_dec(v___x_4613_);
return v___x_4614_;
}
default: 
{
lean_object* v_ch_4615_; lean_object* v___x_4616_; uint8_t v___x_4617_; 
v_ch_4615_ = lean_ctor_get(v_ch_4607_, 0);
lean_inc_ref(v_ch_4615_);
lean_dec_ref_known(v_ch_4607_, 1);
v___x_4616_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_4615_);
v___x_4617_ = lean_unbox(v___x_4616_);
lean_dec(v___x_4616_);
return v___x_4617_;
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4607_ = stack[0].m_obj;
uint8_t v_res_4618_;
v_res_4618_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4607_);
stack->m_num = v_res_4618_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___redArg___boxed(lean_object* v_ch_4619_, lean_object* v_a_4620_){
_start:
{
uint8_t v_res_4621_; lean_object* v_r_4622_; 
v_res_4621_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4619_);
v_r_4622_ = lean_box(v_res_4621_);
return v_r_4622_;
}
}
uint8_t l_Std_CloseableChannel_isClosed(lean_object* v_00_u03b1_4623_, lean_object* v_ch_4624_){
_start:
{
uint8_t v___x_4626_; 
v___x_4626_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_4624_);
return v___x_4626_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4624_ = stack[1].m_obj;
uint8_t v_res_4627_;
v_res_4627_ = l_Std_CloseableChannel_isClosed(lean_box(0), v_ch_4624_);
stack->m_num = v_res_4627_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_isClosed___boxed(lean_object* v_00_u03b1_4628_, lean_object* v_ch_4629_, lean_object* v_a_4630_){
_start:
{
uint8_t v_res_4631_; lean_object* v_r_4632_; 
v_res_4631_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_4628_, v_ch_4629_);
v_r_4632_ = lean_box(v_res_4631_);
return v_r_4632_;
}
}
lean_object* l_Std_CloseableChannel_tryRecv___redArg(lean_object* v_ch_4633_){
_start:
{
switch(lean_obj_tag(v_ch_4633_))
{
case 0:
{
lean_object* v_ch_4635_; lean_object* v___x_4636_; 
v_ch_4635_ = lean_ctor_get(v_ch_4633_, 0);
lean_inc_ref(v_ch_4635_);
lean_dec_ref_known(v_ch_4633_, 1);
v___x_4636_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_4635_);
return v___x_4636_;
}
case 1:
{
lean_object* v_ch_4637_; lean_object* v___x_4638_; 
v_ch_4637_ = lean_ctor_get(v_ch_4633_, 0);
lean_inc_ref(v_ch_4637_);
lean_dec_ref_known(v_ch_4633_, 1);
v___x_4638_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_4637_);
return v___x_4638_;
}
default: 
{
lean_object* v_ch_4639_; lean_object* v___x_4640_; 
v_ch_4639_ = lean_ctor_get(v_ch_4633_, 0);
lean_inc_ref(v_ch_4639_);
lean_dec_ref_known(v_ch_4633_, 1);
v___x_4640_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_4639_);
return v___x_4640_;
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4633_ = stack[0].m_obj;
lean_object* v_res_4641_;
v_res_4641_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4633_);
stack->m_obj
 = v_res_4641_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___redArg___boxed(lean_object* v_ch_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4642_);
return v_res_4644_;
}
}
lean_object* l_Std_CloseableChannel_tryRecv(lean_object* v_00_u03b1_4645_, lean_object* v_ch_4646_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_4646_);
return v___x_4648_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4646_ = stack[1].m_obj;
lean_object* v_res_4649_;
v_res_4649_ = l_Std_CloseableChannel_tryRecv(lean_box(0), v_ch_4646_);
stack->m_obj
 = v_res_4649_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_tryRecv___boxed(lean_object* v_00_u03b1_4650_, lean_object* v_ch_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_4650_, v_ch_4651_);
return v_res_4653_;
}
}
lean_object* l_Std_CloseableChannel_recv___redArg(lean_object* v_ch_4654_){
_start:
{
switch(lean_obj_tag(v_ch_4654_))
{
case 0:
{
lean_object* v_ch_4656_; lean_object* v___x_4657_; 
v_ch_4656_ = lean_ctor_get(v_ch_4654_, 0);
lean_inc_ref(v_ch_4656_);
lean_dec_ref_known(v_ch_4654_, 1);
v___x_4657_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_4656_);
return v___x_4657_;
}
case 1:
{
lean_object* v_ch_4658_; lean_object* v___x_4659_; 
v_ch_4658_ = lean_ctor_get(v_ch_4654_, 0);
lean_inc_ref(v_ch_4658_);
lean_dec_ref_known(v_ch_4654_, 1);
v___x_4659_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_4658_);
return v___x_4659_;
}
default: 
{
lean_object* v_ch_4660_; lean_object* v___x_4661_; 
v_ch_4660_ = lean_ctor_get(v_ch_4654_, 0);
lean_inc_ref(v_ch_4660_);
lean_dec_ref_known(v_ch_4654_, 1);
v___x_4661_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_4660_);
return v___x_4661_;
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4654_ = stack[0].m_obj;
lean_object* v_res_4662_;
v_res_4662_ = l_Std_CloseableChannel_recv___redArg(v_ch_4654_);
stack->m_obj
 = v_res_4662_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___redArg___boxed(lean_object* v_ch_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l_Std_CloseableChannel_recv___redArg(v_ch_4663_);
return v_res_4665_;
}
}
lean_object* l_Std_CloseableChannel_recv(lean_object* v_00_u03b1_4666_, lean_object* v_ch_4667_){
_start:
{
lean_object* v___x_4669_; 
v___x_4669_ = l_Std_CloseableChannel_recv___redArg(v_ch_4667_);
return v___x_4669_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4667_ = stack[1].m_obj;
lean_object* v_res_4670_;
v_res_4670_ = l_Std_CloseableChannel_recv(lean_box(0), v_ch_4667_);
stack->m_obj
 = v_res_4670_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recv___boxed(lean_object* v_00_u03b1_4671_, lean_object* v_ch_4672_, lean_object* v_a_4673_){
_start:
{
lean_object* v_res_4674_; 
v_res_4674_ = l_Std_CloseableChannel_recv(v_00_u03b1_4671_, v_ch_4672_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector___redArg(lean_object* v_ch_4675_){
_start:
{
switch(lean_obj_tag(v_ch_4675_))
{
case 0:
{
lean_object* v_ch_4676_; lean_object* v___x_4677_; 
v_ch_4676_ = lean_ctor_get(v_ch_4675_, 0);
lean_inc_ref(v_ch_4676_);
lean_dec_ref_known(v_ch_4675_, 1);
v___x_4677_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_4676_);
return v___x_4677_;
}
case 1:
{
lean_object* v_ch_4678_; lean_object* v___x_4679_; 
v_ch_4678_ = lean_ctor_get(v_ch_4675_, 0);
lean_inc_ref(v_ch_4678_);
lean_dec_ref_known(v_ch_4675_, 1);
v___x_4679_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_4678_);
return v___x_4679_;
}
default: 
{
lean_object* v_ch_4680_; lean_object* v___x_4681_; 
v_ch_4680_ = lean_ctor_get(v_ch_4675_, 0);
lean_inc_ref(v_ch_4680_);
lean_dec_ref_known(v_ch_4675_, 1);
v___x_4681_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(v_ch_4680_);
return v___x_4681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_recvSelector(lean_object* v_00_u03b1_4682_, lean_object* v_ch_4683_){
_start:
{
lean_object* v___x_4684_; 
v___x_4684_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_4683_);
return v___x_4684_;
}
}
static lean_object* _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4685_ = lean_box(0);
v___x_4686_ = lean_task_pure(v___x_4685_);
return v___x_4686_;
}
}
lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0(lean_object* v_f_4687_, lean_object* v_ch_4688_, lean_object* v_prio_4689_, lean_object* v_x_4690_){
_start:
{
if (lean_obj_tag(v_x_4690_) == 0)
{
lean_object* v___x_4692_; 
lean_dec(v_prio_4689_);
lean_dec_ref(v_ch_4688_);
lean_dec_ref(v_f_4687_);
v___x_4692_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_4692_;
}
else
{
lean_object* v_val_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v_val_4693_ = lean_ctor_get(v_x_4690_, 0);
lean_inc(v_val_4693_);
lean_dec_ref_known(v_x_4690_, 1);
lean_inc_ref(v_f_4687_);
v___x_4694_ = lean_apply_2(v_f_4687_, v_val_4693_, lean_box(0));
v___x_4695_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4687_, v_ch_4688_, v_prio_4689_);
return v___x_4695_;
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_forAsync___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4687_ = stack[0].m_obj;
lean_object* v_ch_4688_ = stack[1].m_obj;
lean_object* v_prio_4689_ = stack[2].m_obj;
lean_object* v_x_4690_ = stack[3].m_obj;
lean_object* v_res_4696_;
v_res_4696_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4687_, v_ch_4688_, v_prio_4689_, v_x_4690_);
stack->m_obj
 = v_res_4696_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(lean_object* v_f_4697_, lean_object* v_ch_4698_, lean_object* v_prio_4699_, lean_object* v_x_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(v_f_4697_, v_ch_4698_, v_prio_4699_, v_x_4700_);
return v_res_4702_;
}
}
lean_object* l_Std_CloseableChannel_forAsync___redArg(lean_object* v_f_4703_, lean_object* v_ch_4704_, lean_object* v_prio_4705_){
_start:
{
lean_object* v___f_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; lean_object* v___x_4710_; 
lean_inc(v_prio_4705_);
lean_inc_ref(v_ch_4704_);
v___f_4707_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4707_, 0, v_f_4703_);
lean_closure_set(v___f_4707_, 1, v_ch_4704_);
lean_closure_set(v___f_4707_, 2, v_prio_4705_);
v___x_4708_ = l_Std_CloseableChannel_recv___redArg(v_ch_4704_);
v___x_4709_ = 0;
v___x_4710_ = lean_io_bind_task(v___x_4708_, v___f_4707_, v_prio_4705_, v___x_4709_);
return v___x_4710_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_forAsync___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4703_ = stack[0].m_obj;
lean_object* v_ch_4704_ = stack[1].m_obj;
lean_object* v_prio_4705_ = stack[2].m_obj;
lean_object* v_res_4711_;
v_res_4711_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4703_, v_ch_4704_, v_prio_4705_);
stack->m_obj
 = v_res_4711_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___redArg___boxed(lean_object* v_f_4712_, lean_object* v_ch_4713_, lean_object* v_prio_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v_res_4716_; 
v_res_4716_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4712_, v_ch_4713_, v_prio_4714_);
return v_res_4716_;
}
}
lean_object* l_Std_CloseableChannel_forAsync(lean_object* v_00_u03b1_4717_, lean_object* v_f_4718_, lean_object* v_ch_4719_, lean_object* v_prio_4720_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Std_CloseableChannel_forAsync___redArg(v_f_4718_, v_ch_4719_, v_prio_4720_);
return v___x_4722_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_forAsync_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4718_ = stack[1].m_obj;
lean_object* v_ch_4719_ = stack[2].m_obj;
lean_object* v_prio_4720_ = stack[3].m_obj;
lean_object* v_res_4723_;
v_res_4723_ = l_Std_CloseableChannel_forAsync(lean_box(0), v_f_4718_, v_ch_4719_, v_prio_4720_);
stack->m_obj
 = v_res_4723_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_forAsync___boxed(lean_object* v_00_u03b1_4724_, lean_object* v_f_4725_, lean_object* v_ch_4726_, lean_object* v_prio_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Std_CloseableChannel_forAsync(v_00_u03b1_4724_, v_f_4725_, v_ch_4726_, v_prio_4727_);
return v_res_4729_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(lean_object* v_x_4730_){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = lean_box(0);
v___x_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
return v___x_4733_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4730_ = stack[0].m_obj;
lean_object* v_res_4734_;
v_res_4734_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(v_x_4730_);
stack->m_obj
 = v_res_4734_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0___boxed(lean_object* v_x_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v_res_4737_; 
v_res_4737_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___lam__0(v_x_4735_);
lean_dec_ref(v_x_4735_);
return v_res_4737_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg(){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__2));
return v___x_4744_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4745_;
v_res_4745_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
stack->m_obj
 = v_res_4745_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object* v___dummy_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
return v_res_4747_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4748_; 
v___x_4748_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg();
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_4749_, lean_object* v_inst_4750_){
_start:
{
lean_object* v___x_4751_; 
v___x_4751_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_4752_, lean_object* v_inst_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_4752_, v_inst_4753_);
lean_dec(v_inst_4753_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object* v_a_4755_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4756_, 0, v_a_4755_);
return v___x_4756_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object* v___f_4757_, lean_object* v_x_4758_){
_start:
{
if (lean_obj_tag(v_x_4758_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4768_; 
lean_dec_ref(v___f_4757_);
v_a_4760_ = lean_ctor_get(v_x_4758_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v_x_4758_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4762_ = v_x_4758_;
v_isShared_4763_ = v_isSharedCheck_4768_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v_x_4758_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4768_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
lean_object* v___x_4766_; 
v___x_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
return v___x_4766_;
}
}
}
else
{
lean_object* v_a_4769_; 
v_a_4769_ = lean_ctor_get(v_x_4758_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v_x_4758_, 1);
if (lean_obj_tag(v_a_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4778_; 
lean_dec_ref(v___f_4757_);
v_a_4770_ = lean_ctor_get(v_a_4769_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v_a_4769_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4772_ = v_a_4769_;
v_isShared_4773_ = v_isSharedCheck_4778_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v_a_4769_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4778_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
lean_object* v___x_4776_; 
v___x_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4775_);
return v___x_4776_;
}
}
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4780_; uint8_t v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v_a_4779_ = lean_ctor_get(v_a_4769_, 0);
lean_inc(v_a_4779_);
lean_dec_ref_known(v_a_4769_, 1);
v___x_4780_ = lean_unsigned_to_nat(0u);
v___x_4781_ = 0;
v___x_4782_ = lean_task_map(v___f_4757_, v_a_4779_, v___x_4780_, v___x_4781_);
v___x_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
return v___x_4783_;
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4757_ = stack[0].m_obj;
lean_object* v_x_4758_ = stack[1].m_obj;
lean_object* v_res_4784_;
v_res_4784_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_4757_, v_x_4758_);
stack->m_obj
 = v_res_4784_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object* v___f_4785_, lean_object* v_x_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_4785_, v_x_4786_);
return v_res_4788_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object* v___f_4789_, lean_object* v_receiver_4790_){
_start:
{
lean_object* v___x_4792_; uint8_t v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4792_ = lean_unsigned_to_nat(0u);
v___x_4793_ = 0;
v___x_4794_ = l_Std_CloseableChannel_recv___redArg(v_receiver_4790_);
v___x_4795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
v___x_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4795_);
v___x_4797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4796_);
v___x_4798_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4792_, v___x_4793_, v___x_4797_, v___f_4789_);
return v___x_4798_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4789_ = stack[0].m_obj;
lean_object* v_receiver_4790_ = stack[1].m_obj;
lean_object* v_res_4799_;
v_res_4799_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_4789_, v_receiver_4790_);
stack->m_obj
 = v_res_4799_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object* v___f_4800_, lean_object* v_receiver_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_4800_, v_receiver_4801_);
return v_res_4803_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg(){
_start:
{
lean_object* v___f_4810_; 
v___f_4810_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___closed__2));
return v___f_4810_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4811_;
v_res_4811_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
stack->m_obj
 = v_res_4811_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object* v___dummy_4812_){
_start:
{
lean_object* v_res_4813_; 
v_res_4813_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
return v_res_4813_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4814_; 
v___x_4814_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___redArg();
return v___x_4814_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_4815_, lean_object* v_inst_4816_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_4818_, lean_object* v_inst_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_4818_, v_inst_4819_);
lean_dec(v_inst_4819_);
return v_res_4820_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_4822_, lean_object* v_x_4823_){
_start:
{
if (lean_obj_tag(v_x_4823_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4833_; 
lean_dec_ref(v___f_4822_);
v_a_4825_ = lean_ctor_get(v_x_4823_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v_x_4823_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4827_ = v_x_4823_;
v_isShared_4828_ = v_isSharedCheck_4833_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v_x_4823_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4833_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
lean_object* v___x_4831_; 
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
return v___x_4831_;
}
}
}
else
{
lean_object* v_a_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; uint8_t v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v_a_4834_ = lean_ctor_get(v_x_4823_, 0);
lean_inc(v_a_4834_);
lean_dec_ref_known(v_x_4823_, 1);
v___x_4835_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___closed__0));
v___x_4836_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4836_, 0, lean_box(0));
lean_closure_set(v___x_4836_, 1, lean_box(0));
lean_closure_set(v___x_4836_, 2, lean_box(0));
lean_closure_set(v___x_4836_, 3, v___x_4835_);
lean_closure_set(v___x_4836_, 4, v___f_4822_);
v___x_4837_ = lean_alloc_closure((void*)(l_Except_mapError), 5, 4);
lean_closure_set(v___x_4837_, 0, lean_box(0));
lean_closure_set(v___x_4837_, 1, lean_box(0));
lean_closure_set(v___x_4837_, 2, lean_box(0));
lean_closure_set(v___x_4837_, 3, v___x_4836_);
v___x_4838_ = lean_unsigned_to_nat(0u);
v___x_4839_ = 0;
v___x_4840_ = lean_task_map(v___x_4837_, v_a_4834_, v___x_4838_, v___x_4839_);
v___x_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
return v___x_4841_;
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4822_ = stack[0].m_obj;
lean_object* v_x_4823_ = stack[1].m_obj;
lean_object* v_res_4842_;
v_res_4842_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_4822_, v_x_4823_);
stack->m_obj
 = v_res_4842_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_4843_, lean_object* v_x_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_4843_, v_x_4844_);
return v_res_4846_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v___f_4847_, lean_object* v_receiver_4848_, lean_object* v_x_4849_){
_start:
{
lean_object* v___x_4851_; uint8_t v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4851_ = lean_unsigned_to_nat(0u);
v___x_4852_ = 0;
v___x_4853_ = l_Std_CloseableChannel_send___redArg(v_receiver_4848_, v_x_4849_);
v___x_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
v___x_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
v___x_4856_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4851_, v___x_4852_, v___x_4855_, v___f_4847_);
return v___x_4856_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4847_ = stack[0].m_obj;
lean_object* v_receiver_4848_ = stack[1].m_obj;
lean_object* v_x_4849_ = stack[2].m_obj;
lean_object* v_res_4857_;
v_res_4857_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(v___f_4847_, v_receiver_4848_, v_x_4849_);
stack->m_obj
 = v_res_4857_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object* v___f_4858_, lean_object* v_receiver_4859_, lean_object* v_x_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__0(v___f_4858_, v_receiver_4859_, v_x_4860_);
return v_res_4862_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v_x_4863_){
_start:
{
lean_object* v___x_4865_; 
v___x_4865_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4865_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4863_ = stack[0].m_obj;
lean_object* v_res_4866_;
v_res_4866_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(v_x_4863_);
stack->m_obj
 = v_res_4866_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v_x_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__2(v_x_4867_);
lean_dec_ref(v_x_4867_);
return v_res_4869_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(lean_object* v___f_4870_, lean_object* v_socket_4871_, lean_object* v_x_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = lean_apply_3(v___f_4870_, v_socket_4871_, v___y_4873_, lean_box(0));
return v___x_4875_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4870_ = stack[0].m_obj;
lean_object* v_socket_4871_ = stack[1].m_obj;
lean_object* v_x_4872_ = stack[2].m_obj;
lean_object* v___y_4873_ = stack[3].m_obj;
lean_object* v_res_4876_;
v_res_4876_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(v___f_4870_, v_socket_4871_, v_x_4872_, v___y_4873_);
stack->m_obj
 = v_res_4876_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object* v___f_4877_, lean_object* v_socket_4878_, lean_object* v_x_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3(v___f_4877_, v_socket_4878_, v_x_4879_, v___y_4880_);
return v_res_4882_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(lean_object* v___f_4883_, lean_object* v___x_4884_, lean_object* v_socket_4885_, lean_object* v_data_4886_){
_start:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; uint8_t v___x_4891_; 
v___x_4888_ = lean_unsigned_to_nat(0u);
v___x_4889_ = lean_array_get_size(v_data_4886_);
v___x_4890_ = lean_box(0);
v___x_4891_ = lean_nat_dec_lt(v___x_4888_, v___x_4889_);
if (v___x_4891_ == 0)
{
lean_object* v___x_4892_; 
lean_dec_ref(v_data_4886_);
lean_dec_ref(v_socket_4885_);
lean_dec_ref(v___x_4884_);
lean_dec_ref(v___f_4883_);
v___x_4892_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4892_;
}
else
{
lean_object* v___f_4893_; uint8_t v___x_4894_; 
v___f_4893_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_4893_, 0, v___f_4883_);
lean_closure_set(v___f_4893_, 1, v_socket_4885_);
v___x_4894_ = lean_nat_dec_le(v___x_4889_, v___x_4889_);
if (v___x_4894_ == 0)
{
if (v___x_4891_ == 0)
{
lean_object* v___x_4895_; 
lean_dec_ref(v___f_4893_);
lean_dec_ref(v_data_4886_);
lean_dec_ref(v___x_4884_);
v___x_4895_ = ((lean_object*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_4895_;
}
else
{
size_t v___x_4896_; size_t v___x_4897_; lean_object* v___x_749__overap_4898_; lean_object* v___x_4899_; 
v___x_4896_ = ((size_t)0ULL);
v___x_4897_ = lean_usize_of_nat(v___x_4889_);
v___x_749__overap_4898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4884_, v___f_4893_, v_data_4886_, v___x_4896_, v___x_4897_, v___x_4890_);
v___x_4899_ = lean_apply_1(v___x_749__overap_4898_, lean_box(0));
return v___x_4899_;
}
}
else
{
size_t v___x_4900_; size_t v___x_4901_; lean_object* v___x_752__overap_4902_; lean_object* v___x_4903_; 
v___x_4900_ = ((size_t)0ULL);
v___x_4901_ = lean_usize_of_nat(v___x_4889_);
v___x_752__overap_4902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4884_, v___f_4893_, v_data_4886_, v___x_4900_, v___x_4901_, v___x_4890_);
v___x_4903_ = lean_apply_1(v___x_752__overap_4902_, lean_box(0));
return v___x_4903_;
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_4883_ = stack[0].m_obj;
lean_object* v___x_4884_ = stack[1].m_obj;
lean_object* v_socket_4885_ = stack[2].m_obj;
lean_object* v_data_4886_ = stack[3].m_obj;
lean_object* v_res_4904_;
v_res_4904_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(v___f_4883_, v___x_4884_, v_socket_4885_, v_data_4886_);
stack->m_obj
 = v_res_4904_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object* v___f_4905_, lean_object* v___x_4906_, lean_object* v_socket_4907_, lean_object* v_data_4908_, lean_object* v___y_4909_){
_start:
{
lean_object* v_res_4910_; 
v_res_4910_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4(v___f_4905_, v___x_4906_, v_socket_4907_, v_data_4908_);
return v_res_4910_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_4916_; 
v___x_4916_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_4916_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_4917_; lean_object* v___f_4918_; lean_object* v___f_4919_; 
v___x_4917_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_4918_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1));
v___f_4919_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_4919_, 0, v___f_4918_);
lean_closure_set(v___f_4919_, 1, v___x_4917_);
return v___f_4919_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5(void){
_start:
{
lean_object* v___f_4920_; lean_object* v___f_4921_; lean_object* v___f_4922_; lean_object* v___x_4923_; 
v___f_4920_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_4921_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__4);
v___f_4922_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__1));
v___x_4923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4923_, 0, v___f_4922_);
lean_ctor_set(v___x_4923_, 1, v___f_4921_);
lean_ctor_set(v___x_4923_, 2, v___f_4920_);
return v___x_4923_;
}
}
lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_4925_; 
v___x_4925_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__5);
return v___x_4925_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4926_;
v_res_4926_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
stack->m_obj
 = v_res_4926_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_4927_){
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
return v_res_4928_;
}
}
static lean_object* _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg();
return v___x_4929_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_4930_, lean_object* v_inst_4931_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_4933_, lean_object* v_inst_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_4933_, v_inst_4934_);
lean_dec(v_inst_4934_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg(lean_object* v_ch_4936_){
_start:
{
lean_inc_ref(v_ch_4936_);
return v_ch_4936_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___redArg___boxed(lean_object* v_ch_4937_){
_start:
{
lean_object* v_res_4938_; 
v_res_4938_ = l_Std_CloseableChannel_sync___redArg(v_ch_4937_);
lean_dec_ref(v_ch_4937_);
return v_res_4938_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync(lean_object* v_00_u03b1_4939_, lean_object* v_ch_4940_){
_start:
{
lean_inc_ref(v_ch_4940_);
return v_ch_4940_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_sync___boxed(lean_object* v_00_u03b1_4941_, lean_object* v_ch_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Std_CloseableChannel_sync(v_00_u03b1_4941_, v_ch_4942_);
lean_dec_ref(v_ch_4942_);
return v_res_4943_;
}
}
lean_object* l_Std_CloseableChannel_Sync_new___redArg(lean_object* v_capacity_4944_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l_Std_CloseableChannel_new___redArg(v_capacity_4944_);
return v___x_4946_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_4944_ = stack[0].m_obj;
lean_object* v_res_4947_;
v_res_4947_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4944_);
stack->m_obj
 = v_res_4947_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___redArg___boxed(lean_object* v_capacity_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v_res_4950_; 
v_res_4950_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_4948_);
return v_res_4950_;
}
}
lean_object* l_Std_CloseableChannel_Sync_new(lean_object* v_00_u03b1_4951_, lean_object* v_capacity_4952_){
_start:
{
lean_object* v___x_4954_; 
v___x_4954_ = l_Std_CloseableChannel_new___redArg(v_capacity_4952_);
return v___x_4954_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_4952_ = stack[1].m_obj;
lean_object* v_res_4955_;
v_res_4955_ = l_Std_CloseableChannel_Sync_new(lean_box(0), v_capacity_4952_);
stack->m_obj
 = v_res_4955_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_new___boxed(lean_object* v_00_u03b1_4956_, lean_object* v_capacity_4957_, lean_object* v_a_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_4956_, v_capacity_4957_);
return v_res_4959_;
}
}
uint8_t l_Std_CloseableChannel_Sync_trySend___redArg(lean_object* v_ch_4960_, lean_object* v_v_4961_){
_start:
{
uint8_t v___x_4963_; 
v___x_4963_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4960_, v_v_4961_);
return v___x_4963_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4960_ = stack[0].m_obj;
lean_object* v_v_4961_ = stack[1].m_obj;
uint8_t v_res_4964_;
v_res_4964_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4960_, v_v_4961_);
stack->m_num = v_res_4964_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___redArg___boxed(lean_object* v_ch_4965_, lean_object* v_v_4966_, lean_object* v_a_4967_){
_start:
{
uint8_t v_res_4968_; lean_object* v_r_4969_; 
v_res_4968_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_4965_, v_v_4966_);
v_r_4969_ = lean_box(v_res_4968_);
return v_r_4969_;
}
}
uint8_t l_Std_CloseableChannel_Sync_trySend(lean_object* v_00_u03b1_4970_, lean_object* v_ch_4971_, lean_object* v_v_4972_){
_start:
{
uint8_t v___x_4974_; 
v___x_4974_ = l_Std_CloseableChannel_trySend___redArg(v_ch_4971_, v_v_4972_);
return v___x_4974_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4971_ = stack[1].m_obj;
lean_object* v_v_4972_ = stack[2].m_obj;
uint8_t v_res_4975_;
v_res_4975_ = l_Std_CloseableChannel_Sync_trySend(lean_box(0), v_ch_4971_, v_v_4972_);
stack->m_num = v_res_4975_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_trySend___boxed(lean_object* v_00_u03b1_4976_, lean_object* v_ch_4977_, lean_object* v_v_4978_, lean_object* v_a_4979_){
_start:
{
uint8_t v_res_4980_; lean_object* v_r_4981_; 
v_res_4980_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_4976_, v_ch_4977_, v_v_4978_);
v_r_4981_ = lean_box(v_res_4980_);
return v_r_4981_;
}
}
lean_object* l_Std_CloseableChannel_Sync_send___redArg(lean_object* v_ch_4982_, lean_object* v_v_4983_){
_start:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4985_ = l_Std_CloseableChannel_send___redArg(v_ch_4982_, v_v_4983_);
v___x_4986_ = lean_io_wait(v___x_4985_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4986_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4986_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
lean_ctor_set_tag(v___x_4989_, 1);
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
else
{
lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5002_; 
v_a_4995_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4997_ = v___x_4986_;
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4986_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_5000_; 
if (v_isShared_4998_ == 0)
{
lean_ctor_set_tag(v___x_4997_, 0);
v___x_5000_ = v___x_4997_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4982_ = stack[0].m_obj;
lean_object* v_v_4983_ = stack[1].m_obj;
lean_object* v_res_5003_;
v_res_5003_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_4982_, v_v_4983_);
stack->m_obj
 = v_res_5003_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___redArg___boxed(lean_object* v_ch_5004_, lean_object* v_v_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_5004_, v_v_5005_);
return v_res_5007_;
}
}
lean_object* l_Std_CloseableChannel_Sync_send(lean_object* v_00_u03b1_5008_, lean_object* v_ch_5009_, lean_object* v_v_5010_){
_start:
{
lean_object* v___x_5012_; 
v___x_5012_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_5009_, v_v_5010_);
return v___x_5012_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5009_ = stack[1].m_obj;
lean_object* v_v_5010_ = stack[2].m_obj;
lean_object* v_res_5013_;
v_res_5013_ = l_Std_CloseableChannel_Sync_send(lean_box(0), v_ch_5009_, v_v_5010_);
stack->m_obj
 = v_res_5013_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_send___boxed(lean_object* v_00_u03b1_5014_, lean_object* v_ch_5015_, lean_object* v_v_5016_, lean_object* v_a_5017_){
_start:
{
lean_object* v_res_5018_; 
v_res_5018_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_5014_, v_ch_5015_, v_v_5016_);
return v_res_5018_;
}
}
lean_object* l_Std_CloseableChannel_Sync_close___redArg(lean_object* v_ch_5019_){
_start:
{
lean_object* v___x_5021_; 
v___x_5021_ = l_Std_CloseableChannel_close___redArg(v_ch_5019_);
return v___x_5021_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5019_ = stack[0].m_obj;
lean_object* v_res_5022_;
v_res_5022_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_5019_);
stack->m_obj
 = v_res_5022_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___redArg___boxed(lean_object* v_ch_5023_, lean_object* v_a_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_5023_);
return v_res_5025_;
}
}
lean_object* l_Std_CloseableChannel_Sync_close(lean_object* v_00_u03b1_5026_, lean_object* v_ch_5027_){
_start:
{
lean_object* v___x_5029_; 
v___x_5029_ = l_Std_CloseableChannel_close___redArg(v_ch_5027_);
return v___x_5029_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5027_ = stack[1].m_obj;
lean_object* v_res_5030_;
v_res_5030_ = l_Std_CloseableChannel_Sync_close(lean_box(0), v_ch_5027_);
stack->m_obj
 = v_res_5030_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_close___boxed(lean_object* v_00_u03b1_5031_, lean_object* v_ch_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v_res_5034_; 
v_res_5034_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_5031_, v_ch_5032_);
return v_res_5034_;
}
}
uint8_t l_Std_CloseableChannel_Sync_isClosed___redArg(lean_object* v_ch_5035_){
_start:
{
uint8_t v___x_5037_; 
v___x_5037_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_5035_);
return v___x_5037_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5035_ = stack[0].m_obj;
uint8_t v_res_5038_;
v_res_5038_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_5035_);
stack->m_num = v_res_5038_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(lean_object* v_ch_5039_, lean_object* v_a_5040_){
_start:
{
uint8_t v_res_5041_; lean_object* v_r_5042_; 
v_res_5041_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_5039_);
v_r_5042_ = lean_box(v_res_5041_);
return v_r_5042_;
}
}
uint8_t l_Std_CloseableChannel_Sync_isClosed(lean_object* v_00_u03b1_5043_, lean_object* v_ch_5044_){
_start:
{
uint8_t v___x_5046_; 
v___x_5046_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_5044_);
return v___x_5046_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5044_ = stack[1].m_obj;
uint8_t v_res_5047_;
v_res_5047_ = l_Std_CloseableChannel_Sync_isClosed(lean_box(0), v_ch_5044_);
stack->m_num = v_res_5047_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_isClosed___boxed(lean_object* v_00_u03b1_5048_, lean_object* v_ch_5049_, lean_object* v_a_5050_){
_start:
{
uint8_t v_res_5051_; lean_object* v_r_5052_; 
v_res_5051_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_5048_, v_ch_5049_);
v_r_5052_ = lean_box(v_res_5051_);
return v_r_5052_;
}
}
lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg(lean_object* v_ch_5053_){
_start:
{
lean_object* v___x_5055_; 
v___x_5055_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5053_);
return v___x_5055_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5053_ = stack[0].m_obj;
lean_object* v_res_5056_;
v_res_5056_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_5053_);
stack->m_obj
 = v_res_5056_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5057_, lean_object* v_a_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_5057_);
return v_res_5059_;
}
}
lean_object* l_Std_CloseableChannel_Sync_tryRecv(lean_object* v_00_u03b1_5060_, lean_object* v_ch_5061_){
_start:
{
lean_object* v___x_5063_; 
v___x_5063_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5061_);
return v___x_5063_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5061_ = stack[1].m_obj;
lean_object* v_res_5064_;
v_res_5064_ = l_Std_CloseableChannel_Sync_tryRecv(lean_box(0), v_ch_5061_);
stack->m_obj
 = v_res_5064_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5065_, lean_object* v_ch_5066_, lean_object* v_a_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_5065_, v_ch_5066_);
return v_res_5068_;
}
}
lean_object* l_Std_CloseableChannel_Sync_recv___redArg(lean_object* v_ch_5069_){
_start:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; 
v___x_5071_ = l_Std_CloseableChannel_recv___redArg(v_ch_5069_);
v___x_5072_ = lean_io_wait(v___x_5071_);
return v___x_5072_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5069_ = stack[0].m_obj;
lean_object* v_res_5073_;
v_res_5073_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_5069_);
stack->m_obj
 = v_res_5073_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___redArg___boxed(lean_object* v_ch_5074_, lean_object* v_a_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_5074_);
return v_res_5076_;
}
}
lean_object* l_Std_CloseableChannel_Sync_recv(lean_object* v_00_u03b1_5077_, lean_object* v_ch_5078_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_5078_);
return v___x_5080_;
}
}
LEAN_EXPORT void l_Std_CloseableChannel_Sync_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5078_ = stack[1].m_obj;
lean_object* v_res_5081_;
v_res_5081_ = l_Std_CloseableChannel_Sync_recv(lean_box(0), v_ch_5078_);
stack->m_obj
 = v_res_5081_;
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_recv___boxed(lean_object* v_00_u03b1_5082_, lean_object* v_ch_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_5082_, v_ch_5083_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(lean_object* v_toPure_5086_, lean_object* v_b_5087_, lean_object* v_f_5088_, lean_object* v_toBind_5089_, lean_object* v___f_5090_, lean_object* v_____do__lift_5091_){
_start:
{
if (lean_obj_tag(v_____do__lift_5091_) == 0)
{
lean_object* v___x_5092_; 
lean_dec(v___f_5090_);
lean_dec(v_toBind_5089_);
lean_dec(v_f_5088_);
v___x_5092_ = lean_apply_2(v_toPure_5086_, lean_box(0), v_b_5087_);
return v___x_5092_;
}
else
{
lean_object* v_val_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
lean_dec(v_toPure_5086_);
v_val_5093_ = lean_ctor_get(v_____do__lift_5091_, 0);
lean_inc(v_val_5093_);
lean_dec_ref_known(v_____do__lift_5091_, 1);
v___x_5094_ = lean_apply_2(v_f_5088_, v_val_5093_, v_b_5087_);
v___x_5095_ = lean_apply_4(v_toBind_5089_, lean_box(0), lean_box(0), v___x_5094_, v___f_5090_);
return v___x_5095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(lean_object* v_inst_5096_, lean_object* v_inst_5097_, lean_object* v_ch_5098_, lean_object* v_f_5099_, lean_object* v_b_5100_){
_start:
{
lean_object* v_toApplicative_5101_; lean_object* v_toBind_5102_; lean_object* v_toPure_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___f_5106_; lean_object* v___f_5107_; lean_object* v___x_5108_; 
v_toApplicative_5101_ = lean_ctor_get(v_inst_5096_, 0);
v_toBind_5102_ = lean_ctor_get(v_inst_5096_, 1);
lean_inc_n(v_toBind_5102_, 2);
v_toPure_5103_ = lean_ctor_get(v_toApplicative_5101_, 1);
lean_inc_n(v_toPure_5103_, 2);
lean_inc_ref(v_ch_5098_);
v___x_5104_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_recv___boxed), 3, 2);
lean_closure_set(v___x_5104_, 0, lean_box(0));
lean_closure_set(v___x_5104_, 1, v_ch_5098_);
lean_inc(v_inst_5097_);
v___x_5105_ = lean_apply_2(v_inst_5097_, lean_box(0), v___x_5104_);
lean_inc(v_f_5099_);
v___f_5106_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_5106_, 0, v_toPure_5103_);
lean_closure_set(v___f_5106_, 1, v_inst_5096_);
lean_closure_set(v___f_5106_, 2, v_inst_5097_);
lean_closure_set(v___f_5106_, 3, v_ch_5098_);
lean_closure_set(v___f_5106_, 4, v_f_5099_);
v___f_5107_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5107_, 0, v_toPure_5103_);
lean_closure_set(v___f_5107_, 1, v_b_5100_);
lean_closure_set(v___f_5107_, 2, v_f_5099_);
lean_closure_set(v___f_5107_, 3, v_toBind_5102_);
lean_closure_set(v___f_5107_, 4, v___f_5106_);
v___x_5108_ = lean_apply_4(v_toBind_5102_, lean_box(0), lean_box(0), v___x_5105_, v___f_5107_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5109_, lean_object* v_inst_5110_, lean_object* v_inst_5111_, lean_object* v_ch_5112_, lean_object* v_f_5113_, lean_object* v_____do__lift_5114_){
_start:
{
if (lean_obj_tag(v_____do__lift_5114_) == 0)
{
lean_object* v_a_5115_; lean_object* v___x_5116_; 
lean_dec(v_f_5113_);
lean_dec_ref(v_ch_5112_);
lean_dec(v_inst_5111_);
lean_dec_ref(v_inst_5110_);
v_a_5115_ = lean_ctor_get(v_____do__lift_5114_, 0);
lean_inc(v_a_5115_);
lean_dec_ref_known(v_____do__lift_5114_, 1);
v___x_5116_ = lean_apply_2(v_toPure_5109_, lean_box(0), v_a_5115_);
return v___x_5116_;
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5118_; 
lean_dec(v_toPure_5109_);
v_a_5117_ = lean_ctor_get(v_____do__lift_5114_, 0);
lean_inc(v_a_5117_);
lean_dec_ref_known(v_____do__lift_5114_, 1);
v___x_5118_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_5110_, v_inst_5111_, v_ch_5112_, v_f_5113_, v_a_5117_);
return v___x_5118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(lean_object* v_m_5119_, lean_object* v_00_u03b1_5120_, lean_object* v_00_u03b2_5121_, lean_object* v_inst_5122_, lean_object* v_inst_5123_, lean_object* v_ch_5124_, lean_object* v_f_5125_, lean_object* v_b_5126_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_5122_, v_inst_5123_, v_ch_5124_, v_f_5125_, v_b_5126_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5128_, lean_object* v_inst_5129_, lean_object* v_ch_5130_, lean_object* v_b_5131_, lean_object* v_f_5132_){
_start:
{
lean_object* v___x_5133_; 
v___x_5133_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_5128_, v_inst_5129_, v_ch_5130_, v_f_5132_, v_b_5131_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_m_5134_, lean_object* v_00_u03b1_5135_, lean_object* v_inst_5136_, lean_object* v_inst_5137_, lean_object* v_00_u03b2_5138_, lean_object* v_ch_5139_, lean_object* v_b_5140_, lean_object* v_f_5141_){
_start:
{
lean_object* v___x_5142_; 
v___x_5142_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_5136_, v_inst_5137_, v_ch_5139_, v_f_5141_, v_b_5140_);
return v___x_5142_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5143_, lean_object* v_inst_5144_, lean_object* v_00_u03b2_5145_, lean_object* v_ch_5146_, lean_object* v_b_5147_, lean_object* v_f_5148_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(v_inst_5143_, v_inst_5144_, v_ch_5146_, v_f_5148_, v_b_5147_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5150_, lean_object* v_inst_5151_){
_start:
{
lean_object* v___f_5152_; 
v___f_5152_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_5152_, 0, v_inst_5150_);
lean_closure_set(v___f_5152_, 1, v_inst_5151_);
return v___f_5152_;
}
}
LEAN_EXPORT lean_object* l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(lean_object* v_m_5153_, lean_object* v_00_u03b1_5154_, lean_object* v_inst_5155_, lean_object* v_inst_5156_){
_start:
{
lean_object* v___f_5157_; 
v___f_5157_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 6, 2);
lean_closure_set(v___f_5157_, 0, v_inst_5155_);
lean_closure_set(v___f_5157_, 1, v_inst_5156_);
return v___f_5157_;
}
}
lean_object* l_Std_Channel_new___redArg(lean_object* v_capacity_5158_){
_start:
{
lean_object* v___x_5160_; 
v___x_5160_ = l_Std_CloseableChannel_new___redArg(v_capacity_5158_);
return v___x_5160_;
}
}
LEAN_EXPORT void l_Std_Channel_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_5158_ = stack[0].m_obj;
lean_object* v_res_5161_;
v_res_5161_ = l_Std_Channel_new___redArg(v_capacity_5158_);
stack->m_obj
 = v_res_5161_;
}
LEAN_EXPORT lean_object* l_Std_Channel_new___redArg___boxed(lean_object* v_capacity_5162_, lean_object* v_a_5163_){
_start:
{
lean_object* v_res_5164_; 
v_res_5164_ = l_Std_Channel_new___redArg(v_capacity_5162_);
return v_res_5164_;
}
}
lean_object* l_Std_Channel_new(lean_object* v_00_u03b1_5165_, lean_object* v_capacity_5166_){
_start:
{
lean_object* v___x_5168_; 
v___x_5168_ = l_Std_CloseableChannel_new___redArg(v_capacity_5166_);
return v___x_5168_;
}
}
LEAN_EXPORT void l_Std_Channel_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_5166_ = stack[1].m_obj;
lean_object* v_res_5169_;
v_res_5169_ = l_Std_Channel_new(lean_box(0), v_capacity_5166_);
stack->m_obj
 = v_res_5169_;
}
LEAN_EXPORT lean_object* l_Std_Channel_new___boxed(lean_object* v_00_u03b1_5170_, lean_object* v_capacity_5171_, lean_object* v_a_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Std_Channel_new(v_00_u03b1_5170_, v_capacity_5171_);
return v_res_5173_;
}
}
uint8_t l_Std_Channel_trySend___redArg(lean_object* v_ch_5174_, lean_object* v_v_5175_){
_start:
{
uint8_t v___x_5177_; 
v___x_5177_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5174_, v_v_5175_);
return v___x_5177_;
}
}
LEAN_EXPORT void l_Std_Channel_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5174_ = stack[0].m_obj;
lean_object* v_v_5175_ = stack[1].m_obj;
uint8_t v_res_5178_;
v_res_5178_ = l_Std_Channel_trySend___redArg(v_ch_5174_, v_v_5175_);
stack->m_num = v_res_5178_;
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___redArg___boxed(lean_object* v_ch_5179_, lean_object* v_v_5180_, lean_object* v_a_5181_){
_start:
{
uint8_t v_res_5182_; lean_object* v_r_5183_; 
v_res_5182_ = l_Std_Channel_trySend___redArg(v_ch_5179_, v_v_5180_);
v_r_5183_ = lean_box(v_res_5182_);
return v_r_5183_;
}
}
uint8_t l_Std_Channel_trySend(lean_object* v_00_u03b1_5184_, lean_object* v_ch_5185_, lean_object* v_v_5186_){
_start:
{
uint8_t v___x_5188_; 
v___x_5188_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5185_, v_v_5186_);
return v___x_5188_;
}
}
LEAN_EXPORT void l_Std_Channel_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5185_ = stack[1].m_obj;
lean_object* v_v_5186_ = stack[2].m_obj;
uint8_t v_res_5189_;
v_res_5189_ = l_Std_Channel_trySend(lean_box(0), v_ch_5185_, v_v_5186_);
stack->m_num = v_res_5189_;
}
LEAN_EXPORT lean_object* l_Std_Channel_trySend___boxed(lean_object* v_00_u03b1_5190_, lean_object* v_ch_5191_, lean_object* v_v_5192_, lean_object* v_a_5193_){
_start:
{
uint8_t v_res_5194_; lean_object* v_r_5195_; 
v_res_5194_ = l_Std_Channel_trySend(v_00_u03b1_5190_, v_ch_5191_, v_v_5192_);
v_r_5195_ = lean_box(v_res_5194_);
return v_r_5195_;
}
}
static lean_object* _init_l_panic___at___00Std_Channel_send_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___x_5196_ = lean_box(0);
v___x_5197_ = lean_task_pure(v___x_5196_);
return v___x_5197_;
}
}
lean_object* l_panic___at___00Std_Channel_send_spec__0(lean_object* v_msg_5198_){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_142__overap_5203_; lean_object* v___x_5204_; 
v___x_5200_ = l_instMonadBaseIO;
v___x_5201_ = lean_obj_once(&l_panic___at___00Std_Channel_send_spec__0___closed__0, &l_panic___at___00Std_Channel_send_spec__0___closed__0_once, _init_l_panic___at___00Std_Channel_send_spec__0___closed__0);
v___x_5202_ = l_instInhabitedOfMonad___redArg(v___x_5200_, v___x_5201_);
v___x_142__overap_5203_ = lean_panic_fn_borrowed(v___x_5202_, v_msg_5198_);
lean_dec(v___x_5202_);
v___x_5204_ = lean_apply_1(v___x_142__overap_5203_, lean_box(0));
return v___x_5204_;
}
}
LEAN_EXPORT void l_panic___at___00Std_Channel_send_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5198_ = stack[0].m_obj;
lean_object* v_res_5205_;
v_res_5205_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_5198_);
stack->m_obj
 = v_res_5205_;
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Channel_send_spec__0___boxed(lean_object* v_msg_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_5206_);
return v_res_5208_;
}
}
static lean_object* _init_l_Std_Channel_send___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5212_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_5213_ = lean_unsigned_to_nat(21u);
v___x_5214_ = lean_unsigned_to_nat(872u);
v___x_5215_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__1));
v___x_5216_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_5217_ = l_mkPanicMessageWithDecl(v___x_5216_, v___x_5215_, v___x_5214_, v___x_5213_, v___x_5212_);
return v___x_5217_;
}
}
lean_object* l_Std_Channel_send___redArg___lam__0(lean_object* v_x_5218_){
_start:
{
if (lean_obj_tag(v_x_5218_) == 0)
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
v___x_5220_ = lean_obj_once(&l_Std_Channel_send___redArg___lam__0___closed__3, &l_Std_Channel_send___redArg___lam__0___closed__3_once, _init_l_Std_Channel_send___redArg___lam__0___closed__3);
v___x_5221_ = l_panic___at___00Std_Channel_send_spec__0(v___x_5220_);
return v___x_5221_;
}
else
{
lean_object* v___x_5222_; 
v___x_5222_ = lean_obj_once(&l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0, &l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once, _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0);
return v___x_5222_;
}
}
}
LEAN_EXPORT void l_Std_Channel_send___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5218_ = stack[0].m_obj;
lean_object* v_res_5223_;
v_res_5223_ = l_Std_Channel_send___redArg___lam__0(v_x_5218_);
stack->m_obj
 = v_res_5223_;
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___lam__0___boxed(lean_object* v_x_5224_, lean_object* v___y_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Std_Channel_send___redArg___lam__0(v_x_5224_);
lean_dec_ref(v_x_5224_);
return v_res_5226_;
}
}
lean_object* l_Std_Channel_send___redArg(lean_object* v_ch_5228_, lean_object* v_v_5229_){
_start:
{
lean_object* v___f_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; uint8_t v___x_5234_; lean_object* v___x_5235_; 
v___f_5231_ = ((lean_object*)(l_Std_Channel_send___redArg___closed__0));
v___x_5232_ = l_Std_CloseableChannel_send___redArg(v_ch_5228_, v_v_5229_);
v___x_5233_ = lean_unsigned_to_nat(0u);
v___x_5234_ = 1;
v___x_5235_ = lean_io_bind_task(v___x_5232_, v___f_5231_, v___x_5233_, v___x_5234_);
return v___x_5235_;
}
}
LEAN_EXPORT void l_Std_Channel_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5228_ = stack[0].m_obj;
lean_object* v_v_5229_ = stack[1].m_obj;
lean_object* v_res_5236_;
v_res_5236_ = l_Std_Channel_send___redArg(v_ch_5228_, v_v_5229_);
stack->m_obj
 = v_res_5236_;
}
LEAN_EXPORT lean_object* l_Std_Channel_send___redArg___boxed(lean_object* v_ch_5237_, lean_object* v_v_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Std_Channel_send___redArg(v_ch_5237_, v_v_5238_);
return v_res_5240_;
}
}
lean_object* l_Std_Channel_send(lean_object* v_00_u03b1_5241_, lean_object* v_ch_5242_, lean_object* v_v_5243_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Std_Channel_send___redArg(v_ch_5242_, v_v_5243_);
return v___x_5245_;
}
}
LEAN_EXPORT void l_Std_Channel_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5242_ = stack[1].m_obj;
lean_object* v_v_5243_ = stack[2].m_obj;
lean_object* v_res_5246_;
v_res_5246_ = l_Std_Channel_send(lean_box(0), v_ch_5242_, v_v_5243_);
stack->m_obj
 = v_res_5246_;
}
LEAN_EXPORT lean_object* l_Std_Channel_send___boxed(lean_object* v_00_u03b1_5247_, lean_object* v_ch_5248_, lean_object* v_v_5249_, lean_object* v_a_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Std_Channel_send(v_00_u03b1_5247_, v_ch_5248_, v_v_5249_);
return v_res_5251_;
}
}
lean_object* l_Std_Channel_tryRecv___redArg(lean_object* v_ch_5252_){
_start:
{
lean_object* v___x_5254_; 
v___x_5254_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5252_);
return v___x_5254_;
}
}
LEAN_EXPORT void l_Std_Channel_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5252_ = stack[0].m_obj;
lean_object* v_res_5255_;
v_res_5255_ = l_Std_Channel_tryRecv___redArg(v_ch_5252_);
stack->m_obj
 = v_res_5255_;
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___redArg___boxed(lean_object* v_ch_5256_, lean_object* v_a_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Std_Channel_tryRecv___redArg(v_ch_5256_);
return v_res_5258_;
}
}
lean_object* l_Std_Channel_tryRecv(lean_object* v_00_u03b1_5259_, lean_object* v_ch_5260_){
_start:
{
lean_object* v___x_5262_; 
v___x_5262_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5260_);
return v___x_5262_;
}
}
LEAN_EXPORT void l_Std_Channel_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5260_ = stack[1].m_obj;
lean_object* v_res_5263_;
v_res_5263_ = l_Std_Channel_tryRecv(lean_box(0), v_ch_5260_);
stack->m_obj
 = v_res_5263_;
}
LEAN_EXPORT lean_object* l_Std_Channel_tryRecv___boxed(lean_object* v_00_u03b1_5264_, lean_object* v_ch_5265_, lean_object* v_a_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Std_Channel_tryRecv(v_00_u03b1_5264_, v_ch_5265_);
return v_res_5267_;
}
}
static lean_object* _init_l_Std_Channel_recv___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; 
v___x_5269_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__2));
v___x_5270_ = lean_unsigned_to_nat(16u);
v___x_5271_ = lean_unsigned_to_nat(883u);
v___x_5272_ = ((lean_object*)(l_Std_Channel_recv___redArg___lam__0___closed__0));
v___x_5273_ = ((lean_object*)(l_Std_Channel_send___redArg___lam__0___closed__0));
v___x_5274_ = l_mkPanicMessageWithDecl(v___x_5273_, v___x_5272_, v___x_5271_, v___x_5270_, v___x_5269_);
return v___x_5274_;
}
}
lean_object* l_Std_Channel_recv___redArg___lam__0(lean_object* v___x_5275_, lean_object* v_x_5276_){
_start:
{
if (lean_obj_tag(v_x_5276_) == 0)
{
lean_object* v___x_5278_; lean_object* v___x_144__overap_5279_; lean_object* v___x_5280_; 
v___x_5278_ = lean_obj_once(&l_Std_Channel_recv___redArg___lam__0___closed__1, &l_Std_Channel_recv___redArg___lam__0___closed__1_once, _init_l_Std_Channel_recv___redArg___lam__0___closed__1);
v___x_144__overap_5279_ = l_panic___redArg(v___x_5275_, v___x_5278_);
v___x_5280_ = lean_apply_1(v___x_144__overap_5279_, lean_box(0));
return v___x_5280_;
}
else
{
lean_object* v_val_5281_; lean_object* v___x_5282_; 
v_val_5281_ = lean_ctor_get(v_x_5276_, 0);
lean_inc(v_val_5281_);
lean_dec_ref_known(v_x_5276_, 1);
v___x_5282_ = lean_task_pure(v_val_5281_);
return v___x_5282_;
}
}
}
LEAN_EXPORT void l_Std_Channel_recv___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5275_ = stack[0].m_obj;
lean_object* v_x_5276_ = stack[1].m_obj;
lean_object* v_res_5283_;
v_res_5283_ = l_Std_Channel_recv___redArg___lam__0(v___x_5275_, v_x_5276_);
stack->m_obj
 = v_res_5283_;
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___lam__0___boxed(lean_object* v___x_5284_, lean_object* v_x_5285_, lean_object* v___y_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Std_Channel_recv___redArg___lam__0(v___x_5284_, v_x_5285_);
lean_dec(v___x_5284_);
return v_res_5287_;
}
}
lean_object* l_Std_Channel_recv___redArg(lean_object* v_inst_5288_, lean_object* v_ch_5289_){
_start:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___f_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; uint8_t v___x_5297_; lean_object* v___x_5298_; 
v___x_5291_ = l_instMonadBaseIO;
v___x_5292_ = lean_task_pure(v_inst_5288_);
v___x_5293_ = l_instInhabitedOfMonad___redArg(v___x_5291_, v___x_5292_);
v___f_5294_ = lean_alloc_closure((void*)(l_Std_Channel_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5294_, 0, v___x_5293_);
v___x_5295_ = l_Std_CloseableChannel_recv___redArg(v_ch_5289_);
v___x_5296_ = lean_unsigned_to_nat(0u);
v___x_5297_ = 1;
v___x_5298_ = lean_io_bind_task(v___x_5295_, v___f_5294_, v___x_5296_, v___x_5297_);
return v___x_5298_;
}
}
LEAN_EXPORT void l_Std_Channel_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5288_ = stack[0].m_obj;
lean_object* v_ch_5289_ = stack[1].m_obj;
lean_object* v_res_5299_;
v_res_5299_ = l_Std_Channel_recv___redArg(v_inst_5288_, v_ch_5289_);
stack->m_obj
 = v_res_5299_;
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___redArg___boxed(lean_object* v_inst_5300_, lean_object* v_ch_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Std_Channel_recv___redArg(v_inst_5300_, v_ch_5301_);
return v_res_5303_;
}
}
lean_object* l_Std_Channel_recv(lean_object* v_00_u03b1_5304_, lean_object* v_inst_5305_, lean_object* v_ch_5306_){
_start:
{
lean_object* v___x_5308_; 
v___x_5308_ = l_Std_Channel_recv___redArg(v_inst_5305_, v_ch_5306_);
return v___x_5308_;
}
}
LEAN_EXPORT void l_Std_Channel_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5305_ = stack[1].m_obj;
lean_object* v_ch_5306_ = stack[2].m_obj;
lean_object* v_res_5309_;
v_res_5309_ = l_Std_Channel_recv(lean_box(0), v_inst_5305_, v_ch_5306_);
stack->m_obj
 = v_res_5309_;
}
LEAN_EXPORT lean_object* l_Std_Channel_recv___boxed(lean_object* v_00_u03b1_5310_, lean_object* v_inst_5311_, lean_object* v_ch_5312_, lean_object* v_a_5313_){
_start:
{
lean_object* v_res_5314_; 
v_res_5314_ = l_Std_Channel_recv(v_00_u03b1_5310_, v_inst_5311_, v_ch_5312_);
return v_res_5314_;
}
}
lean_object* l_Std_Channel_recvSelector___redArg___lam__0(lean_object* v_ch_5315_){
_start:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; 
v___x_5317_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5315_);
v___x_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5317_);
v___x_5319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5319_, 0, v___x_5318_);
return v___x_5319_;
}
}
LEAN_EXPORT void l_Std_Channel_recvSelector___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5315_ = stack[0].m_obj;
lean_object* v_res_5320_;
v_res_5320_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5315_);
stack->m_obj
 = v_res_5320_;
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__0___boxed(lean_object* v_ch_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v_res_5323_; 
v_res_5323_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_5321_);
return v_res_5323_;
}
}
static lean_object* _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; 
v___x_5327_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__2));
v___x_5328_ = lean_unsigned_to_nat(14u);
v___x_5329_ = lean_unsigned_to_nat(22u);
v___x_5330_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__1));
v___x_5331_ = ((lean_object*)(l_Std_Channel_recvSelector___redArg___lam__1___closed__0));
v___x_5332_ = l_mkPanicMessageWithDecl(v___x_5331_, v___x_5330_, v___x_5329_, v___x_5328_, v___x_5327_);
return v___x_5332_;
}
}
lean_object* l_Std_Channel_recvSelector___redArg___lam__1(lean_object* v_promise_5333_, lean_object* v_inst_5334_, lean_object* v_x_5335_){
_start:
{
lean_object* v___y_5338_; lean_object* v___y_5342_; 
if (lean_obj_tag(v_x_5335_) == 0)
{
lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5344_ = lean_box(0);
v___x_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5345_, 0, v___x_5344_);
return v___x_5345_;
}
else
{
lean_object* v_val_5346_; 
v_val_5346_ = lean_ctor_get(v_x_5335_, 0);
lean_inc(v_val_5346_);
lean_dec_ref_known(v_x_5335_, 1);
if (lean_obj_tag(v_val_5346_) == 0)
{
lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5354_; 
v_a_5347_ = lean_ctor_get(v_val_5346_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v_val_5346_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5349_ = v_val_5346_;
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_dec(v_val_5346_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5354_;
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
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
v___y_5338_ = v___x_5352_;
goto v___jp_5337_;
}
}
}
else
{
lean_object* v_a_5355_; 
v_a_5355_ = lean_ctor_get(v_val_5346_, 0);
lean_inc(v_a_5355_);
lean_dec_ref_known(v_val_5346_, 1);
if (lean_obj_tag(v_a_5355_) == 0)
{
lean_object* v___x_5356_; lean_object* v___x_5357_; 
v___x_5356_ = lean_obj_once(&l_Std_Channel_recvSelector___redArg___lam__1___closed__3, &l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once, _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3);
v___x_5357_ = l_panic___redArg(v_inst_5334_, v___x_5356_);
v___y_5342_ = v___x_5357_;
goto v___jp_5341_;
}
else
{
lean_object* v_val_5358_; 
v_val_5358_ = lean_ctor_get(v_a_5355_, 0);
lean_inc(v_val_5358_);
lean_dec_ref_known(v_a_5355_, 1);
v___y_5342_ = v_val_5358_;
goto v___jp_5341_;
}
}
}
v___jp_5337_:
{
lean_object* v___x_5339_; lean_object* v___x_5340_; 
v___x_5339_ = lean_io_promise_resolve(v___y_5338_, v_promise_5333_);
v___x_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5340_, 0, v___x_5339_);
return v___x_5340_;
}
v___jp_5341_:
{
lean_object* v___x_5343_; 
v___x_5343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5343_, 0, v___y_5342_);
v___y_5338_ = v___x_5343_;
goto v___jp_5337_;
}
}
}
LEAN_EXPORT void l_Std_Channel_recvSelector___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_5333_ = stack[0].m_obj;
lean_object* v_inst_5334_ = stack[1].m_obj;
lean_object* v_x_5335_ = stack[2].m_obj;
lean_object* v_res_5359_;
v_res_5359_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5333_, v_inst_5334_, v_x_5335_);
stack->m_obj
 = v_res_5359_;
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__1___boxed(lean_object* v_promise_5360_, lean_object* v_inst_5361_, lean_object* v_x_5362_, lean_object* v___y_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Std_Channel_recvSelector___redArg___lam__1(v_promise_5360_, v_inst_5361_, v_x_5362_);
lean_dec(v_inst_5361_);
lean_dec(v_promise_5360_);
return v_res_5364_;
}
}
lean_object* l_Std_Channel_recvSelector___redArg___lam__2(lean_object* v_a_5365_, lean_object* v___f_5366_, lean_object* v_x_5367_){
_start:
{
lean_object* v_val_5370_; 
if (lean_obj_tag(v_x_5367_) == 0)
{
lean_object* v___x_5372_; 
lean_dec_ref(v___f_5366_);
v___x_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5372_, 0, v_x_5367_);
return v___x_5372_;
}
else
{
lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5388_; 
v_isSharedCheck_5388_ = !lean_is_exclusive(v_x_5367_);
if (v_isSharedCheck_5388_ == 0)
{
lean_object* v_unused_5389_; 
v_unused_5389_ = lean_ctor_get(v_x_5367_, 0);
lean_dec(v_unused_5389_);
v___x_5374_ = v_x_5367_;
v_isShared_5375_ = v_isSharedCheck_5388_;
goto v_resetjp_5373_;
}
else
{
lean_dec(v_x_5367_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5388_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
lean_object* v___x_5376_; lean_object* v___x_5377_; uint8_t v___x_5378_; lean_object* v___x_5379_; 
v___x_5376_ = lean_io_promise_result_opt(v_a_5365_);
v___x_5377_ = lean_unsigned_to_nat(0u);
v___x_5378_ = 1;
v___x_5379_ = l_EIO_chainTask___redArg(v___x_5376_, v___f_5366_, v___x_5377_, v___x_5378_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v_a_5380_; lean_object* v___x_5382_; 
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
lean_inc(v_a_5380_);
lean_dec_ref_known(v___x_5379_, 1);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 0, v_a_5380_);
v___x_5382_ = v___x_5374_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5380_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
v_val_5370_ = v___x_5382_;
goto v___jp_5369_;
}
}
else
{
lean_object* v_a_5384_; lean_object* v___x_5386_; 
v_a_5384_ = lean_ctor_get(v___x_5379_, 0);
lean_inc(v_a_5384_);
lean_dec_ref_known(v___x_5379_, 1);
if (v_isShared_5375_ == 0)
{
lean_ctor_set_tag(v___x_5374_, 0);
lean_ctor_set(v___x_5374_, 0, v_a_5384_);
v___x_5386_ = v___x_5374_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5384_);
v___x_5386_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
v_val_5370_ = v___x_5386_;
goto v___jp_5369_;
}
}
}
}
v___jp_5369_:
{
lean_object* v___x_5371_; 
v___x_5371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5371_, 0, v_val_5370_);
return v___x_5371_;
}
}
}
LEAN_EXPORT void l_Std_Channel_recvSelector___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5365_ = stack[0].m_obj;
lean_object* v___f_5366_ = stack[1].m_obj;
lean_object* v_x_5367_ = stack[2].m_obj;
lean_object* v_res_5390_;
v_res_5390_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5365_, v___f_5366_, v_x_5367_);
stack->m_obj
 = v_res_5390_;
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__2___boxed(lean_object* v_a_5391_, lean_object* v___f_5392_, lean_object* v_x_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_Std_Channel_recvSelector___redArg___lam__2(v_a_5391_, v___f_5392_, v_x_5393_);
lean_dec(v_a_5391_);
return v_res_5395_;
}
}
lean_object* l_Std_Channel_recvSelector___redArg___lam__3(lean_object* v_sel_5396_, lean_object* v___f_5397_, lean_object* v_finished_5398_, lean_object* v_x_5399_){
_start:
{
if (lean_obj_tag(v_x_5399_) == 0)
{
lean_object* v_a_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5409_; 
lean_dec(v_finished_5398_);
lean_dec_ref(v___f_5397_);
lean_dec_ref(v_sel_5396_);
v_a_5401_ = lean_ctor_get(v_x_5399_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v_x_5399_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5403_ = v_x_5399_;
v_isShared_5404_ = v_isSharedCheck_5409_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_a_5401_);
lean_dec(v_x_5399_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5409_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
lean_object* v___x_5406_; 
if (v_isShared_5404_ == 0)
{
v___x_5406_ = v___x_5403_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5401_);
v___x_5406_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
lean_object* v___x_5407_; 
v___x_5407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5406_);
return v___x_5407_;
}
}
}
else
{
lean_object* v_a_5410_; lean_object* v_registerFn_5411_; lean_object* v___f_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; uint8_t v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
v_a_5410_ = lean_ctor_get(v_x_5399_, 0);
lean_inc_n(v_a_5410_, 2);
lean_dec_ref_known(v_x_5399_, 1);
v_registerFn_5411_ = lean_ctor_get(v_sel_5396_, 1);
lean_inc_ref(v_registerFn_5411_);
lean_dec_ref(v_sel_5396_);
v___f_5412_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5412_, 0, v_a_5410_);
lean_closure_set(v___f_5412_, 1, v___f_5397_);
v___x_5413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5413_, 0, v_finished_5398_);
lean_ctor_set(v___x_5413_, 1, v_a_5410_);
v___x_5414_ = lean_unsigned_to_nat(0u);
v___x_5415_ = 0;
v___x_5416_ = lean_apply_2(v_registerFn_5411_, v___x_5413_, lean_box(0));
v___x_5417_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5414_, v___x_5415_, v___x_5416_, v___f_5412_);
return v___x_5417_;
}
}
}
LEAN_EXPORT void l_Std_Channel_recvSelector___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_sel_5396_ = stack[0].m_obj;
lean_object* v___f_5397_ = stack[1].m_obj;
lean_object* v_finished_5398_ = stack[2].m_obj;
lean_object* v_x_5399_ = stack[3].m_obj;
lean_object* v_res_5418_;
v_res_5418_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5396_, v___f_5397_, v_finished_5398_, v_x_5399_);
stack->m_obj
 = v_res_5418_;
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__3___boxed(lean_object* v_sel_5419_, lean_object* v___f_5420_, lean_object* v_finished_5421_, lean_object* v_x_5422_, lean_object* v___y_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Std_Channel_recvSelector___redArg___lam__3(v_sel_5419_, v___f_5420_, v_finished_5421_, v_x_5422_);
return v_res_5424_;
}
}
lean_object* l_Std_Channel_recvSelector___redArg___lam__4(lean_object* v_inst_5425_, lean_object* v_sel_5426_, lean_object* v_waiter_5427_){
_start:
{
lean_object* v_finished_5429_; lean_object* v_promise_5430_; lean_object* v___f_5431_; lean_object* v___f_5432_; lean_object* v___x_5433_; uint8_t v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; 
v_finished_5429_ = lean_ctor_get(v_waiter_5427_, 0);
lean_inc(v_finished_5429_);
v_promise_5430_ = lean_ctor_get(v_waiter_5427_, 1);
lean_inc(v_promise_5430_);
lean_dec_ref(v_waiter_5427_);
v___f_5431_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_5431_, 0, v_promise_5430_);
lean_closure_set(v___f_5431_, 1, v_inst_5425_);
v___f_5432_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_5432_, 0, v_sel_5426_);
lean_closure_set(v___f_5432_, 1, v___f_5431_);
lean_closure_set(v___f_5432_, 2, v_finished_5429_);
v___x_5433_ = lean_unsigned_to_nat(0u);
v___x_5434_ = 0;
v___x_5435_ = lean_io_promise_new();
v___x_5436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5436_, 0, v___x_5435_);
v___x_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5436_);
v___x_5438_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5433_, v___x_5434_, v___x_5437_, v___f_5432_);
return v___x_5438_;
}
}
LEAN_EXPORT void l_Std_Channel_recvSelector___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5425_ = stack[0].m_obj;
lean_object* v_sel_5426_ = stack[1].m_obj;
lean_object* v_waiter_5427_ = stack[2].m_obj;
lean_object* v_res_5439_;
v_res_5439_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5425_, v_sel_5426_, v_waiter_5427_);
stack->m_obj
 = v_res_5439_;
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg___lam__4___boxed(lean_object* v_inst_5440_, lean_object* v_sel_5441_, lean_object* v_waiter_5442_, lean_object* v___y_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l_Std_Channel_recvSelector___redArg___lam__4(v_inst_5440_, v_sel_5441_, v_waiter_5442_);
return v_res_5444_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector___redArg(lean_object* v_inst_5445_, lean_object* v_ch_5446_){
_start:
{
lean_object* v_sel_5447_; lean_object* v_unregisterFn_5448_; lean_object* v___f_5449_; lean_object* v___f_5450_; lean_object* v___x_5451_; 
lean_inc_ref(v_ch_5446_);
v_sel_5447_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_5446_);
v_unregisterFn_5448_ = lean_ctor_get(v_sel_5447_, 2);
lean_inc_ref(v_unregisterFn_5448_);
v___f_5449_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5449_, 0, v_ch_5446_);
v___f_5450_ = lean_alloc_closure((void*)(l_Std_Channel_recvSelector___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_5450_, 0, v_inst_5445_);
lean_closure_set(v___f_5450_, 1, v_sel_5447_);
v___x_5451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5451_, 0, v___f_5449_);
lean_ctor_set(v___x_5451_, 1, v___f_5450_);
lean_ctor_set(v___x_5451_, 2, v_unregisterFn_5448_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_recvSelector(lean_object* v_00_u03b1_5452_, lean_object* v_inst_5453_, lean_object* v_ch_5454_){
_start:
{
lean_object* v___x_5455_; 
v___x_5455_ = l_Std_Channel_recvSelector___redArg(v_inst_5453_, v_ch_5454_);
return v___x_5455_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___lam__0___boxed(lean_object* v_f_5456_, lean_object* v_inst_5457_, lean_object* v_ch_5458_, lean_object* v_prio_5459_, lean_object* v_v_5460_, lean_object* v___y_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5456_, v_inst_5457_, v_ch_5458_, v_prio_5459_, v_v_5460_);
return v_res_5462_;
}
}
lean_object* l_Std_Channel_forAsync___redArg(lean_object* v_inst_5463_, lean_object* v_f_5464_, lean_object* v_ch_5465_, lean_object* v_prio_5466_){
_start:
{
lean_object* v___f_5468_; lean_object* v___x_5469_; uint8_t v___x_5470_; lean_object* v___x_5471_; 
lean_inc(v_prio_5466_);
lean_inc_ref(v_ch_5465_);
lean_inc(v_inst_5463_);
v___f_5468_ = lean_alloc_closure((void*)(l_Std_Channel_forAsync___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_5468_, 0, v_f_5464_);
lean_closure_set(v___f_5468_, 1, v_inst_5463_);
lean_closure_set(v___f_5468_, 2, v_ch_5465_);
lean_closure_set(v___f_5468_, 3, v_prio_5466_);
v___x_5469_ = l_Std_Channel_recv___redArg(v_inst_5463_, v_ch_5465_);
v___x_5470_ = 0;
v___x_5471_ = lean_io_bind_task(v___x_5469_, v___f_5468_, v_prio_5466_, v___x_5470_);
return v___x_5471_;
}
}
LEAN_EXPORT void l_Std_Channel_forAsync___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5463_ = stack[0].m_obj;
lean_object* v_f_5464_ = stack[1].m_obj;
lean_object* v_ch_5465_ = stack[2].m_obj;
lean_object* v_prio_5466_ = stack[3].m_obj;
lean_object* v_res_5472_;
v_res_5472_ = l_Std_Channel_forAsync___redArg(v_inst_5463_, v_f_5464_, v_ch_5465_, v_prio_5466_);
stack->m_obj
 = v_res_5472_;
}
lean_object* l_Std_Channel_forAsync___redArg___lam__0(lean_object* v_f_5473_, lean_object* v_inst_5474_, lean_object* v_ch_5475_, lean_object* v_prio_5476_, lean_object* v_v_5477_){
_start:
{
lean_object* v___x_5479_; lean_object* v___x_5480_; 
lean_inc_ref(v_f_5473_);
v___x_5479_ = lean_apply_2(v_f_5473_, v_v_5477_, lean_box(0));
v___x_5480_ = l_Std_Channel_forAsync___redArg(v_inst_5474_, v_f_5473_, v_ch_5475_, v_prio_5476_);
return v___x_5480_;
}
}
LEAN_EXPORT void l_Std_Channel_forAsync___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_5473_ = stack[0].m_obj;
lean_object* v_inst_5474_ = stack[1].m_obj;
lean_object* v_ch_5475_ = stack[2].m_obj;
lean_object* v_prio_5476_ = stack[3].m_obj;
lean_object* v_v_5477_ = stack[4].m_obj;
lean_object* v_res_5481_;
v_res_5481_ = l_Std_Channel_forAsync___redArg___lam__0(v_f_5473_, v_inst_5474_, v_ch_5475_, v_prio_5476_, v_v_5477_);
stack->m_obj
 = v_res_5481_;
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___redArg___boxed(lean_object* v_inst_5482_, lean_object* v_f_5483_, lean_object* v_ch_5484_, lean_object* v_prio_5485_, lean_object* v_a_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l_Std_Channel_forAsync___redArg(v_inst_5482_, v_f_5483_, v_ch_5484_, v_prio_5485_);
return v_res_5487_;
}
}
lean_object* l_Std_Channel_forAsync(lean_object* v_00_u03b1_5488_, lean_object* v_inst_5489_, lean_object* v_f_5490_, lean_object* v_ch_5491_, lean_object* v_prio_5492_){
_start:
{
lean_object* v___x_5494_; 
v___x_5494_ = l_Std_Channel_forAsync___redArg(v_inst_5489_, v_f_5490_, v_ch_5491_, v_prio_5492_);
return v___x_5494_;
}
}
LEAN_EXPORT void l_Std_Channel_forAsync_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5489_ = stack[1].m_obj;
lean_object* v_f_5490_ = stack[2].m_obj;
lean_object* v_ch_5491_ = stack[3].m_obj;
lean_object* v_prio_5492_ = stack[4].m_obj;
lean_object* v_res_5495_;
v_res_5495_ = l_Std_Channel_forAsync(lean_box(0), v_inst_5489_, v_f_5490_, v_ch_5491_, v_prio_5492_);
stack->m_obj
 = v_res_5495_;
}
LEAN_EXPORT lean_object* l_Std_Channel_forAsync___boxed(lean_object* v_00_u03b1_5496_, lean_object* v_inst_5497_, lean_object* v_f_5498_, lean_object* v_ch_5499_, lean_object* v_prio_5500_, lean_object* v_a_5501_){
_start:
{
lean_object* v_res_5502_; 
v_res_5502_ = l_Std_Channel_forAsync(v_00_u03b1_5496_, v_inst_5497_, v_f_5498_, v_ch_5499_, v_prio_5500_);
return v_res_5502_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(lean_object* v_inst_5503_, lean_object* v_channel_5504_){
_start:
{
lean_object* v___x_5505_; 
v___x_5505_ = l_Std_Channel_recvSelector___redArg(v_inst_5503_, v_channel_5504_);
return v___x_5505_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited___redArg(lean_object* v_inst_5506_){
_start:
{
lean_object* v___f_5507_; lean_object* v___f_5508_; lean_object* v___x_5509_; 
v___f_5507_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5507_, 0, v_inst_5506_);
v___f_5508_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___redArg___closed__1));
v___x_5509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5509_, 0, v___f_5507_);
lean_ctor_set(v___x_5509_, 1, v___f_5508_);
return v___x_5509_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncStreamOfInhabited(lean_object* v_00_u03b1_5510_, lean_object* v_inst_5511_){
_start:
{
lean_object* v___x_5512_; 
v___x_5512_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_5511_);
return v___x_5512_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(lean_object* v_a_5513_){
_start:
{
lean_object* v___x_5514_; 
v___x_5514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5514_, 0, v_a_5513_);
return v___x_5514_;
}
}
lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(lean_object* v___f_5515_, lean_object* v_x_5516_){
_start:
{
if (lean_obj_tag(v_x_5516_) == 0)
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5526_; 
lean_dec_ref(v___f_5515_);
v_a_5518_ = lean_ctor_get(v_x_5516_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v_x_5516_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5520_ = v_x_5516_;
v_isShared_5521_ = v_isSharedCheck_5526_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v_x_5516_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5526_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
lean_object* v___x_5524_; 
v___x_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5523_);
return v___x_5524_;
}
}
}
else
{
lean_object* v_a_5527_; 
v_a_5527_ = lean_ctor_get(v_x_5516_, 0);
lean_inc(v_a_5527_);
lean_dec_ref_known(v_x_5516_, 1);
if (lean_obj_tag(v_a_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5536_; 
lean_dec_ref(v___f_5515_);
v_a_5528_ = lean_ctor_get(v_a_5527_, 0);
v_isSharedCheck_5536_ = !lean_is_exclusive(v_a_5527_);
if (v_isSharedCheck_5536_ == 0)
{
v___x_5530_ = v_a_5527_;
v_isShared_5531_ = v_isSharedCheck_5536_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_a_5528_);
lean_dec(v_a_5527_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5536_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5533_; 
if (v_isShared_5531_ == 0)
{
v___x_5533_ = v___x_5530_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5528_);
v___x_5533_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
lean_object* v___x_5534_; 
v___x_5534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5534_, 0, v___x_5533_);
return v___x_5534_;
}
}
}
else
{
lean_object* v_a_5537_; lean_object* v___x_5538_; uint8_t v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; 
v_a_5537_ = lean_ctor_get(v_a_5527_, 0);
lean_inc(v_a_5537_);
lean_dec_ref_known(v_a_5527_, 1);
v___x_5538_ = lean_unsigned_to_nat(0u);
v___x_5539_ = 0;
v___x_5540_ = lean_task_map(v___f_5515_, v_a_5537_, v___x_5538_, v___x_5539_);
v___x_5541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5541_, 0, v___x_5540_);
return v___x_5541_;
}
}
}
}
LEAN_EXPORT void l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5515_ = stack[0].m_obj;
lean_object* v_x_5516_ = stack[1].m_obj;
lean_object* v_res_5542_;
v_res_5542_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5515_, v_x_5516_);
stack->m_obj
 = v_res_5542_;
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5543_, lean_object* v_x_5544_, lean_object* v___y_5545_){
_start:
{
lean_object* v_res_5546_; 
v_res_5546_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_5543_, v_x_5544_);
return v_res_5546_;
}
}
lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(lean_object* v_inst_5547_, lean_object* v___f_5548_, lean_object* v_receiver_5549_){
_start:
{
lean_object* v___x_5551_; uint8_t v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; 
v___x_5551_ = lean_unsigned_to_nat(0u);
v___x_5552_ = 0;
v___x_5553_ = l_Std_Channel_recv___redArg(v_inst_5547_, v_receiver_5549_);
v___x_5554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5554_, 0, v___x_5553_);
v___x_5555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5554_);
v___x_5556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5556_, 0, v___x_5555_);
v___x_5557_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5551_, v___x_5552_, v___x_5556_, v___f_5548_);
return v___x_5557_;
}
}
LEAN_EXPORT void l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5547_ = stack[0].m_obj;
lean_object* v___f_5548_ = stack[1].m_obj;
lean_object* v_receiver_5549_ = stack[2].m_obj;
lean_object* v_res_5558_;
v_res_5558_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5547_, v___f_5548_, v_receiver_5549_);
stack->m_obj
 = v_res_5558_;
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(lean_object* v_inst_5559_, lean_object* v___f_5560_, lean_object* v_receiver_5561_, lean_object* v___y_5562_){
_start:
{
lean_object* v_res_5563_; 
v_res_5563_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(v_inst_5559_, v___f_5560_, v_receiver_5561_);
return v_res_5563_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited___redArg(lean_object* v_inst_5567_){
_start:
{
lean_object* v___f_5568_; lean_object* v___f_5569_; 
v___f_5568_ = ((lean_object*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1));
v___f_5569_ = lean_alloc_closure((void*)(l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_5569_, 0, v_inst_5567_);
lean_closure_set(v___f_5569_, 1, v___f_5568_);
return v___f_5569_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncReadOfInhabited(lean_object* v_00_u03b1_5570_, lean_object* v_inst_5571_){
_start:
{
lean_object* v___x_5572_; 
v___x_5572_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_5571_);
return v___x_5572_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v_a_5573_){
_start:
{
lean_object* v___x_5574_; 
v___x_5574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5574_, 0, v_a_5573_);
return v___x_5574_;
}
}
lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_5575_, lean_object* v_x_5576_){
_start:
{
if (lean_obj_tag(v_x_5576_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5586_; 
lean_dec_ref(v___f_5575_);
v_a_5578_ = lean_ctor_get(v_x_5576_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v_x_5576_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5580_ = v_x_5576_;
v_isShared_5581_ = v_isSharedCheck_5586_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_dec(v_x_5576_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5586_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5581_ == 0)
{
v___x_5583_ = v___x_5580_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5578_);
v___x_5583_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v___x_5584_; 
v___x_5584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5583_);
return v___x_5584_;
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5588_; uint8_t v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
v_a_5587_ = lean_ctor_get(v_x_5576_, 0);
lean_inc(v_a_5587_);
lean_dec_ref_known(v_x_5576_, 1);
v___x_5588_ = lean_unsigned_to_nat(0u);
v___x_5589_ = 0;
v___x_5590_ = lean_task_map(v___f_5575_, v_a_5587_, v___x_5588_, v___x_5589_);
v___x_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5591_, 0, v___x_5590_);
return v___x_5591_;
}
}
}
LEAN_EXPORT void l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5575_ = stack[0].m_obj;
lean_object* v_x_5576_ = stack[1].m_obj;
lean_object* v_res_5592_;
v_res_5592_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_5575_, v_x_5576_);
stack->m_obj
 = v_res_5592_;
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5593_, lean_object* v_x_5594_, lean_object* v___y_5595_){
_start:
{
lean_object* v_res_5596_; 
v_res_5596_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__1(v___f_5593_, v_x_5594_);
return v_res_5596_;
}
}
lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v___f_5597_, lean_object* v_receiver_5598_, lean_object* v_x_5599_){
_start:
{
lean_object* v___x_5601_; uint8_t v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; 
v___x_5601_ = lean_unsigned_to_nat(0u);
v___x_5602_ = 0;
v___x_5603_ = l_Std_Channel_send___redArg(v_receiver_5598_, v_x_5599_);
v___x_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5603_);
v___x_5605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
v___x_5606_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5601_, v___x_5602_, v___x_5605_, v___f_5597_);
return v___x_5606_;
}
}
LEAN_EXPORT void l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5597_ = stack[0].m_obj;
lean_object* v_receiver_5598_ = stack[1].m_obj;
lean_object* v_x_5599_ = stack[2].m_obj;
lean_object* v_res_5607_;
v_res_5607_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5597_, v_receiver_5598_, v_x_5599_);
stack->m_obj
 = v_res_5607_;
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5608_, lean_object* v_receiver_5609_, lean_object* v_x_5610_, lean_object* v___y_5611_){
_start:
{
lean_object* v_res_5612_; 
v_res_5612_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5608_, v_receiver_5609_, v_x_5610_);
return v_res_5612_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_5618_; lean_object* v___f_5619_; lean_object* v___f_5620_; 
v___x_5618_ = lean_obj_once(&l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5619_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5620_ = lean_alloc_closure((void*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5620_, 0, v___f_5619_);
lean_closure_set(v___f_5620_, 1, v___x_5618_);
return v___f_5620_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___f_5621_; lean_object* v___f_5622_; lean_object* v___f_5623_; lean_object* v___x_5624_; 
v___f_5621_ = ((lean_object*)(l_Std_CloseableChannel_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5622_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5623_ = ((lean_object*)(l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__2));
v___x_5624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5624_, 0, v___f_5623_);
lean_ctor_set(v___x_5624_, 1, v___f_5622_);
lean_ctor_set(v___x_5624_, 2, v___f_5621_);
return v___x_5624_;
}
}
lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_5626_; 
v___x_5626_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___redArg___closed__4);
return v___x_5626_;
}
}
LEAN_EXPORT void l_Std_Channel_instAsyncWriteOfInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5627_;
v_res_5627_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
stack->m_obj
 = v_res_5627_;
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_5628_){
_start:
{
lean_object* v_res_5629_; 
v_res_5629_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
return v_res_5629_;
}
}
static lean_object* _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5630_; 
v___x_5630_ = l_Std_Channel_instAsyncWriteOfInhabited___redArg();
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5631_, lean_object* v_inst_5632_){
_start:
{
lean_object* v___x_5633_; 
v___x_5633_ = lean_obj_once(&l_Std_Channel_instAsyncWriteOfInhabited___closed__0, &l_Std_Channel_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__0);
return v___x_5633_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5634_, lean_object* v_inst_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_5634_, v_inst_5635_);
lean_dec(v_inst_5635_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg(lean_object* v_ch_5637_){
_start:
{
lean_inc_ref(v_ch_5637_);
return v_ch_5637_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___redArg___boxed(lean_object* v_ch_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l_Std_Channel_sync___redArg(v_ch_5638_);
lean_dec_ref(v_ch_5638_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync(lean_object* v_00_u03b1_5640_, lean_object* v_ch_5641_){
_start:
{
lean_inc_ref(v_ch_5641_);
return v_ch_5641_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_sync___boxed(lean_object* v_00_u03b1_5642_, lean_object* v_ch_5643_){
_start:
{
lean_object* v_res_5644_; 
v_res_5644_ = l_Std_Channel_sync(v_00_u03b1_5642_, v_ch_5643_);
lean_dec_ref(v_ch_5643_);
return v_res_5644_;
}
}
lean_object* l_Std_Channel_Sync_new___redArg(lean_object* v_capacity_5645_){
_start:
{
lean_object* v___x_5647_; 
v___x_5647_ = l_Std_CloseableChannel_new___redArg(v_capacity_5645_);
return v___x_5647_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_5645_ = stack[0].m_obj;
lean_object* v_res_5648_;
v_res_5648_ = l_Std_Channel_Sync_new___redArg(v_capacity_5645_);
stack->m_obj
 = v_res_5648_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___redArg___boxed(lean_object* v_capacity_5649_, lean_object* v_a_5650_){
_start:
{
lean_object* v_res_5651_; 
v_res_5651_ = l_Std_Channel_Sync_new___redArg(v_capacity_5649_);
return v_res_5651_;
}
}
lean_object* l_Std_Channel_Sync_new(lean_object* v_00_u03b1_5652_, lean_object* v_capacity_5653_){
_start:
{
lean_object* v___x_5655_; 
v___x_5655_ = l_Std_CloseableChannel_new___redArg(v_capacity_5653_);
return v___x_5655_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_5653_ = stack[1].m_obj;
lean_object* v_res_5656_;
v_res_5656_ = l_Std_Channel_Sync_new(lean_box(0), v_capacity_5653_);
stack->m_obj
 = v_res_5656_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_new___boxed(lean_object* v_00_u03b1_5657_, lean_object* v_capacity_5658_, lean_object* v_a_5659_){
_start:
{
lean_object* v_res_5660_; 
v_res_5660_ = l_Std_Channel_Sync_new(v_00_u03b1_5657_, v_capacity_5658_);
return v_res_5660_;
}
}
uint8_t l_Std_Channel_Sync_trySend___redArg(lean_object* v_ch_5661_, lean_object* v_v_5662_){
_start:
{
uint8_t v___x_5664_; 
v___x_5664_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5661_, v_v_5662_);
return v___x_5664_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5661_ = stack[0].m_obj;
lean_object* v_v_5662_ = stack[1].m_obj;
uint8_t v_res_5665_;
v_res_5665_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5661_, v_v_5662_);
stack->m_num = v_res_5665_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___redArg___boxed(lean_object* v_ch_5666_, lean_object* v_v_5667_, lean_object* v_a_5668_){
_start:
{
uint8_t v_res_5669_; lean_object* v_r_5670_; 
v_res_5669_ = l_Std_Channel_Sync_trySend___redArg(v_ch_5666_, v_v_5667_);
v_r_5670_ = lean_box(v_res_5669_);
return v_r_5670_;
}
}
uint8_t l_Std_Channel_Sync_trySend(lean_object* v_00_u03b1_5671_, lean_object* v_ch_5672_, lean_object* v_v_5673_){
_start:
{
uint8_t v___x_5675_; 
v___x_5675_ = l_Std_CloseableChannel_trySend___redArg(v_ch_5672_, v_v_5673_);
return v___x_5675_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5672_ = stack[1].m_obj;
lean_object* v_v_5673_ = stack[2].m_obj;
uint8_t v_res_5676_;
v_res_5676_ = l_Std_Channel_Sync_trySend(lean_box(0), v_ch_5672_, v_v_5673_);
stack->m_num = v_res_5676_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_trySend___boxed(lean_object* v_00_u03b1_5677_, lean_object* v_ch_5678_, lean_object* v_v_5679_, lean_object* v_a_5680_){
_start:
{
uint8_t v_res_5681_; lean_object* v_r_5682_; 
v_res_5681_ = l_Std_Channel_Sync_trySend(v_00_u03b1_5677_, v_ch_5678_, v_v_5679_);
v_r_5682_ = lean_box(v_res_5681_);
return v_r_5682_;
}
}
lean_object* l_Std_Channel_Sync_send___redArg(lean_object* v_ch_5683_, lean_object* v_v_5684_){
_start:
{
lean_object* v___x_5686_; lean_object* v___x_5687_; 
v___x_5686_ = l_Std_Channel_send___redArg(v_ch_5683_, v_v_5684_);
v___x_5687_ = lean_io_wait(v___x_5686_);
return v___x_5687_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5683_ = stack[0].m_obj;
lean_object* v_v_5684_ = stack[1].m_obj;
lean_object* v_res_5688_;
v_res_5688_ = l_Std_Channel_Sync_send___redArg(v_ch_5683_, v_v_5684_);
stack->m_obj
 = v_res_5688_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___redArg___boxed(lean_object* v_ch_5689_, lean_object* v_v_5690_, lean_object* v_a_5691_){
_start:
{
lean_object* v_res_5692_; 
v_res_5692_ = l_Std_Channel_Sync_send___redArg(v_ch_5689_, v_v_5690_);
return v_res_5692_;
}
}
lean_object* l_Std_Channel_Sync_send(lean_object* v_00_u03b1_5693_, lean_object* v_ch_5694_, lean_object* v_v_5695_){
_start:
{
lean_object* v___x_5697_; 
v___x_5697_ = l_Std_Channel_Sync_send___redArg(v_ch_5694_, v_v_5695_);
return v___x_5697_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5694_ = stack[1].m_obj;
lean_object* v_v_5695_ = stack[2].m_obj;
lean_object* v_res_5698_;
v_res_5698_ = l_Std_Channel_Sync_send(lean_box(0), v_ch_5694_, v_v_5695_);
stack->m_obj
 = v_res_5698_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_send___boxed(lean_object* v_00_u03b1_5699_, lean_object* v_ch_5700_, lean_object* v_v_5701_, lean_object* v_a_5702_){
_start:
{
lean_object* v_res_5703_; 
v_res_5703_ = l_Std_Channel_Sync_send(v_00_u03b1_5699_, v_ch_5700_, v_v_5701_);
return v_res_5703_;
}
}
lean_object* l_Std_Channel_Sync_tryRecv___redArg(lean_object* v_ch_5704_){
_start:
{
lean_object* v___x_5706_; 
v___x_5706_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5704_);
return v___x_5706_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5704_ = stack[0].m_obj;
lean_object* v_res_5707_;
v_res_5707_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5704_);
stack->m_obj
 = v_res_5707_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___redArg___boxed(lean_object* v_ch_5708_, lean_object* v_a_5709_){
_start:
{
lean_object* v_res_5710_; 
v_res_5710_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_5708_);
return v_res_5710_;
}
}
lean_object* l_Std_Channel_Sync_tryRecv(lean_object* v_00_u03b1_5711_, lean_object* v_ch_5712_){
_start:
{
lean_object* v___x_5714_; 
v___x_5714_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_5712_);
return v___x_5714_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5712_ = stack[1].m_obj;
lean_object* v_res_5715_;
v_res_5715_ = l_Std_Channel_Sync_tryRecv(lean_box(0), v_ch_5712_);
stack->m_obj
 = v_res_5715_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_tryRecv___boxed(lean_object* v_00_u03b1_5716_, lean_object* v_ch_5717_, lean_object* v_a_5718_){
_start:
{
lean_object* v_res_5719_; 
v_res_5719_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_5716_, v_ch_5717_);
return v_res_5719_;
}
}
lean_object* l_Std_Channel_Sync_recv___redArg(lean_object* v_inst_5720_, lean_object* v_ch_5721_){
_start:
{
lean_object* v___x_5723_; lean_object* v___x_5724_; 
v___x_5723_ = l_Std_Channel_recv___redArg(v_inst_5720_, v_ch_5721_);
v___x_5724_ = lean_io_wait(v___x_5723_);
return v___x_5724_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5720_ = stack[0].m_obj;
lean_object* v_ch_5721_ = stack[1].m_obj;
lean_object* v_res_5725_;
v_res_5725_ = l_Std_Channel_Sync_recv___redArg(v_inst_5720_, v_ch_5721_);
stack->m_obj
 = v_res_5725_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___redArg___boxed(lean_object* v_inst_5726_, lean_object* v_ch_5727_, lean_object* v_a_5728_){
_start:
{
lean_object* v_res_5729_; 
v_res_5729_ = l_Std_Channel_Sync_recv___redArg(v_inst_5726_, v_ch_5727_);
return v_res_5729_;
}
}
lean_object* l_Std_Channel_Sync_recv(lean_object* v_00_u03b1_5730_, lean_object* v_inst_5731_, lean_object* v_ch_5732_){
_start:
{
lean_object* v___x_5734_; 
v___x_5734_ = l_Std_Channel_Sync_recv___redArg(v_inst_5731_, v_ch_5732_);
return v___x_5734_;
}
}
LEAN_EXPORT void l_Std_Channel_Sync_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5731_ = stack[1].m_obj;
lean_object* v_ch_5732_ = stack[2].m_obj;
lean_object* v_res_5735_;
v_res_5735_ = l_Std_Channel_Sync_recv(lean_box(0), v_inst_5731_, v_ch_5732_);
stack->m_obj
 = v_res_5735_;
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_recv___boxed(lean_object* v_00_u03b1_5736_, lean_object* v_inst_5737_, lean_object* v_ch_5738_, lean_object* v_a_5739_){
_start:
{
lean_object* v_res_5740_; 
v_res_5740_ = l_Std_Channel_Sync_recv(v_00_u03b1_5736_, v_inst_5737_, v_ch_5738_);
return v_res_5740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(lean_object* v_f_5741_, lean_object* v_b_5742_, lean_object* v_toBind_5743_, lean_object* v___f_5744_, lean_object* v_a_5745_){
_start:
{
lean_object* v___x_5746_; lean_object* v___x_5747_; 
v___x_5746_ = lean_apply_2(v_f_5741_, v_a_5745_, v_b_5742_);
v___x_5747_ = lean_apply_4(v_toBind_5743_, lean_box(0), lean_box(0), v___x_5746_, v___f_5744_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(lean_object* v_inst_5748_, lean_object* v_inst_5749_, lean_object* v_inst_5750_, lean_object* v_ch_5751_, lean_object* v_f_5752_, lean_object* v_b_5753_){
_start:
{
lean_object* v_toApplicative_5754_; lean_object* v_toBind_5755_; lean_object* v_toPure_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___f_5759_; lean_object* v___f_5760_; lean_object* v___x_5761_; 
v_toApplicative_5754_ = lean_ctor_get(v_inst_5749_, 0);
v_toBind_5755_ = lean_ctor_get(v_inst_5749_, 1);
lean_inc_n(v_toBind_5755_, 2);
v_toPure_5756_ = lean_ctor_get(v_toApplicative_5754_, 1);
lean_inc(v_toPure_5756_);
lean_inc_ref(v_ch_5751_);
lean_inc(v_inst_5748_);
v___x_5757_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_recv___boxed), 4, 3);
lean_closure_set(v___x_5757_, 0, lean_box(0));
lean_closure_set(v___x_5757_, 1, v_inst_5748_);
lean_closure_set(v___x_5757_, 2, v_ch_5751_);
lean_inc(v_inst_5750_);
v___x_5758_ = lean_apply_2(v_inst_5750_, lean_box(0), v___x_5757_);
lean_inc(v_f_5752_);
v___f_5759_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5759_, 0, v_toPure_5756_);
lean_closure_set(v___f_5759_, 1, v_inst_5748_);
lean_closure_set(v___f_5759_, 2, v_inst_5749_);
lean_closure_set(v___f_5759_, 3, v_inst_5750_);
lean_closure_set(v___f_5759_, 4, v_ch_5751_);
lean_closure_set(v___f_5759_, 5, v_f_5752_);
v___f_5760_ = lean_alloc_closure((void*)(l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1), 5, 4);
lean_closure_set(v___f_5760_, 0, v_f_5752_);
lean_closure_set(v___f_5760_, 1, v_b_5753_);
lean_closure_set(v___f_5760_, 2, v_toBind_5755_);
lean_closure_set(v___f_5760_, 3, v___f_5759_);
v___x_5761_ = lean_apply_4(v_toBind_5755_, lean_box(0), lean_box(0), v___x_5758_, v___f_5760_);
return v___x_5761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(lean_object* v_toPure_5762_, lean_object* v_inst_5763_, lean_object* v_inst_5764_, lean_object* v_inst_5765_, lean_object* v_ch_5766_, lean_object* v_f_5767_, lean_object* v_____do__lift_5768_){
_start:
{
if (lean_obj_tag(v_____do__lift_5768_) == 0)
{
lean_object* v_a_5769_; lean_object* v___x_5770_; 
lean_dec(v_f_5767_);
lean_dec_ref(v_ch_5766_);
lean_dec(v_inst_5765_);
lean_dec_ref(v_inst_5764_);
lean_dec(v_inst_5763_);
v_a_5769_ = lean_ctor_get(v_____do__lift_5768_, 0);
lean_inc(v_a_5769_);
lean_dec_ref_known(v_____do__lift_5768_, 1);
v___x_5770_ = lean_apply_2(v_toPure_5762_, lean_box(0), v_a_5769_);
return v___x_5770_;
}
else
{
lean_object* v_a_5771_; lean_object* v___x_5772_; 
lean_dec(v_toPure_5762_);
v_a_5771_ = lean_ctor_get(v_____do__lift_5768_, 0);
lean_inc(v_a_5771_);
lean_dec_ref_known(v_____do__lift_5768_, 1);
v___x_5772_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5763_, v_inst_5764_, v_inst_5765_, v_ch_5766_, v_f_5767_, v_a_5771_);
return v___x_5772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(lean_object* v_00_u03b1_5773_, lean_object* v_m_5774_, lean_object* v_00_u03b2_5775_, lean_object* v_inst_5776_, lean_object* v_inst_5777_, lean_object* v_inst_5778_, lean_object* v_ch_5779_, lean_object* v_f_5780_, lean_object* v_b_5781_){
_start:
{
lean_object* v___x_5782_; 
v___x_5782_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5776_, v_inst_5777_, v_inst_5778_, v_ch_5779_, v_f_5780_, v_b_5781_);
return v___x_5782_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(lean_object* v_inst_5783_, lean_object* v_inst_5784_, lean_object* v_inst_5785_, lean_object* v_ch_5786_, lean_object* v_b_5787_, lean_object* v_f_5788_){
_start:
{
lean_object* v___x_5789_; 
v___x_5789_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5783_, v_inst_5784_, v_inst_5785_, v_ch_5786_, v_f_5788_, v_b_5787_);
return v___x_5789_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(lean_object* v_00_u03b1_5790_, lean_object* v_m_5791_, lean_object* v_inst_5792_, lean_object* v_inst_5793_, lean_object* v_inst_5794_, lean_object* v_00_u03b2_5795_, lean_object* v_ch_5796_, lean_object* v_b_5797_, lean_object* v_f_5798_){
_start:
{
lean_object* v___x_5799_; 
v___x_5799_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5792_, v_inst_5793_, v_inst_5794_, v_ch_5796_, v_f_5798_, v_b_5797_);
return v___x_5799_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5800_, lean_object* v_inst_5801_, lean_object* v_inst_5802_, lean_object* v_00_u03b2_5803_, lean_object* v_ch_5804_, lean_object* v_b_5805_, lean_object* v_f_5806_){
_start:
{
lean_object* v___x_5807_; 
v___x_5807_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(v_inst_5800_, v_inst_5801_, v_inst_5802_, v_ch_5804_, v_f_5806_, v_b_5805_);
return v___x_5807_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5808_, lean_object* v_inst_5809_, lean_object* v_inst_5810_){
_start:
{
lean_object* v___f_5811_; 
v___f_5811_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5811_, 0, v_inst_5808_);
lean_closure_set(v___f_5811_, 1, v_inst_5809_);
lean_closure_set(v___f_5811_, 2, v_inst_5810_);
return v___f_5811_;
}
}
LEAN_EXPORT lean_object* l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5812_, lean_object* v_m_5813_, lean_object* v_inst_5814_, lean_object* v_inst_5815_, lean_object* v_inst_5816_){
_start:
{
lean_object* v___f_5817_; 
v___f_5817_ = lean_alloc_closure((void*)(l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5817_, 0, v_inst_5814_);
lean_closure_set(v___f_5817_, 1, v_inst_5815_);
lean_closure_set(v___f_5817_, 2, v_inst_5816_);
return v___f_5817_;
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

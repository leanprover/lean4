// Lean compiler output
// Module: Std.Sync.Broadcast
// Imports: public import Std.Data public import Init.Data.Queue public import Init.Data.Vector public import Std.Sync.Mutex public import Std.Async.IO
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
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_Queue_enqueue___redArg(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Queue_empty(lean_object*);
lean_object* l_Std_Queue_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_repr___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonad(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Broadcast_instReprError_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Broadcast.Error.closed"};
static const lean_object* l_Std_Broadcast_instReprError_repr___closed__0 = (const lean_object*)&l_Std_Broadcast_instReprError_repr___closed__0_value;
static const lean_ctor_object l_Std_Broadcast_instReprError_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Broadcast_instReprError_repr___closed__0_value)}};
static const lean_object* l_Std_Broadcast_instReprError_repr___closed__1 = (const lean_object*)&l_Std_Broadcast_instReprError_repr___closed__1_value;
static const lean_string_object l_Std_Broadcast_instReprError_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Broadcast.Error.alreadyClosed"};
static const lean_object* l_Std_Broadcast_instReprError_repr___closed__2 = (const lean_object*)&l_Std_Broadcast_instReprError_repr___closed__2_value;
static const lean_ctor_object l_Std_Broadcast_instReprError_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Broadcast_instReprError_repr___closed__2_value)}};
static const lean_object* l_Std_Broadcast_instReprError_repr___closed__3 = (const lean_object*)&l_Std_Broadcast_instReprError_repr___closed__3_value;
static const lean_string_object l_Std_Broadcast_instReprError_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Std.Broadcast.Error.notSubscribed"};
static const lean_object* l_Std_Broadcast_instReprError_repr___closed__4 = (const lean_object*)&l_Std_Broadcast_instReprError_repr___closed__4_value;
static const lean_ctor_object l_Std_Broadcast_instReprError_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Broadcast_instReprError_repr___closed__4_value)}};
static const lean_object* l_Std_Broadcast_instReprError_repr___closed__5 = (const lean_object*)&l_Std_Broadcast_instReprError_repr___closed__5_value;
static lean_once_cell_t l_Std_Broadcast_instReprError_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_instReprError_repr___closed__6;
static lean_once_cell_t l_Std_Broadcast_instReprError_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_instReprError_repr___closed__7;
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_instReprError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_instReprError_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_instReprError___closed__0 = (const lean_object*)&l_Std_Broadcast_instReprError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Broadcast_instReprError = (const lean_object*)&l_Std_Broadcast_instReprError___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Broadcast_Error_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Broadcast_instDecidableEqError(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Broadcast_instDecidableEqError___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Broadcast_instHashableError_hash(uint8_t);
LEAN_EXPORT lean_object* l_Std_Broadcast_instHashableError_hash___boxed(lean_object*);
static const lean_closure_object l_Std_Broadcast_instHashableError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_instHashableError_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_instHashableError___closed__0 = (const lean_object*)&l_Std_Broadcast_instHashableError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Broadcast_instHashableError = (const lean_object*)&l_Std_Broadcast_instHashableError___closed__0_value;
static const lean_string_object l_Std_instToStringBroadcastError___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "attempted to send on an already closed channel"};
static const lean_object* l_Std_instToStringBroadcastError___lam__0___closed__0 = (const lean_object*)&l_Std_instToStringBroadcastError___lam__0___closed__0_value;
static const lean_string_object l_Std_instToStringBroadcastError___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "attempted to close an already closed broadcast channel"};
static const lean_object* l_Std_instToStringBroadcastError___lam__0___closed__1 = (const lean_object*)&l_Std_instToStringBroadcastError___lam__0___closed__1_value;
static const lean_string_object l_Std_instToStringBroadcastError___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "receiver not subscribed in a broadcast channel"};
static const lean_object* l_Std_instToStringBroadcastError___lam__0___closed__2 = (const lean_object*)&l_Std_instToStringBroadcastError___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStringBroadcastError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStringBroadcastError___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStringBroadcastError___closed__0 = (const lean_object*)&l_Std_instToStringBroadcastError___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instToStringBroadcastError = (const lean_object*)&l_Std_instToStringBroadcastError___closed__0_value;
static const lean_ctor_object l_Std_instMonadLiftBroadcastIO___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_instToStringBroadcastError___lam__0___closed__0_value)}};
static const lean_object* l_Std_instMonadLiftBroadcastIO___lam__0___closed__0 = (const lean_object*)&l_Std_instMonadLiftBroadcastIO___lam__0___closed__0_value;
static const lean_ctor_object l_Std_instMonadLiftBroadcastIO___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_instToStringBroadcastError___lam__0___closed__1_value)}};
static const lean_object* l_Std_instMonadLiftBroadcastIO___lam__0___closed__1 = (const lean_object*)&l_Std_instMonadLiftBroadcastIO___lam__0___closed__1_value;
static const lean_ctor_object l_Std_instMonadLiftBroadcastIO___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Std_instToStringBroadcastError___lam__0___closed__2_value)}};
static const lean_object* l_Std_instMonadLiftBroadcastIO___lam__0___closed__2 = (const lean_object*)&l_Std_instMonadLiftBroadcastIO___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_instMonadLiftBroadcastIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instMonadLiftBroadcastIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instMonadLiftBroadcastIO___closed__0 = (const lean_object*)&l_Std_instMonadLiftBroadcastIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instMonadLiftBroadcastIO = (const lean_object*)&l_Std_instMonadLiftBroadcastIO___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_instInhabitedSlot_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_instInhabitedSlot_default___closed__0 = (const lean_object*)&l_Std_instInhabitedSlot_default___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default(lean_object*);
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot(lean_object*);
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__1_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__1_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__2 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__2_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__2_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__3 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__3_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__4 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__4_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__4_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__3_value),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__6 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__6_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__8 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__8_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__8_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__9 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__9_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pos"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__10 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__10_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__10_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__11 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__11_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "remaining"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__13 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__13_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__13_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__14 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__14_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__16 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__16_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__19 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__19_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__16_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__20 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot(lean_object*, lean_object*);
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__0_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__1_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__2 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__2_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__3 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__3_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4_value_aux_0),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4_value_aux_1),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4_value;
static const lean_array_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__6 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__6_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7_value_aux_0),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7_value_aux_1),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7_value_aux_2),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__8 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__8_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9_value;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11_value_aux_0),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11_value_aux_1),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11_value_aux_2),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13;
static const lean_string_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__14 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__14_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15_value_aux_0),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15_value_aux_1),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15_value_aux_2),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9_value),((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__16 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__16_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__0_value;
static const lean_array_object l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__1_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2_value;
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0_value;
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__0 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__0_value)}};
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1_value;
static const lean_closure_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0 = (const lean_object*)&l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__0_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_new___auto__1;
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_send___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_send___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_send___redArg___closed__0 = (const lean_object*)&l_Std_Broadcast_send___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__1_value;
static const lean_ctor_object l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0_value),((lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__1_value)}};
static const lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__1_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__1_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__1(lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_const___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__0_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__1_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Broadcast_send___redArg___closed__0_value),((lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__1_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3_value;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___auto__3;
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_Sync_send___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lean_io_error_to_string, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Sync_send___redArg___closed__0 = (const lean_object*)&l_Std_Broadcast_Sync_send___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Broadcast_Error_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Broadcast_Error_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Std_Broadcast_Error_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg(lean_object* v_closed_23_){
_start:
{
lean_inc(v_closed_23_);
return v_closed_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg___boxed(lean_object* v_closed_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Broadcast_Error_closed_elim___redArg(v_closed_24_);
lean_dec(v_closed_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_closed_29_){
_start:
{
lean_inc(v_closed_29_);
return v_closed_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_closed_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Std_Broadcast_Error_closed_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_closed_33_);
lean_dec(v_closed_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg(lean_object* v_alreadyClosed_36_){
_start:
{
lean_inc(v_alreadyClosed_36_);
return v_alreadyClosed_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg___boxed(lean_object* v_alreadyClosed_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Broadcast_Error_alreadyClosed_elim___redArg(v_alreadyClosed_37_);
lean_dec(v_alreadyClosed_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_alreadyClosed_42_){
_start:
{
lean_inc(v_alreadyClosed_42_);
return v_alreadyClosed_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_alreadyClosed_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Std_Broadcast_Error_alreadyClosed_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_alreadyClosed_46_);
lean_dec(v_alreadyClosed_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg(lean_object* v_notSubscribed_49_){
_start:
{
lean_inc(v_notSubscribed_49_);
return v_notSubscribed_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg___boxed(lean_object* v_notSubscribed_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Std_Broadcast_Error_notSubscribed_elim___redArg(v_notSubscribed_50_);
lean_dec(v_notSubscribed_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_notSubscribed_55_){
_start:
{
lean_inc(v_notSubscribed_55_);
return v_notSubscribed_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_notSubscribed_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Std_Broadcast_Error_notSubscribed_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_notSubscribed_59_);
lean_dec(v_notSubscribed_59_);
return v_res_61_;
}
}
static lean_object* _init_l_Std_Broadcast_instReprError_repr___closed__6(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(2u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Std_Broadcast_instReprError_repr___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr(uint8_t v_x_75_, lean_object* v_prec_76_){
_start:
{
lean_object* v___y_78_; lean_object* v___y_85_; lean_object* v___y_92_; 
switch(v_x_75_)
{
case 0:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1024u);
v___x_99_ = lean_nat_dec_le(v___x_98_, v_prec_76_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_78_ = v___x_100_;
goto v___jp_77_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_78_ = v___x_101_;
goto v___jp_77_;
}
}
case 1:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_76_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_85_ = v___x_104_;
goto v___jp_84_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_85_ = v___x_105_;
goto v___jp_84_;
}
}
default: 
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_76_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_92_ = v___x_108_;
goto v___jp_91_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_92_ = v___x_109_;
goto v___jp_91_;
}
}
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__1));
lean_inc(v___y_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___y_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = 0;
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_81_);
v___x_83_ = l_Repr_addAppParen(v___x_82_, v_prec_76_);
return v___x_83_;
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__3));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_76_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__5));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_76_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr___boxed(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
uint8_t v_x_171__boxed_112_; lean_object* v_res_113_; 
v_x_171__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Std_Broadcast_instReprError_repr(v_x_171__boxed_112_, v_prec_111_);
lean_dec(v_prec_111_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Std_Broadcast_Error_ofNat(lean_object* v_n_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_nat_dec_le(v_n_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_dec_le(v_n_116_, v___x_119_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ofNat___boxed(lean_object* v_n_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Std_Broadcast_Error_ofNat(v_n_124_);
lean_dec(v_n_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Std_Broadcast_instDecidableEqError(uint8_t v_x_127_, uint8_t v_y_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = l_Std_Broadcast_Error_ctorIdx(v_x_127_);
v___x_130_ = l_Std_Broadcast_Error_ctorIdx(v_y_128_);
v___x_131_ = lean_nat_dec_eq(v___x_129_, v___x_130_);
lean_dec(v___x_130_);
lean_dec(v___x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instDecidableEqError___boxed(lean_object* v_x_132_, lean_object* v_y_133_){
_start:
{
uint8_t v_x_20__boxed_134_; uint8_t v_y_21__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_x_20__boxed_134_ = lean_unbox(v_x_132_);
v_y_21__boxed_135_ = lean_unbox(v_y_133_);
v_res_136_ = l_Std_Broadcast_instDecidableEqError(v_x_20__boxed_134_, v_y_21__boxed_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint64_t l_Std_Broadcast_instHashableError_hash(uint8_t v_x_138_){
_start:
{
switch(v_x_138_)
{
case 0:
{
uint64_t v___x_139_; 
v___x_139_ = 0ULL;
return v___x_139_;
}
case 1:
{
uint64_t v___x_140_; 
v___x_140_ = 1ULL;
return v___x_140_;
}
default: 
{
uint64_t v___x_141_; 
v___x_141_ = 2ULL;
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instHashableError_hash___boxed(lean_object* v_x_142_){
_start:
{
uint8_t v_x_40__boxed_143_; uint64_t v_res_144_; lean_object* v_r_145_; 
v_x_40__boxed_143_ = lean_unbox(v_x_142_);
v_res_144_ = l_Std_Broadcast_instHashableError_hash(v_x_40__boxed_143_);
v_r_145_ = lean_box_uint64(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0(uint8_t v_x_151_){
_start:
{
switch(v_x_151_)
{
case 0:
{
lean_object* v___x_152_; 
v___x_152_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
return v___x_152_;
}
case 1:
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
return v___x_153_;
}
default: 
{
lean_object* v___x_154_; 
v___x_154_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0___boxed(lean_object* v_x_155_){
_start:
{
uint8_t v_x_36__boxed_156_; lean_object* v_res_157_; 
v_x_36__boxed_156_ = lean_unbox(v_x_155_);
v_res_157_ = l_Std_instToStringBroadcastError___lam__0(v_x_36__boxed_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0(lean_object* v_00_u03b1_166_, lean_object* v_x_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_apply_1(v_x_167_, lean_box(0));
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_195_; 
v_a_178_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_195_ == 0)
{
v___x_180_ = v___x_169_;
v_isShared_181_ = v_isSharedCheck_195_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_169_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_195_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
uint8_t v___x_182_; 
v___x_182_ = lean_unbox(v_a_178_);
lean_dec(v_a_178_);
switch(v___x_182_)
{
case 0:
{
lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_183_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
case 1:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_187_);
v___x_189_ = v___x_180_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
default: 
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_191_);
v___x_193_ = v___x_180_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0___boxed(lean_object* v_00_u03b1_196_, lean_object* v_x_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_instMonadLiftBroadcastIO___lam__0(v_00_u03b1_196_, v_x_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(lean_object* v_c_202_, uint8_t v_b_203_){
_start:
{
lean_object* v_promise_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_promise_205_ = lean_ctor_get(v_c_202_, 0);
v___x_206_ = lean_box(v_b_203_);
v___x_207_ = lean_io_promise_resolve(v___x_206_, v_promise_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg___boxed(lean_object* v_c_208_, lean_object* v_b_209_, lean_object* v_a_210_){
_start:
{
uint8_t v_b_boxed_211_; lean_object* v_res_212_; 
v_b_boxed_211_ = lean_unbox(v_b_209_);
v_res_212_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_208_, v_b_boxed_211_);
lean_dec_ref(v_c_208_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(lean_object* v_00_u03b1_213_, lean_object* v_c_214_, uint8_t v_b_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_214_, v_b_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___boxed(lean_object* v_00_u03b1_218_, lean_object* v_c_219_, lean_object* v_b_220_, lean_object* v_a_221_){
_start:
{
uint8_t v_b_boxed_222_; lean_object* v_res_223_; 
v_b_boxed_222_ = lean_unbox(v_b_220_);
v_res_223_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(v_00_u03b1_218_, v_c_219_, v_b_boxed_222_);
lean_dec_ref(v_c_219_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default(lean_object* v_00_u03b1_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = ((lean_object*)(l_Std_instInhabitedSlot_default___closed__0));
return v___x_228_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0(void){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_instInhabitedSlot_default(lean_box(0));
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot(lean_object* v_a_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0, &l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0);
return v___x_231_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(9u);
v___x_246_ = lean_nat_to_int(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(7u);
v___x_254_ = lean_nat_to_int(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(13u);
v___x_259_ = lean_nat_to_int(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0));
v___x_262_ = lean_string_length(v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17);
v___x_264_ = lean_nat_to_int(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(lean_object* v_inst_269_, lean_object* v_x_270_){
_start:
{
lean_object* v_value_271_; lean_object* v_pos_272_; lean_object* v_remaining_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_value_271_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_value_271_);
v_pos_272_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_pos_272_);
v_remaining_273_ = lean_ctor_get(v_x_270_, 2);
lean_inc(v_remaining_273_);
lean_dec_ref(v_x_270_);
v___x_274_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5));
v___x_275_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__6));
v___x_276_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Option_repr___redArg(v_inst_269_, v_value_271_, v___x_277_);
v___x_279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_276_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = 0;
v___x_281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*1, v___x_280_);
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_275_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__9));
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_box(1);
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__11));
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_274_);
v___x_290_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12);
v___x_291_ = l_Nat_reprFast(v_pos_272_);
v___x_292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_290_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*1, v___x_280_);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_289_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_283_);
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_285_);
v___x_298_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__14));
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_274_);
v___x_301_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15);
v___x_302_ = l_Nat_reprFast(v_remaining_273_);
v___x_303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
v___x_304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_301_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*1, v___x_280_);
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_300_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18);
v___x_308_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__19));
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_306_);
v___x_310_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__20));
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_307_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_280_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(lean_object* v_00_u03b1_314_, lean_object* v_inst_315_, lean_object* v_x_316_, lean_object* v_prec_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(v_inst_315_, v_x_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_x_321_, lean_object* v_prec_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(v_00_u03b1_319_, v_inst_320_, v_x_321_, v_prec_322_);
lean_dec(v_prec_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot___redArg(lean_object* v_inst_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, v_inst_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot(lean_object* v_00_u03b1_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_328_, 0, lean_box(0));
lean_closure_set(v___x_328_, 1, v_inst_327_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10));
v___x_356_ = l_Lean_mkAtom(v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12);
v___x_358_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_359_ = lean_array_push(v___x_358_, v___x_357_);
return v___x_359_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__16));
v___x_371_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_372_ = lean_array_push(v___x_371_, v___x_370_);
return v___x_372_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_373_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17);
v___x_374_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15));
v___x_375_ = lean_box(2);
v___x_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___x_373_);
return v___x_376_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18);
v___x_378_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13);
v___x_379_ = lean_array_push(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19);
v___x_381_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11));
v___x_382_ = lean_box(2);
v___x_383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_380_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20);
v___x_385_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_386_ = lean_array_push(v___x_385_, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21);
v___x_388_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9));
v___x_389_ = lean_box(2);
v___x_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
lean_ctor_set(v___x_390_, 2, v___x_387_);
return v___x_390_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22);
v___x_392_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_393_ = lean_array_push(v___x_392_, v___x_391_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23);
v___x_395_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7));
v___x_396_ = lean_box(2);
v___x_397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_394_);
return v___x_397_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24);
v___x_399_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_400_ = lean_array_push(v___x_399_, v___x_398_);
return v___x_400_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25);
v___x_402_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4));
v___x_403_ = lean_box(2);
v___x_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_401_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1(void){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(lean_object* v_x_406_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Std_instInhabitedSlot_default___closed__0));
v___x_409_ = lean_st_mk_ref(v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(v_x_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(lean_object* v_n_413_, lean_object* v_f_414_, lean_object* v_xs_415_, lean_object* v_k_416_, lean_object* v_acc_417_){
_start:
{
uint8_t v___x_419_; 
v___x_419_ = lean_nat_dec_lt(v_k_416_, v_n_413_);
if (v___x_419_ == 0)
{
lean_dec(v_k_416_);
lean_dec_ref(v_f_414_);
return v_acc_417_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = lean_array_fget_borrowed(v_xs_415_, v_k_416_);
lean_inc_ref(v_f_414_);
lean_inc(v___x_420_);
v___x_421_ = lean_apply_2(v_f_414_, v___x_420_, lean_box(0));
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_k_416_, v___x_422_);
lean_dec(v_k_416_);
v___x_424_ = lean_array_push(v_acc_417_, v___x_421_);
v_k_416_ = v___x_423_;
v_acc_417_ = v___x_424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_426_, lean_object* v_f_427_, lean_object* v_xs_428_, lean_object* v_k_429_, lean_object* v_acc_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_426_, v_f_427_, v_xs_428_, v_k_429_, v_acc_430_);
lean_dec_ref(v_xs_428_);
lean_dec(v_n_426_);
return v_res_432_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2(void){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_Queue_empty(lean_box(0));
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(lean_object* v_capacity_437_){
_start:
{
lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___f_439_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__0));
v___x_440_ = lean_box(0);
lean_inc(v_capacity_437_);
v___x_441_ = lean_mk_array(v_capacity_437_, v___x_440_);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__1));
v___x_444_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_capacity_437_, v___f_439_, v___x_441_, v___x_442_, v___x_443_);
lean_dec_ref(v___x_441_);
v___x_445_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_446_ = lean_box(1);
v___x_447_ = 0;
v___x_448_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_448_, 0, v___x_445_);
lean_ctor_set(v___x_448_, 1, v___x_445_);
lean_ctor_set(v___x_448_, 2, v_capacity_437_);
lean_ctor_set(v___x_448_, 3, v___x_442_);
lean_ctor_set(v___x_448_, 4, v___x_444_);
lean_ctor_set(v___x_448_, 5, v___x_442_);
lean_ctor_set(v___x_448_, 6, v___x_442_);
lean_ctor_set(v___x_448_, 7, v___x_446_);
lean_ctor_set(v___x_448_, 8, v___x_442_);
lean_ctor_set(v___x_448_, 9, v___x_442_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*10, v___x_447_);
v___x_449_ = l_Std_Mutex_new___redArg(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___boxed(lean_object* v_capacity_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new(lean_object* v_00_u03b1_453_, lean_object* v_capacity_454_, lean_object* v_h_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_454_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___boxed(lean_object* v_00_u03b1_458_, lean_object* v_capacity_459_, lean_object* v_h_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new(v_00_u03b1_458_, v_capacity_459_, v_h_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_n_465_, lean_object* v_f_466_, lean_object* v_xs_467_, lean_object* v_k_468_, lean_object* v_h_469_, lean_object* v_acc_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_465_, v_f_466_, v_xs_467_, v_k_468_, v_acc_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_n_475_, lean_object* v_f_476_, lean_object* v_xs_477_, lean_object* v_k_478_, lean_object* v_h_479_, lean_object* v_acc_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(v_00_u03b1_473_, v_00_u03b2_474_, v_n_475_, v_f_476_, v_xs_477_, v_k_478_, v_h_479_, v_acc_480_);
lean_dec_ref(v_xs_477_);
lean_dec(v_n_475_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(lean_object* v_mutex_483_, lean_object* v_k_484_){
_start:
{
lean_object* v_ref_486_; lean_object* v_mutex_487_; lean_object* v___x_488_; lean_object* v_r_489_; 
v_ref_486_ = lean_ctor_get(v_mutex_483_, 0);
lean_inc(v_ref_486_);
v_mutex_487_ = lean_ctor_get(v_mutex_483_, 1);
lean_inc(v_mutex_487_);
lean_dec_ref(v_mutex_483_);
v___x_488_ = lean_io_basemutex_lock(v_mutex_487_);
v_r_489_ = lean_apply_2(v_k_484_, v_ref_486_, lean_box(0));
if (lean_obj_tag(v_r_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_498_; 
v_a_490_ = lean_ctor_get(v_r_489_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v_r_489_);
if (v_isSharedCheck_498_ == 0)
{
v___x_492_ = v_r_489_;
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v_r_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_498_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_io_basemutex_unlock(v_mutex_487_);
lean_dec(v_mutex_487_);
if (v_isShared_493_ == 0)
{
v___x_496_ = v___x_492_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_490_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_a_499_ = lean_ctor_get(v_r_489_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_r_489_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v_r_489_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v_r_489_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_io_basemutex_unlock(v_mutex_487_);
lean_dec(v_mutex_487_);
if (v_isShared_502_ == 0)
{
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_499_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg___boxed(lean_object* v_mutex_508_, lean_object* v_k_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_508_, v_k_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_, lean_object* v_mutex_514_, lean_object* v_k_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_514_, v_k_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___boxed(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_mutex_520_, lean_object* v_k_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(v_00_u03b1_518_, v_00_u03b2_519_, v_mutex_520_, v_k_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(lean_object* v_k_524_, lean_object* v_v_525_, lean_object* v_t_526_){
_start:
{
if (lean_obj_tag(v_t_526_) == 0)
{
lean_object* v_size_527_; lean_object* v_k_528_; lean_object* v_v_529_; lean_object* v_l_530_; lean_object* v_r_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_812_; 
v_size_527_ = lean_ctor_get(v_t_526_, 0);
v_k_528_ = lean_ctor_get(v_t_526_, 1);
v_v_529_ = lean_ctor_get(v_t_526_, 2);
v_l_530_ = lean_ctor_get(v_t_526_, 3);
v_r_531_ = lean_ctor_get(v_t_526_, 4);
v_isSharedCheck_812_ = !lean_is_exclusive(v_t_526_);
if (v_isSharedCheck_812_ == 0)
{
v___x_533_ = v_t_526_;
v_isShared_534_ = v_isSharedCheck_812_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_r_531_);
lean_inc(v_l_530_);
lean_inc(v_v_529_);
lean_inc(v_k_528_);
lean_inc(v_size_527_);
lean_dec(v_t_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_812_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
uint8_t v___x_535_; 
v___x_535_ = lean_nat_dec_lt(v_k_524_, v_k_528_);
if (v___x_535_ == 0)
{
uint8_t v___x_536_; 
v___x_536_ = lean_nat_dec_eq(v_k_524_, v_k_528_);
if (v___x_536_ == 0)
{
lean_object* v_impl_537_; lean_object* v___x_538_; 
lean_dec(v_size_527_);
v_impl_537_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_524_, v_v_525_, v_r_531_);
v___x_538_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_530_) == 0)
{
lean_object* v_size_539_; lean_object* v_size_540_; lean_object* v_k_541_; lean_object* v_v_542_; lean_object* v_l_543_; lean_object* v_r_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_size_539_ = lean_ctor_get(v_l_530_, 0);
v_size_540_ = lean_ctor_get(v_impl_537_, 0);
lean_inc(v_size_540_);
v_k_541_ = lean_ctor_get(v_impl_537_, 1);
lean_inc(v_k_541_);
v_v_542_ = lean_ctor_get(v_impl_537_, 2);
lean_inc(v_v_542_);
v_l_543_ = lean_ctor_get(v_impl_537_, 3);
lean_inc(v_l_543_);
v_r_544_ = lean_ctor_get(v_impl_537_, 4);
lean_inc(v_r_544_);
v___x_545_ = lean_unsigned_to_nat(3u);
v___x_546_ = lean_nat_mul(v___x_545_, v_size_539_);
v___x_547_ = lean_nat_dec_lt(v___x_546_, v_size_540_);
lean_dec(v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v_r_544_);
lean_dec(v_l_543_);
lean_dec(v_v_542_);
lean_dec(v_k_541_);
v___x_548_ = lean_nat_add(v___x_538_, v_size_539_);
v___x_549_ = lean_nat_add(v___x_548_, v_size_540_);
lean_dec(v_size_540_);
lean_dec(v___x_548_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v_impl_537_);
lean_ctor_set(v___x_533_, 0, v___x_549_);
v___x_551_ = v___x_533_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_l_530_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_impl_537_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
else
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_616_; 
v_isSharedCheck_616_ = !lean_is_exclusive(v_impl_537_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; 
v_unused_617_ = lean_ctor_get(v_impl_537_, 4);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_impl_537_, 3);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_impl_537_, 2);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_impl_537_, 1);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_impl_537_, 0);
lean_dec(v_unused_621_);
v___x_554_ = v_impl_537_;
v_isShared_555_ = v_isSharedCheck_616_;
goto v_resetjp_553_;
}
else
{
lean_dec(v_impl_537_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_616_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_size_556_; lean_object* v_k_557_; lean_object* v_v_558_; lean_object* v_l_559_; lean_object* v_r_560_; lean_object* v_size_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_size_556_ = lean_ctor_get(v_l_543_, 0);
v_k_557_ = lean_ctor_get(v_l_543_, 1);
v_v_558_ = lean_ctor_get(v_l_543_, 2);
v_l_559_ = lean_ctor_get(v_l_543_, 3);
v_r_560_ = lean_ctor_get(v_l_543_, 4);
v_size_561_ = lean_ctor_get(v_r_544_, 0);
v___x_562_ = lean_unsigned_to_nat(2u);
v___x_563_ = lean_nat_mul(v___x_562_, v_size_561_);
v___x_564_ = lean_nat_dec_lt(v_size_556_, v___x_563_);
lean_dec(v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_592_; 
lean_inc(v_r_560_);
lean_inc(v_l_559_);
lean_inc(v_v_558_);
lean_inc(v_k_557_);
v_isSharedCheck_592_ = !lean_is_exclusive(v_l_543_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; lean_object* v_unused_594_; lean_object* v_unused_595_; lean_object* v_unused_596_; lean_object* v_unused_597_; 
v_unused_593_ = lean_ctor_get(v_l_543_, 4);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_l_543_, 3);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_l_543_, 2);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_l_543_, 1);
lean_dec(v_unused_596_);
v_unused_597_ = lean_ctor_get(v_l_543_, 0);
lean_dec(v_unused_597_);
v___x_566_ = v_l_543_;
v_isShared_567_ = v_isSharedCheck_592_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_l_543_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_592_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_582_; 
v___x_568_ = lean_nat_add(v___x_538_, v_size_539_);
v___x_569_ = lean_nat_add(v___x_568_, v_size_540_);
lean_dec(v_size_540_);
if (lean_obj_tag(v_l_559_) == 0)
{
lean_object* v_size_590_; 
v_size_590_ = lean_ctor_get(v_l_559_, 0);
lean_inc(v_size_590_);
v___y_582_ = v_size_590_;
goto v___jp_581_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___y_582_ = v___x_591_;
goto v___jp_581_;
}
v___jp_570_:
{
lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_574_ = lean_nat_add(v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec(v___y_572_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 4, v_r_544_);
lean_ctor_set(v___x_566_, 3, v_r_560_);
lean_ctor_set(v___x_566_, 2, v_v_542_);
lean_ctor_set(v___x_566_, 1, v_k_541_);
lean_ctor_set(v___x_566_, 0, v___x_574_);
v___x_576_ = v___x_566_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_k_541_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_v_542_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_r_560_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v_r_544_);
v___x_576_ = v_reuseFailAlloc_580_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 4, v___x_576_);
lean_ctor_set(v___x_554_, 3, v___y_571_);
lean_ctor_set(v___x_554_, 2, v_v_558_);
lean_ctor_set(v___x_554_, 1, v_k_557_);
lean_ctor_set(v___x_554_, 0, v___x_569_);
v___x_578_ = v___x_554_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_k_557_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v_v_558_);
lean_ctor_set(v_reuseFailAlloc_579_, 3, v___y_571_);
lean_ctor_set(v_reuseFailAlloc_579_, 4, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
v___jp_581_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = lean_nat_add(v___x_568_, v___y_582_);
lean_dec(v___y_582_);
lean_dec(v___x_568_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v_l_559_);
lean_ctor_set(v___x_533_, 0, v___x_583_);
v___x_585_ = v___x_533_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_l_530_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_l_559_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_nat_add(v___x_538_, v_size_561_);
if (lean_obj_tag(v_r_560_) == 0)
{
lean_object* v_size_587_; 
v_size_587_ = lean_ctor_get(v_r_560_, 0);
lean_inc(v_size_587_);
v___y_571_ = v___x_585_;
v___y_572_ = v___x_586_;
v___y_573_ = v_size_587_;
goto v___jp_570_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___y_571_ = v___x_585_;
v___y_572_ = v___x_586_;
v___y_573_ = v___x_588_;
goto v___jp_570_;
}
}
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
lean_del_object(v___x_533_);
v___x_598_ = lean_nat_add(v___x_538_, v_size_539_);
v___x_599_ = lean_nat_add(v___x_598_, v_size_540_);
lean_dec(v_size_540_);
v___x_600_ = lean_nat_add(v___x_598_, v_size_556_);
lean_dec(v___x_598_);
lean_inc_ref(v_l_530_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 4, v_l_543_);
lean_ctor_set(v___x_554_, 3, v_l_530_);
lean_ctor_set(v___x_554_, 2, v_v_529_);
lean_ctor_set(v___x_554_, 1, v_k_528_);
lean_ctor_set(v___x_554_, 0, v___x_600_);
v___x_602_ = v___x_554_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_l_530_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_l_543_);
v___x_602_ = v_reuseFailAlloc_615_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_isSharedCheck_609_ = !lean_is_exclusive(v_l_530_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; lean_object* v_unused_611_; lean_object* v_unused_612_; lean_object* v_unused_613_; lean_object* v_unused_614_; 
v_unused_610_ = lean_ctor_get(v_l_530_, 4);
lean_dec(v_unused_610_);
v_unused_611_ = lean_ctor_get(v_l_530_, 3);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v_l_530_, 2);
lean_dec(v_unused_612_);
v_unused_613_ = lean_ctor_get(v_l_530_, 1);
lean_dec(v_unused_613_);
v_unused_614_ = lean_ctor_get(v_l_530_, 0);
lean_dec(v_unused_614_);
v___x_604_ = v_l_530_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_dec(v_l_530_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 4, v_r_544_);
lean_ctor_set(v___x_604_, 3, v___x_602_);
lean_ctor_set(v___x_604_, 2, v_v_542_);
lean_ctor_set(v___x_604_, 1, v_k_541_);
lean_ctor_set(v___x_604_, 0, v___x_599_);
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_k_541_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_v_542_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_r_544_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_622_; 
v_l_622_ = lean_ctor_get(v_impl_537_, 3);
lean_inc(v_l_622_);
if (lean_obj_tag(v_l_622_) == 0)
{
lean_object* v_r_623_; lean_object* v_k_624_; lean_object* v_v_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_648_; 
v_r_623_ = lean_ctor_get(v_impl_537_, 4);
v_k_624_ = lean_ctor_get(v_impl_537_, 1);
v_v_625_ = lean_ctor_get(v_impl_537_, 2);
v_isSharedCheck_648_ = !lean_is_exclusive(v_impl_537_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; lean_object* v_unused_650_; 
v_unused_649_ = lean_ctor_get(v_impl_537_, 3);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v_impl_537_, 0);
lean_dec(v_unused_650_);
v___x_627_ = v_impl_537_;
v_isShared_628_ = v_isSharedCheck_648_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_r_623_);
lean_inc(v_v_625_);
lean_inc(v_k_624_);
lean_dec(v_impl_537_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_648_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_k_629_; lean_object* v_v_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_644_; 
v_k_629_ = lean_ctor_get(v_l_622_, 1);
v_v_630_ = lean_ctor_get(v_l_622_, 2);
v_isSharedCheck_644_ = !lean_is_exclusive(v_l_622_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; lean_object* v_unused_646_; lean_object* v_unused_647_; 
v_unused_645_ = lean_ctor_get(v_l_622_, 4);
lean_dec(v_unused_645_);
v_unused_646_ = lean_ctor_get(v_l_622_, 3);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_l_622_, 0);
lean_dec(v_unused_647_);
v___x_632_ = v_l_622_;
v_isShared_633_ = v_isSharedCheck_644_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_v_630_);
lean_inc(v_k_629_);
lean_dec(v_l_622_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_644_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_623_, 2);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v_r_623_);
lean_ctor_set(v___x_632_, 3, v_r_623_);
lean_ctor_set(v___x_632_, 2, v_v_529_);
lean_ctor_set(v___x_632_, 1, v_k_528_);
lean_ctor_set(v___x_632_, 0, v___x_538_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_643_, 3, v_r_623_);
lean_ctor_set(v_reuseFailAlloc_643_, 4, v_r_623_);
v___x_636_ = v_reuseFailAlloc_643_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
lean_inc(v_r_623_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 3, v_r_623_);
lean_ctor_set(v___x_627_, 0, v___x_538_);
v___x_638_ = v___x_627_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_k_624_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_v_625_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_r_623_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v_r_623_);
v___x_638_ = v_reuseFailAlloc_642_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v___x_638_);
lean_ctor_set(v___x_533_, 3, v___x_636_);
lean_ctor_set(v___x_533_, 2, v_v_630_);
lean_ctor_set(v___x_533_, 1, v_k_629_);
lean_ctor_set(v___x_533_, 0, v___x_634_);
v___x_640_ = v___x_533_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
}
else
{
lean_object* v_r_651_; 
v_r_651_ = lean_ctor_get(v_impl_537_, 4);
lean_inc(v_r_651_);
if (lean_obj_tag(v_r_651_) == 0)
{
lean_object* v_k_652_; lean_object* v_v_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_664_; 
v_k_652_ = lean_ctor_get(v_impl_537_, 1);
v_v_653_ = lean_ctor_get(v_impl_537_, 2);
v_isSharedCheck_664_ = !lean_is_exclusive(v_impl_537_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; lean_object* v_unused_666_; lean_object* v_unused_667_; 
v_unused_665_ = lean_ctor_get(v_impl_537_, 4);
lean_dec(v_unused_665_);
v_unused_666_ = lean_ctor_get(v_impl_537_, 3);
lean_dec(v_unused_666_);
v_unused_667_ = lean_ctor_get(v_impl_537_, 0);
lean_dec(v_unused_667_);
v___x_655_ = v_impl_537_;
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_v_653_);
lean_inc(v_k_652_);
lean_dec(v_impl_537_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = lean_unsigned_to_nat(3u);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 4, v_l_622_);
lean_ctor_set(v___x_655_, 2, v_v_529_);
lean_ctor_set(v___x_655_, 1, v_k_528_);
lean_ctor_set(v___x_655_, 0, v___x_538_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_663_, 3, v_l_622_);
lean_ctor_set(v_reuseFailAlloc_663_, 4, v_l_622_);
v___x_659_ = v_reuseFailAlloc_663_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v_r_651_);
lean_ctor_set(v___x_533_, 3, v___x_659_);
lean_ctor_set(v___x_533_, 2, v_v_653_);
lean_ctor_set(v___x_533_, 1, v_k_652_);
lean_ctor_set(v___x_533_, 0, v___x_657_);
v___x_661_ = v___x_533_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_k_652_);
lean_ctor_set(v_reuseFailAlloc_662_, 2, v_v_653_);
lean_ctor_set(v_reuseFailAlloc_662_, 3, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_662_, 4, v_r_651_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = lean_unsigned_to_nat(2u);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v_impl_537_);
lean_ctor_set(v___x_533_, 3, v_r_651_);
lean_ctor_set(v___x_533_, 0, v___x_668_);
v___x_670_ = v___x_533_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_r_651_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_impl_537_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
else
{
lean_object* v___x_673_; 
lean_dec(v_v_529_);
lean_dec(v_k_528_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 2, v_v_525_);
lean_ctor_set(v___x_533_, 1, v_k_524_);
v___x_673_ = v___x_533_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_size_527_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_k_524_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_v_525_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_l_530_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_r_531_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v_impl_675_; lean_object* v___x_676_; 
lean_dec(v_size_527_);
v_impl_675_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_524_, v_v_525_, v_l_530_);
v___x_676_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_531_) == 0)
{
lean_object* v_size_677_; lean_object* v_size_678_; lean_object* v_k_679_; lean_object* v_v_680_; lean_object* v_l_681_; lean_object* v_r_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_size_677_ = lean_ctor_get(v_r_531_, 0);
v_size_678_ = lean_ctor_get(v_impl_675_, 0);
lean_inc(v_size_678_);
v_k_679_ = lean_ctor_get(v_impl_675_, 1);
lean_inc(v_k_679_);
v_v_680_ = lean_ctor_get(v_impl_675_, 2);
lean_inc(v_v_680_);
v_l_681_ = lean_ctor_get(v_impl_675_, 3);
lean_inc(v_l_681_);
v_r_682_ = lean_ctor_get(v_impl_675_, 4);
lean_inc(v_r_682_);
v___x_683_ = lean_unsigned_to_nat(3u);
v___x_684_ = lean_nat_mul(v___x_683_, v_size_677_);
v___x_685_ = lean_nat_dec_lt(v___x_684_, v_size_678_);
lean_dec(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
lean_dec(v_r_682_);
lean_dec(v_l_681_);
lean_dec(v_v_680_);
lean_dec(v_k_679_);
v___x_686_ = lean_nat_add(v___x_676_, v_size_678_);
lean_dec(v_size_678_);
v___x_687_ = lean_nat_add(v___x_686_, v_size_677_);
lean_dec(v___x_686_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 3, v_impl_675_);
lean_ctor_set(v___x_533_, 0, v___x_687_);
v___x_689_ = v___x_533_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_690_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_690_, 3, v_impl_675_);
lean_ctor_set(v_reuseFailAlloc_690_, 4, v_r_531_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
else
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_756_; 
v_isSharedCheck_756_ = !lean_is_exclusive(v_impl_675_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; lean_object* v_unused_761_; 
v_unused_757_ = lean_ctor_get(v_impl_675_, 4);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_impl_675_, 3);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_impl_675_, 2);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_impl_675_, 1);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_impl_675_, 0);
lean_dec(v_unused_761_);
v___x_692_ = v_impl_675_;
v_isShared_693_ = v_isSharedCheck_756_;
goto v_resetjp_691_;
}
else
{
lean_dec(v_impl_675_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_756_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_size_694_; lean_object* v_size_695_; lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v_l_698_; lean_object* v_r_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_size_694_ = lean_ctor_get(v_l_681_, 0);
v_size_695_ = lean_ctor_get(v_r_682_, 0);
v_k_696_ = lean_ctor_get(v_r_682_, 1);
v_v_697_ = lean_ctor_get(v_r_682_, 2);
v_l_698_ = lean_ctor_get(v_r_682_, 3);
v_r_699_ = lean_ctor_get(v_r_682_, 4);
v___x_700_ = lean_unsigned_to_nat(2u);
v___x_701_ = lean_nat_mul(v___x_700_, v_size_694_);
v___x_702_ = lean_nat_dec_lt(v_size_695_, v___x_701_);
lean_dec(v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_731_; 
lean_inc(v_r_699_);
lean_inc(v_l_698_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
v_isSharedCheck_731_ = !lean_is_exclusive(v_r_682_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; lean_object* v_unused_733_; lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_732_ = lean_ctor_get(v_r_682_, 4);
lean_dec(v_unused_732_);
v_unused_733_ = lean_ctor_get(v_r_682_, 3);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_r_682_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_r_682_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_r_682_, 0);
lean_dec(v_unused_736_);
v___x_704_ = v_r_682_;
v_isShared_705_ = v_isSharedCheck_731_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_r_682_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_731_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___x_719_; lean_object* v___y_721_; 
v___x_706_ = lean_nat_add(v___x_676_, v_size_678_);
lean_dec(v_size_678_);
v___x_707_ = lean_nat_add(v___x_706_, v_size_677_);
lean_dec(v___x_706_);
v___x_719_ = lean_nat_add(v___x_676_, v_size_694_);
if (lean_obj_tag(v_l_698_) == 0)
{
lean_object* v_size_729_; 
v_size_729_ = lean_ctor_get(v_l_698_, 0);
lean_inc(v_size_729_);
v___y_721_ = v_size_729_;
goto v___jp_720_;
}
else
{
lean_object* v___x_730_; 
v___x_730_ = lean_unsigned_to_nat(0u);
v___y_721_ = v___x_730_;
goto v___jp_720_;
}
v___jp_708_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_nat_add(v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec(v___y_710_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 4, v_r_531_);
lean_ctor_set(v___x_704_, 3, v_r_699_);
lean_ctor_set(v___x_704_, 2, v_v_529_);
lean_ctor_set(v___x_704_, 1, v_k_528_);
lean_ctor_set(v___x_704_, 0, v___x_712_);
v___x_714_ = v___x_704_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v_r_531_);
v___x_714_ = v_reuseFailAlloc_718_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_716_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 4, v___x_714_);
lean_ctor_set(v___x_692_, 3, v___y_709_);
lean_ctor_set(v___x_692_, 2, v_v_697_);
lean_ctor_set(v___x_692_, 1, v_k_696_);
lean_ctor_set(v___x_692_, 0, v___x_707_);
v___x_716_ = v___x_692_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v___y_709_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
v___jp_720_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_nat_add(v___x_719_, v___y_721_);
lean_dec(v___y_721_);
lean_dec(v___x_719_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v_l_698_);
lean_ctor_set(v___x_533_, 3, v_l_681_);
lean_ctor_set(v___x_533_, 2, v_v_680_);
lean_ctor_set(v___x_533_, 1, v_k_679_);
lean_ctor_set(v___x_533_, 0, v___x_722_);
v___x_724_ = v___x_533_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_k_679_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_v_680_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_l_681_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v_l_698_);
v___x_724_ = v_reuseFailAlloc_728_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; 
v___x_725_ = lean_nat_add(v___x_676_, v_size_677_);
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_size_726_; 
v_size_726_ = lean_ctor_get(v_r_699_, 0);
lean_inc(v_size_726_);
v___y_709_ = v___x_724_;
v___y_710_ = v___x_725_;
v___y_711_ = v_size_726_;
goto v___jp_708_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___y_709_ = v___x_724_;
v___y_710_ = v___x_725_;
v___y_711_ = v___x_727_;
goto v___jp_708_;
}
}
}
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
lean_del_object(v___x_533_);
v___x_737_ = lean_nat_add(v___x_676_, v_size_678_);
lean_dec(v_size_678_);
v___x_738_ = lean_nat_add(v___x_737_, v_size_677_);
lean_dec(v___x_737_);
v___x_739_ = lean_nat_add(v___x_676_, v_size_677_);
v___x_740_ = lean_nat_add(v___x_739_, v_size_695_);
lean_dec(v___x_739_);
lean_inc_ref(v_r_531_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 4, v_r_531_);
lean_ctor_set(v___x_692_, 3, v_r_682_);
lean_ctor_set(v___x_692_, 2, v_v_529_);
lean_ctor_set(v___x_692_, 1, v_k_528_);
lean_ctor_set(v___x_692_, 0, v___x_740_);
v___x_742_ = v___x_692_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_r_682_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_r_531_);
v___x_742_ = v_reuseFailAlloc_755_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
v_isSharedCheck_749_ = !lean_is_exclusive(v_r_531_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_750_ = lean_ctor_get(v_r_531_, 4);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_r_531_, 3);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_r_531_, 2);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_r_531_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_r_531_, 0);
lean_dec(v_unused_754_);
v___x_744_ = v_r_531_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_dec(v_r_531_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 4, v___x_742_);
lean_ctor_set(v___x_744_, 3, v_l_681_);
lean_ctor_set(v___x_744_, 2, v_v_680_);
lean_ctor_set(v___x_744_, 1, v_k_679_);
lean_ctor_set(v___x_744_, 0, v___x_738_);
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_k_679_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_v_680_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_l_681_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v___x_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_762_; 
v_l_762_ = lean_ctor_get(v_impl_675_, 3);
lean_inc(v_l_762_);
if (lean_obj_tag(v_l_762_) == 0)
{
lean_object* v_r_763_; lean_object* v_k_764_; lean_object* v_v_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_776_; 
v_r_763_ = lean_ctor_get(v_impl_675_, 4);
v_k_764_ = lean_ctor_get(v_impl_675_, 1);
v_v_765_ = lean_ctor_get(v_impl_675_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_impl_675_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; lean_object* v_unused_778_; 
v_unused_777_ = lean_ctor_get(v_impl_675_, 3);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_impl_675_, 0);
lean_dec(v_unused_778_);
v___x_767_ = v_impl_675_;
v_isShared_768_ = v_isSharedCheck_776_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_r_763_);
lean_inc(v_v_765_);
lean_inc(v_k_764_);
lean_dec(v_impl_675_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_776_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_763_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 3, v_r_763_);
lean_ctor_set(v___x_767_, 2, v_v_529_);
lean_ctor_set(v___x_767_, 1, v_k_528_);
lean_ctor_set(v___x_767_, 0, v___x_676_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_r_763_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_r_763_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v___x_771_);
lean_ctor_set(v___x_533_, 3, v_l_762_);
lean_ctor_set(v___x_533_, 2, v_v_765_);
lean_ctor_set(v___x_533_, 1, v_k_764_);
lean_ctor_set(v___x_533_, 0, v___x_769_);
v___x_773_ = v___x_533_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_k_764_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_v_765_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_l_762_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_r_779_; 
v_r_779_ = lean_ctor_get(v_impl_675_, 4);
lean_inc(v_r_779_);
if (lean_obj_tag(v_r_779_) == 0)
{
lean_object* v_k_780_; lean_object* v_v_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_804_; 
v_k_780_ = lean_ctor_get(v_impl_675_, 1);
v_v_781_ = lean_ctor_get(v_impl_675_, 2);
v_isSharedCheck_804_ = !lean_is_exclusive(v_impl_675_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; lean_object* v_unused_806_; lean_object* v_unused_807_; 
v_unused_805_ = lean_ctor_get(v_impl_675_, 4);
lean_dec(v_unused_805_);
v_unused_806_ = lean_ctor_get(v_impl_675_, 3);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_impl_675_, 0);
lean_dec(v_unused_807_);
v___x_783_ = v_impl_675_;
v_isShared_784_ = v_isSharedCheck_804_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_v_781_);
lean_inc(v_k_780_);
lean_dec(v_impl_675_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_804_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v_k_785_; lean_object* v_v_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_800_; 
v_k_785_ = lean_ctor_get(v_r_779_, 1);
v_v_786_ = lean_ctor_get(v_r_779_, 2);
v_isSharedCheck_800_ = !lean_is_exclusive(v_r_779_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; lean_object* v_unused_803_; 
v_unused_801_ = lean_ctor_get(v_r_779_, 4);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_r_779_, 3);
lean_dec(v_unused_802_);
v_unused_803_ = lean_ctor_get(v_r_779_, 0);
lean_dec(v_unused_803_);
v___x_788_ = v_r_779_;
v_isShared_789_ = v_isSharedCheck_800_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_v_786_);
lean_inc(v_k_785_);
lean_dec(v_r_779_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_800_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_unsigned_to_nat(3u);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 4, v_l_762_);
lean_ctor_set(v___x_788_, 3, v_l_762_);
lean_ctor_set(v___x_788_, 2, v_v_781_);
lean_ctor_set(v___x_788_, 1, v_k_780_);
lean_ctor_set(v___x_788_, 0, v___x_676_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_k_780_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_v_781_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_l_762_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_l_762_);
v___x_792_ = v_reuseFailAlloc_799_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 4, v_l_762_);
lean_ctor_set(v___x_783_, 2, v_v_529_);
lean_ctor_set(v___x_783_, 1, v_k_528_);
lean_ctor_set(v___x_783_, 0, v___x_676_);
v___x_794_ = v___x_783_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_l_762_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_l_762_);
v___x_794_ = v_reuseFailAlloc_798_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v___x_794_);
lean_ctor_set(v___x_533_, 3, v___x_792_);
lean_ctor_set(v___x_533_, 2, v_v_786_);
lean_ctor_set(v___x_533_, 1, v_k_785_);
lean_ctor_set(v___x_533_, 0, v___x_790_);
v___x_796_ = v___x_533_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_k_785_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_v_786_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_unsigned_to_nat(2u);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 4, v_r_779_);
lean_ctor_set(v___x_533_, 3, v_impl_675_);
lean_ctor_set(v___x_533_, 0, v___x_808_);
v___x_810_ = v___x_533_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_k_528_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_v_529_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v_impl_675_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v_r_779_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_k_524_);
lean_ctor_set(v___x_814_, 2, v_v_525_);
lean_ctor_set(v___x_814_, 3, v_t_526_);
lean_ctor_set(v___x_814_, 4, v_t_526_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_producers_818_; lean_object* v_waiters_819_; lean_object* v_capacity_820_; lean_object* v_size_821_; lean_object* v_buffer_822_; lean_object* v_write_823_; lean_object* v_read_824_; lean_object* v_receivers_825_; lean_object* v_nextId_826_; uint8_t v_closed_827_; lean_object* v_pos_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_840_; 
v___x_817_ = lean_st_ref_take(v___y_815_);
v_producers_818_ = lean_ctor_get(v___x_817_, 0);
v_waiters_819_ = lean_ctor_get(v___x_817_, 1);
v_capacity_820_ = lean_ctor_get(v___x_817_, 2);
v_size_821_ = lean_ctor_get(v___x_817_, 3);
v_buffer_822_ = lean_ctor_get(v___x_817_, 4);
v_write_823_ = lean_ctor_get(v___x_817_, 5);
v_read_824_ = lean_ctor_get(v___x_817_, 6);
v_receivers_825_ = lean_ctor_get(v___x_817_, 7);
v_nextId_826_ = lean_ctor_get(v___x_817_, 8);
v_closed_827_ = lean_ctor_get_uint8(v___x_817_, sizeof(void*)*10);
v_pos_828_ = lean_ctor_get(v___x_817_, 9);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_840_ == 0)
{
v___x_830_ = v___x_817_;
v_isShared_831_ = v_isSharedCheck_840_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_pos_828_);
lean_inc(v_nextId_826_);
lean_inc(v_receivers_825_);
lean_inc(v_read_824_);
lean_inc(v_write_823_);
lean_inc(v_buffer_822_);
lean_inc(v_size_821_);
lean_inc(v_capacity_820_);
lean_inc(v_waiters_819_);
lean_inc(v_producers_818_);
lean_dec(v___x_817_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_840_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
lean_inc(v_pos_828_);
lean_inc(v_nextId_826_);
v___x_832_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_nextId_826_, v_pos_828_, v_receivers_825_);
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v_nextId_826_, v___x_833_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 8, v___x_834_);
lean_ctor_set(v___x_830_, 7, v___x_832_);
v___x_836_ = v___x_830_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_producers_818_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_waiters_819_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_capacity_820_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_size_821_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_buffer_822_);
lean_ctor_set(v_reuseFailAlloc_839_, 5, v_write_823_);
lean_ctor_set(v_reuseFailAlloc_839_, 6, v_read_824_);
lean_ctor_set(v_reuseFailAlloc_839_, 7, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_839_, 8, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_839_, 9, v_pos_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_839_, sizeof(void*)*10, v_closed_827_);
v___x_836_ = v_reuseFailAlloc_839_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_st_ref_put(v___y_815_, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v_nextId_826_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0___boxed(lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(v___y_841_);
lean_dec(v___y_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(lean_object* v_bd_845_){
_start:
{
lean_object* v___f_847_; lean_object* v___x_848_; 
v___f_847_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___closed__0));
lean_inc_ref(v_bd_845_);
v___x_848_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_bd_845_, v___f_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_857_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_857_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v_bd_845_);
lean_ctor_set(v___x_853_, 1, v_a_849_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v_bd_845_);
v_a_858_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_848_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_848_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___boxed(lean_object* v_bd_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(lean_object* v_00_u03b1_869_, lean_object* v_bd_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___boxed(lean_object* v_00_u03b1_873_, lean_object* v_bd_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(v_00_u03b1_873_, v_bd_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0(lean_object* v_00_u03b2_877_, lean_object* v_k_878_, lean_object* v_v_879_, lean_object* v_t_880_, lean_object* v_hl_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_878_, v_v_879_, v_t_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(lean_object* v_toApplicative_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_size_885_; lean_object* v_toPure_886_; lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_size_885_ = lean_ctor_get(v_a_884_, 3);
v_toPure_886_ = lean_ctor_get(v_toApplicative_883_, 1);
lean_inc(v_toPure_886_);
lean_dec_ref(v_toApplicative_883_);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_nat_dec_eq(v_size_885_, v___x_887_);
v___x_889_ = lean_box(v___x_888_);
v___x_890_ = lean_apply_2(v_toPure_886_, lean_box(0), v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed(lean_object* v_toApplicative_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(v_toApplicative_891_, v_a_892_);
lean_dec_ref(v_a_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_toApplicative_897_; lean_object* v_toBind_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_toApplicative_897_ = lean_ctor_get(v_inst_894_, 0);
lean_inc_ref(v_toApplicative_897_);
v_toBind_898_ = lean_ctor_get(v_inst_894_, 1);
lean_inc(v_toBind_898_);
lean_dec_ref(v_inst_894_);
v___f_899_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_899_, 0, v_toApplicative_897_);
lean_inc(v_a_896_);
v___x_900_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_900_, 0, lean_box(0));
lean_closure_set(v___x_900_, 1, lean_box(0));
lean_closure_set(v___x_900_, 2, v_a_896_);
v___x_901_ = lean_apply_2(v_inst_895_, lean_box(0), v___x_900_);
v___x_902_ = lean_apply_4(v_toBind_898_, lean_box(0), lean_box(0), v___x_901_, v___f_899_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___boxed(lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_903_, v_inst_904_, v_a_905_);
lean_dec(v_a_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(lean_object* v_m_907_, lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_909_, v_inst_910_, v_a_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___boxed(lean_object* v_m_913_, lean_object* v_00_u03b1_914_, lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(v_m_913_, v_00_u03b1_914_, v_inst_915_, v_inst_916_, v_a_917_);
lean_dec(v_a_917_);
return v_res_918_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(lean_object* v_a_919_){
_start:
{
lean_object* v___x_921_; lean_object* v_capacity_922_; lean_object* v_size_923_; uint8_t v___x_924_; 
v___x_921_ = lean_st_ref_get(v_a_919_);
v_capacity_922_ = lean_ctor_get(v___x_921_, 2);
lean_inc(v_capacity_922_);
v_size_923_ = lean_ctor_get(v___x_921_, 3);
lean_inc(v_size_923_);
lean_dec(v___x_921_);
v___x_924_ = lean_nat_dec_le(v_capacity_922_, v_size_923_);
lean_dec(v_size_923_);
lean_dec(v_capacity_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg___boxed(lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
uint8_t v_res_927_; lean_object* v_r_928_; 
v_res_927_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_925_);
lean_dec(v_a_925_);
v_r_928_ = lean_box(v_res_927_);
return v_r_928_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(lean_object* v_00_u03b1_929_, lean_object* v_a_930_){
_start:
{
uint8_t v___x_932_; 
v___x_932_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___boxed(lean_object* v_00_u03b1_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(v_00_u03b1_933_, v_a_934_);
lean_dec(v_a_934_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(lean_object* v_value_938_, lean_object* v_st_939_){
_start:
{
lean_object* v_producers_941_; lean_object* v_waiters_942_; lean_object* v_capacity_943_; lean_object* v_size_944_; lean_object* v_buffer_945_; lean_object* v_write_946_; lean_object* v_read_947_; lean_object* v_receivers_948_; lean_object* v_nextId_949_; uint8_t v_closed_950_; lean_object* v_pos_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_971_; 
v_producers_941_ = lean_ctor_get(v_st_939_, 0);
v_waiters_942_ = lean_ctor_get(v_st_939_, 1);
v_capacity_943_ = lean_ctor_get(v_st_939_, 2);
v_size_944_ = lean_ctor_get(v_st_939_, 3);
v_buffer_945_ = lean_ctor_get(v_st_939_, 4);
v_write_946_ = lean_ctor_get(v_st_939_, 5);
v_read_947_ = lean_ctor_get(v_st_939_, 6);
v_receivers_948_ = lean_ctor_get(v_st_939_, 7);
v_nextId_949_ = lean_ctor_get(v_st_939_, 8);
v_closed_950_ = lean_ctor_get_uint8(v_st_939_, sizeof(void*)*10);
v_pos_951_ = lean_ctor_get(v_st_939_, 9);
v_isSharedCheck_971_ = !lean_is_exclusive(v_st_939_);
if (v_isSharedCheck_971_ == 0)
{
v___x_953_ = v_st_939_;
v_isShared_954_ = v_isSharedCheck_971_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_pos_951_);
lean_inc(v_nextId_949_);
lean_inc(v_receivers_948_);
lean_inc(v_read_947_);
lean_inc(v_write_946_);
lean_inc(v_buffer_945_);
lean_inc(v_size_944_);
lean_inc(v_capacity_943_);
lean_inc(v_waiters_942_);
lean_inc(v_producers_941_);
lean_dec(v_st_939_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_971_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_tailRef_955_; lean_object* v___x_956_; lean_object* v___y_958_; 
v_tailRef_955_ = lean_array_fget_borrowed(v_buffer_945_, v_write_946_);
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_value_938_);
if (lean_obj_tag(v_receivers_948_) == 0)
{
lean_object* v_size_969_; 
v_size_969_ = lean_ctor_get(v_receivers_948_, 0);
lean_inc(v_size_969_);
v___y_958_ = v_size_969_;
goto v___jp_957_;
}
else
{
lean_object* v___x_970_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v___y_958_ = v___x_970_;
goto v___jp_957_;
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
lean_inc(v_pos_951_);
v___x_959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_959_, 0, v___x_956_);
lean_ctor_set(v___x_959_, 1, v_pos_951_);
lean_ctor_set(v___x_959_, 2, v___y_958_);
v___x_960_ = lean_st_ref_swap(v_tailRef_955_, v___x_959_);
lean_dec(v___x_960_);
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_add(v_write_946_, v___x_961_);
lean_dec(v_write_946_);
v___x_963_ = lean_nat_mod(v___x_962_, v_capacity_943_);
lean_dec(v___x_962_);
v___x_964_ = lean_nat_add(v_size_944_, v___x_961_);
lean_dec(v_size_944_);
v___x_965_ = lean_nat_add(v_pos_951_, v___x_961_);
lean_dec(v_pos_951_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 9, v___x_965_);
lean_ctor_set(v___x_953_, 5, v___x_963_);
lean_ctor_set(v___x_953_, 3, v___x_964_);
v___x_967_ = v___x_953_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_producers_941_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_waiters_942_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_capacity_943_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_968_, 4, v_buffer_945_);
lean_ctor_set(v_reuseFailAlloc_968_, 5, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_968_, 6, v_read_947_);
lean_ctor_set(v_reuseFailAlloc_968_, 7, v_receivers_948_);
lean_ctor_set(v_reuseFailAlloc_968_, 8, v_nextId_949_);
lean_ctor_set(v_reuseFailAlloc_968_, 9, v___x_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*10, v_closed_950_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg___boxed(lean_object* v_value_972_, lean_object* v_st_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_972_, v_st_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(lean_object* v_00_u03b1_976_, lean_object* v_value_977_, lean_object* v_st_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_977_, v_st_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___boxed(lean_object* v_00_u03b1_981_, lean_object* v_value_982_, lean_object* v_st_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(v_00_u03b1_981_, v_value_982_, v_st_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(lean_object* v_st_986_){
_start:
{
lean_object* v_producers_987_; lean_object* v_waiters_988_; lean_object* v_capacity_989_; lean_object* v_size_990_; lean_object* v_buffer_991_; lean_object* v_write_992_; lean_object* v_read_993_; lean_object* v_receivers_994_; lean_object* v_nextId_995_; uint8_t v_closed_996_; lean_object* v_pos_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1008_; 
v_producers_987_ = lean_ctor_get(v_st_986_, 0);
v_waiters_988_ = lean_ctor_get(v_st_986_, 1);
v_capacity_989_ = lean_ctor_get(v_st_986_, 2);
v_size_990_ = lean_ctor_get(v_st_986_, 3);
v_buffer_991_ = lean_ctor_get(v_st_986_, 4);
v_write_992_ = lean_ctor_get(v_st_986_, 5);
v_read_993_ = lean_ctor_get(v_st_986_, 6);
v_receivers_994_ = lean_ctor_get(v_st_986_, 7);
v_nextId_995_ = lean_ctor_get(v_st_986_, 8);
v_closed_996_ = lean_ctor_get_uint8(v_st_986_, sizeof(void*)*10);
v_pos_997_ = lean_ctor_get(v_st_986_, 9);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_st_986_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_999_ = v_st_986_;
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_pos_997_);
lean_inc(v_nextId_995_);
lean_inc(v_receivers_994_);
lean_inc(v_read_993_);
lean_inc(v_write_992_);
lean_inc(v_buffer_991_);
lean_inc(v_size_990_);
lean_inc(v_capacity_989_);
lean_inc(v_waiters_988_);
lean_inc(v_producers_987_);
lean_dec(v_st_986_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1008_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v_size_1002_; lean_object* v___x_1003_; lean_object* v_read_1004_; lean_object* v___x_1006_; 
v___x_1001_ = lean_unsigned_to_nat(1u);
v_size_1002_ = lean_nat_sub(v_size_990_, v___x_1001_);
lean_dec(v_size_990_);
v___x_1003_ = lean_nat_add(v_read_993_, v___x_1001_);
lean_dec(v_read_993_);
v_read_1004_ = lean_nat_mod(v___x_1003_, v_capacity_989_);
lean_dec(v___x_1003_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 6, v_read_1004_);
lean_ctor_set(v___x_999_, 3, v_size_1002_);
v___x_1006_ = v___x_999_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_producers_987_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_waiters_988_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_capacity_989_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_size_1002_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_buffer_991_);
lean_ctor_set(v_reuseFailAlloc_1007_, 5, v_write_992_);
lean_ctor_set(v_reuseFailAlloc_1007_, 6, v_read_1004_);
lean_ctor_set(v_reuseFailAlloc_1007_, 7, v_receivers_994_);
lean_ctor_set(v_reuseFailAlloc_1007_, 8, v_nextId_995_);
lean_ctor_set(v_reuseFailAlloc_1007_, 9, v_pos_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1007_, sizeof(void*)*10, v_closed_996_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue(lean_object* v_00_u03b1_1009_, lean_object* v_st_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_st_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(lean_object* v_toApplicative_1012_, lean_object* v_place_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_capacity_1015_; lean_object* v_buffer_1016_; lean_object* v_toPure_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_capacity_1015_ = lean_ctor_get(v_a_1014_, 2);
v_buffer_1016_ = lean_ctor_get(v_a_1014_, 4);
v_toPure_1017_ = lean_ctor_get(v_toApplicative_1012_, 1);
lean_inc(v_toPure_1017_);
lean_dec_ref(v_toApplicative_1012_);
v___x_1018_ = lean_nat_mod(v_place_1013_, v_capacity_1015_);
v___x_1019_ = lean_array_fget_borrowed(v_buffer_1016_, v___x_1018_);
lean_dec(v___x_1018_);
lean_inc(v___x_1019_);
v___x_1020_ = lean_apply_2(v_toPure_1017_, lean_box(0), v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed(lean_object* v_toApplicative_1021_, lean_object* v_place_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(v_toApplicative_1021_, v_place_1022_, v_a_1023_);
lean_dec_ref(v_a_1023_);
lean_dec(v_place_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_place_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_toApplicative_1029_; lean_object* v_toBind_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_toApplicative_1029_ = lean_ctor_get(v_inst_1025_, 0);
lean_inc_ref(v_toApplicative_1029_);
v_toBind_1030_ = lean_ctor_get(v_inst_1025_, 1);
lean_inc(v_toBind_1030_);
lean_dec_ref(v_inst_1025_);
v___f_1031_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1031_, 0, v_toApplicative_1029_);
lean_closure_set(v___f_1031_, 1, v_place_1027_);
lean_inc(v_a_1028_);
v___x_1032_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1032_, 0, lean_box(0));
lean_closure_set(v___x_1032_, 1, lean_box(0));
lean_closure_set(v___x_1032_, 2, v_a_1028_);
v___x_1033_ = lean_apply_2(v_inst_1026_, lean_box(0), v___x_1032_);
v___x_1034_ = lean_apply_4(v_toBind_1030_, lean_box(0), lean_box(0), v___x_1033_, v___f_1031_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___boxed(lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_place_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1035_, v_inst_1036_, v_place_1037_, v_a_1038_);
lean_dec(v_a_1038_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(lean_object* v_m_1040_, lean_object* v_00_u03b1_1041_, lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_place_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1042_, v_inst_1043_, v_place_1044_, v_a_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___boxed(lean_object* v_m_1047_, lean_object* v_00_u03b1_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_place_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(v_m_1047_, v_00_u03b1_1048_, v_inst_1049_, v_inst_1050_, v_place_1051_, v_a_1052_);
lean_dec(v_a_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(lean_object* v_as_1054_, size_t v_sz_1055_, size_t v_i_1056_, lean_object* v_b_1057_){
_start:
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_usize_dec_lt(v_i_1056_, v_sz_1055_);
if (v___x_1059_ == 0)
{
return v_b_1057_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; 
v_a_1060_ = lean_array_uget_borrowed(v_as_1054_, v_i_1056_);
v___x_1061_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1060_, v___x_1059_);
v___x_1062_ = lean_box(0);
v___x_1063_ = ((size_t)1ULL);
v___x_1064_ = lean_usize_add(v_i_1056_, v___x_1063_);
v_i_1056_ = v___x_1064_;
v_b_1057_ = v___x_1062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg___boxed(lean_object* v_as_1066_, lean_object* v_sz_1067_, lean_object* v_i_1068_, lean_object* v_b_1069_, lean_object* v___y_1070_){
_start:
{
size_t v_sz_boxed_1071_; size_t v_i_boxed_1072_; lean_object* v_res_1073_; 
v_sz_boxed_1071_ = lean_unbox_usize(v_sz_1067_);
lean_dec(v_sz_1067_);
v_i_boxed_1072_ = lean_unbox_usize(v_i_1068_);
lean_dec(v_i_1068_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1066_, v_sz_boxed_1071_, v_i_boxed_1072_, v_b_1069_);
lean_dec_ref(v_as_1066_);
return v_res_1073_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_Queue_empty(lean_box(0));
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(lean_object* v_v_1075_, lean_object* v_a_1076_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_producers_1081_; lean_object* v_waiters_1082_; lean_object* v_capacity_1083_; lean_object* v_size_1084_; lean_object* v_buffer_1085_; lean_object* v_write_1086_; lean_object* v_read_1087_; lean_object* v_receivers_1088_; lean_object* v_nextId_1089_; uint8_t v_closed_1090_; lean_object* v_pos_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1110_; 
v___x_1079_ = lean_st_ref_get(v_a_1076_);
v___x_1080_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_v_1075_, v___x_1079_);
v_producers_1081_ = lean_ctor_get(v___x_1080_, 0);
v_waiters_1082_ = lean_ctor_get(v___x_1080_, 1);
v_capacity_1083_ = lean_ctor_get(v___x_1080_, 2);
v_size_1084_ = lean_ctor_get(v___x_1080_, 3);
v_buffer_1085_ = lean_ctor_get(v___x_1080_, 4);
v_write_1086_ = lean_ctor_get(v___x_1080_, 5);
v_read_1087_ = lean_ctor_get(v___x_1080_, 6);
v_receivers_1088_ = lean_ctor_get(v___x_1080_, 7);
v_nextId_1089_ = lean_ctor_get(v___x_1080_, 8);
v_closed_1090_ = lean_ctor_get_uint8(v___x_1080_, sizeof(void*)*10);
v_pos_1091_ = lean_ctor_get(v___x_1080_, 9);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1093_ = v___x_1080_;
v_isShared_1094_ = v_isSharedCheck_1110_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_pos_1091_);
lean_inc(v_nextId_1089_);
lean_inc(v_receivers_1088_);
lean_inc(v_read_1087_);
lean_inc(v_write_1086_);
lean_inc(v_buffer_1085_);
lean_inc(v_size_1084_);
lean_inc(v_capacity_1083_);
lean_inc(v_waiters_1082_);
lean_inc(v_producers_1081_);
lean_dec(v___x_1080_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1110_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0);
lean_inc(v_receivers_1088_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_producers_1081_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_capacity_1083_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_size_1084_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_buffer_1085_);
lean_ctor_set(v_reuseFailAlloc_1109_, 5, v_write_1086_);
lean_ctor_set(v_reuseFailAlloc_1109_, 6, v_read_1087_);
lean_ctor_set(v_reuseFailAlloc_1109_, 7, v_receivers_1088_);
lean_ctor_set(v_reuseFailAlloc_1109_, 8, v_nextId_1089_);
lean_ctor_set(v_reuseFailAlloc_1109_, 9, v_pos_1091_);
lean_ctor_set_uint8(v_reuseFailAlloc_1109_, sizeof(void*)*10, v_closed_1090_);
v___x_1097_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; size_t v_sz_1101_; size_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___y_1105_; 
v___x_1098_ = lean_st_ref_swap(v_a_1076_, v___x_1097_);
lean_dec(v___x_1098_);
v___x_1099_ = l_Std_Queue_toArray___redArg(v_waiters_1082_);
v___x_1100_ = lean_box(0);
v_sz_1101_ = lean_array_size(v___x_1099_);
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v___x_1099_, v_sz_1101_, v___x_1102_, v___x_1100_);
lean_dec_ref(v___x_1099_);
if (lean_obj_tag(v_receivers_1088_) == 0)
{
lean_object* v_size_1107_; 
v_size_1107_ = lean_ctor_get(v_receivers_1088_, 0);
lean_inc(v_size_1107_);
lean_dec_ref_known(v_receivers_1088_, 5);
v___y_1105_ = v_size_1107_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_unsigned_to_nat(0u);
v___y_1105_ = v___x_1108_;
goto v___jp_1104_;
}
v___jp_1104_:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___y_1105_);
return v___x_1106_;
}
}
}
}
else
{
lean_object* v___x_1111_; 
lean_dec(v_v_1075_);
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1112_, v_a_1113_);
lean_dec(v_a_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(lean_object* v_00_u03b1_1116_, lean_object* v_v_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1117_, v_a_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_1121_, lean_object* v_v_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(v_00_u03b1_1121_, v_v_1122_, v_a_1123_);
lean_dec(v_a_1123_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(lean_object* v_00_u03b1_1126_, lean_object* v_as_1127_, size_t v_sz_1128_, size_t v_i_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1127_, v_sz_1128_, v_i_1129_, v_b_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1134_, lean_object* v_as_1135_, lean_object* v_sz_1136_, lean_object* v_i_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
size_t v_sz_boxed_1141_; size_t v_i_boxed_1142_; lean_object* v_res_1143_; 
v_sz_boxed_1141_ = lean_unbox_usize(v_sz_1136_);
lean_dec(v_sz_1136_);
v_i_boxed_1142_ = lean_unbox_usize(v_i_1137_);
lean_dec(v_i_1137_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(v_00_u03b1_1134_, v_as_1135_, v_sz_boxed_1141_, v_i_boxed_1142_, v_b_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v_as_1135_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(lean_object* v_mutex_1144_, lean_object* v_k_1145_){
_start:
{
lean_object* v_ref_1147_; lean_object* v_mutex_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_ref_1147_ = lean_ctor_get(v_mutex_1144_, 0);
lean_inc(v_ref_1147_);
v_mutex_1148_ = lean_ctor_get(v_mutex_1144_, 1);
lean_inc(v_mutex_1148_);
lean_dec_ref(v_mutex_1144_);
v___x_1149_ = lean_io_basemutex_lock(v_mutex_1148_);
v___x_1150_ = lean_apply_2(v_k_1145_, v_ref_1147_, lean_box(0));
v___x_1151_ = lean_io_basemutex_unlock(v_mutex_1148_);
lean_dec(v_mutex_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg___boxed(lean_object* v_mutex_1152_, lean_object* v_k_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1152_, v_k_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(lean_object* v_00_u03b1_1156_, lean_object* v_00_u03b2_1157_, lean_object* v_mutex_1158_, lean_object* v_k_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1158_, v_k_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_mutex_1164_, lean_object* v_k_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(v_00_u03b1_1162_, v_00_u03b2_1163_, v_mutex_1164_, v_k_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(lean_object* v_v_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; uint8_t v_closed_1174_; 
v___x_1173_ = lean_st_ref_get(v___y_1171_);
v_closed_1174_ = lean_ctor_get_uint8(v___x_1173_, sizeof(void*)*10);
lean_dec(v___x_1173_);
if (v_closed_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v_receivers_1176_; 
v___x_1175_ = lean_st_ref_get(v___y_1171_);
v_receivers_1176_ = lean_ctor_get(v___x_1175_, 7);
lean_inc(v_receivers_1176_);
lean_dec(v___x_1175_);
if (lean_obj_tag(v_receivers_1176_) == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref_known(v_receivers_1176_, 5);
v___x_1177_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1170_, v___y_1171_);
return v___x_1177_;
}
else
{
lean_object* v___x_1178_; 
lean_dec(v_v_1170_);
v___x_1178_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0));
return v___x_1178_;
}
}
else
{
lean_object* v___x_1179_; 
lean_dec(v_v_1170_);
v___x_1179_ = lean_box(0);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(v_v_1180_, v___y_1181_);
lean_dec(v___y_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(lean_object* v_ch_1184_, lean_object* v_v_1185_){
_start:
{
lean_object* v___f_1187_; lean_object* v___x_1188_; 
v___f_1187_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1187_, 0, v_v_1185_);
v___x_1188_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1184_, v___f_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___boxed(lean_object* v_ch_1189_, lean_object* v_v_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1189_, v_v_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(lean_object* v_00_u03b1_1193_, lean_object* v_ch_1194_, lean_object* v_v_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1194_, v_v_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_ch_1199_, lean_object* v_v_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(v_00_u03b1_1198_, v_ch_1199_, v_v_1200_);
return v_res_1202_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0));
v___x_1206_ = lean_task_pure(v___x_1205_);
return v___x_1206_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2));
v___x_1211_ = lean_task_pure(v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(lean_object* v_v_1212_, lean_object* v___f_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; uint8_t v_closed_1217_; 
v___x_1216_ = lean_st_ref_get(v___y_1214_);
v_closed_1217_ = lean_ctor_get_uint8(v___x_1216_, sizeof(void*)*10);
lean_dec(v___x_1216_);
if (v_closed_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v_receivers_1219_; 
v___x_1218_ = lean_st_ref_get(v___y_1214_);
v_receivers_1219_ = lean_ctor_get(v___x_1218_, 7);
lean_inc(v_receivers_1219_);
lean_dec(v___x_1218_);
if (lean_obj_tag(v_receivers_1219_) == 0)
{
lean_object* v___x_1220_; 
lean_dec_ref_known(v_receivers_1219_, 5);
v___x_1220_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1212_, v___y_1214_);
if (lean_obj_tag(v___x_1220_) == 1)
{
lean_object* v_val_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v___f_1213_);
v_val_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_val_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_val_1221_);
v___x_1226_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_task_pure(v___x_1226_);
return v___x_1227_;
}
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_producers_1232_; lean_object* v_waiters_1233_; lean_object* v_capacity_1234_; lean_object* v_size_1235_; lean_object* v_buffer_1236_; lean_object* v_write_1237_; lean_object* v_read_1238_; lean_object* v_receivers_1239_; lean_object* v_nextId_1240_; uint8_t v_closed_1241_; lean_object* v_pos_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1254_; 
lean_dec(v___x_1220_);
v___x_1230_ = lean_io_promise_new();
v___x_1231_ = lean_st_ref_take(v___y_1214_);
v_producers_1232_ = lean_ctor_get(v___x_1231_, 0);
v_waiters_1233_ = lean_ctor_get(v___x_1231_, 1);
v_capacity_1234_ = lean_ctor_get(v___x_1231_, 2);
v_size_1235_ = lean_ctor_get(v___x_1231_, 3);
v_buffer_1236_ = lean_ctor_get(v___x_1231_, 4);
v_write_1237_ = lean_ctor_get(v___x_1231_, 5);
v_read_1238_ = lean_ctor_get(v___x_1231_, 6);
v_receivers_1239_ = lean_ctor_get(v___x_1231_, 7);
v_nextId_1240_ = lean_ctor_get(v___x_1231_, 8);
v_closed_1241_ = lean_ctor_get_uint8(v___x_1231_, sizeof(void*)*10);
v_pos_1242_ = lean_ctor_get(v___x_1231_, 9);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1244_ = v___x_1231_;
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_pos_1242_);
lean_inc(v_nextId_1240_);
lean_inc(v_receivers_1239_);
lean_inc(v_read_1238_);
lean_inc(v_write_1237_);
lean_inc(v_buffer_1236_);
lean_inc(v_size_1235_);
lean_inc(v_capacity_1234_);
lean_inc(v_waiters_1233_);
lean_inc(v_producers_1232_);
lean_dec(v___x_1231_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_inc(v___x_1230_);
v___x_1246_ = l_Std_Queue_enqueue___redArg(v___x_1230_, v_producers_1232_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_waiters_1233_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_capacity_1234_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_size_1235_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v_buffer_1236_);
lean_ctor_set(v_reuseFailAlloc_1253_, 5, v_write_1237_);
lean_ctor_set(v_reuseFailAlloc_1253_, 6, v_read_1238_);
lean_ctor_set(v_reuseFailAlloc_1253_, 7, v_receivers_1239_);
lean_ctor_set(v_reuseFailAlloc_1253_, 8, v_nextId_1240_);
lean_ctor_set(v_reuseFailAlloc_1253_, 9, v_pos_1242_);
lean_ctor_set_uint8(v_reuseFailAlloc_1253_, sizeof(void*)*10, v_closed_1241_);
v___x_1248_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1249_ = lean_st_ref_put(v___y_1214_, v___x_1248_);
v___x_1250_ = lean_io_promise_result_opt(v___x_1230_);
lean_dec(v___x_1230_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_io_bind_task(v___x_1250_, v___f_1213_, v___x_1251_, v_closed_1217_);
return v___x_1252_;
}
}
}
}
else
{
lean_object* v___x_1255_; 
lean_dec_ref(v___f_1213_);
lean_dec(v_v_1212_);
v___x_1255_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1);
return v___x_1255_;
}
}
else
{
lean_object* v___x_1256_; 
lean_dec_ref(v___f_1213_);
lean_dec(v_v_1212_);
v___x_1256_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_1257_, lean_object* v___f_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(v_v_1257_, v___f_1258_, v___y_1259_);
lean_dec(v___y_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(lean_object* v_ch_1262_, lean_object* v_v_1263_, lean_object* v_res_1264_){
_start:
{
if (lean_obj_tag(v_res_1264_) == 0)
{
lean_dec(v_v_1263_);
lean_dec_ref(v_ch_1262_);
goto v___jp_1266_;
}
else
{
lean_object* v_val_1268_; uint8_t v___x_1269_; 
v_val_1268_ = lean_ctor_get(v_res_1264_, 0);
v___x_1269_ = lean_unbox(v_val_1268_);
if (v___x_1269_ == 0)
{
lean_dec(v_v_1263_);
lean_dec_ref(v_ch_1262_);
goto v___jp_1266_;
}
else
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1262_, v_v_1263_);
return v___x_1270_;
}
}
v___jp_1266_:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_1271_, lean_object* v_v_1272_, lean_object* v_res_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(v_ch_1271_, v_v_1272_, v_res_1273_);
lean_dec(v_res_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(lean_object* v_ch_1276_, lean_object* v_v_1277_){
_start:
{
lean_object* v___f_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; 
lean_inc(v_v_1277_);
lean_inc_ref(v_ch_1276_);
v___f_1279_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1279_, 0, v_ch_1276_);
lean_closure_set(v___f_1279_, 1, v_v_1277_);
v___f_1280_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1280_, 0, v_v_1277_);
lean_closure_set(v___f_1280_, 1, v___f_1279_);
v___x_1281_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1276_, v___f_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___boxed(lean_object* v_ch_1282_, lean_object* v_v_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1282_, v_v_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send(lean_object* v_00_u03b1_1286_, lean_object* v_ch_1287_, lean_object* v_v_1288_){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1287_, v_v_1288_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___boxed(lean_object* v_00_u03b1_1291_, lean_object* v_ch_1292_, lean_object* v_v_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send(v_00_u03b1_1291_, v_ch_1292_, v_v_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(lean_object* v_mutex_1296_, lean_object* v_k_1297_){
_start:
{
lean_object* v_ref_1299_; lean_object* v_mutex_1300_; lean_object* v___x_1301_; lean_object* v_r_1302_; 
v_ref_1299_ = lean_ctor_get(v_mutex_1296_, 0);
lean_inc(v_ref_1299_);
v_mutex_1300_ = lean_ctor_get(v_mutex_1296_, 1);
lean_inc(v_mutex_1300_);
lean_dec_ref(v_mutex_1296_);
v___x_1301_ = lean_io_basemutex_lock(v_mutex_1300_);
v_r_1302_ = lean_apply_2(v_k_1297_, v_ref_1299_, lean_box(0));
if (lean_obj_tag(v_r_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
v_a_1303_ = lean_ctor_get(v_r_1302_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_r_1302_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1305_ = v_r_1302_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v_r_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_io_basemutex_unlock(v_mutex_1300_);
lean_dec(v_mutex_1300_);
if (v_isShared_1306_ == 0)
{
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1303_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1320_; 
v_a_1312_ = lean_ctor_get(v_r_1302_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_r_1302_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1314_ = v_r_1302_;
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v_r_1302_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_io_basemutex_unlock(v_mutex_1300_);
lean_dec(v_mutex_1300_);
if (v_isShared_1315_ == 0)
{
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1312_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object* v_mutex_1321_, lean_object* v_k_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_mutex_1321_, v_k_1322_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object* v_00_u03b1_1325_, lean_object* v_00_u03b2_1326_, lean_object* v_mutex_1327_, lean_object* v_k_1328_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_mutex_1327_, v_k_1328_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_mutex_1333_, lean_object* v_k_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(v_00_u03b1_1331_, v_00_u03b2_1332_, v_mutex_1333_, v_k_1334_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(uint8_t v___x_1337_, lean_object* v_as_1338_, size_t v_sz_1339_, size_t v_i_1340_, lean_object* v_b_1341_){
_start:
{
uint8_t v___x_1343_; 
v___x_1343_ = lean_usize_dec_lt(v_i_1340_, v_sz_1339_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v_b_1341_);
return v___x_1344_;
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; 
v_a_1345_ = lean_array_uget_borrowed(v_as_1338_, v_i_1340_);
v___x_1346_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1345_, v___x_1337_);
v___x_1347_ = lean_box(0);
v___x_1348_ = ((size_t)1ULL);
v___x_1349_ = lean_usize_add(v_i_1340_, v___x_1348_);
v_i_1340_ = v___x_1349_;
v_b_1341_ = v___x_1347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_1351_, lean_object* v_as_1352_, lean_object* v_sz_1353_, lean_object* v_i_1354_, lean_object* v_b_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v___x_1402__boxed_1357_; size_t v_sz_boxed_1358_; size_t v_i_boxed_1359_; lean_object* v_res_1360_; 
v___x_1402__boxed_1357_ = lean_unbox(v___x_1351_);
v_sz_boxed_1358_ = lean_unbox_usize(v_sz_1353_);
lean_dec(v_sz_1353_);
v_i_boxed_1359_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1402__boxed_1357_, v_as_1352_, v_sz_boxed_1358_, v_i_boxed_1359_, v_b_1355_);
lean_dec_ref(v_as_1352_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; uint8_t v_closed_1364_; 
v___x_1363_ = lean_st_ref_get(v___y_1361_);
v_closed_1364_ = lean_ctor_get_uint8(v___x_1363_, sizeof(void*)*10);
if (v_closed_1364_ == 0)
{
lean_object* v_producers_1365_; lean_object* v_waiters_1366_; lean_object* v_capacity_1367_; lean_object* v_size_1368_; lean_object* v_buffer_1369_; lean_object* v_write_1370_; lean_object* v_read_1371_; lean_object* v_receivers_1372_; lean_object* v_nextId_1373_; lean_object* v_pos_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1397_; 
v_producers_1365_ = lean_ctor_get(v___x_1363_, 0);
v_waiters_1366_ = lean_ctor_get(v___x_1363_, 1);
v_capacity_1367_ = lean_ctor_get(v___x_1363_, 2);
v_size_1368_ = lean_ctor_get(v___x_1363_, 3);
v_buffer_1369_ = lean_ctor_get(v___x_1363_, 4);
v_write_1370_ = lean_ctor_get(v___x_1363_, 5);
v_read_1371_ = lean_ctor_get(v___x_1363_, 6);
v_receivers_1372_ = lean_ctor_get(v___x_1363_, 7);
v_nextId_1373_ = lean_ctor_get(v___x_1363_, 8);
v_pos_1374_ = lean_ctor_get(v___x_1363_, 9);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1376_ = v___x_1363_;
v_isShared_1377_ = v_isSharedCheck_1397_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_pos_1374_);
lean_inc(v_nextId_1373_);
lean_inc(v_receivers_1372_);
lean_inc(v_read_1371_);
lean_inc(v_write_1370_);
lean_inc(v_buffer_1369_);
lean_inc(v_size_1368_);
lean_inc(v_capacity_1367_);
lean_inc(v_waiters_1366_);
lean_inc(v_producers_1365_);
lean_dec(v___x_1363_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1397_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; size_t v_sz_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
v___x_1378_ = l_Std_Queue_toArray___redArg(v_waiters_1366_);
v___x_1379_ = lean_box(0);
v_sz_1380_ = lean_array_size(v___x_1378_);
v___x_1381_ = ((size_t)0ULL);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v_closed_1364_, v___x_1378_, v_sz_1380_, v___x_1381_, v___x_1379_);
lean_dec_ref(v___x_1378_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1395_; 
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; 
v_unused_1396_ = lean_ctor_get(v___x_1382_, 0);
lean_dec(v_unused_1396_);
v___x_1384_ = v___x_1382_;
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
else
{
lean_dec(v___x_1382_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0);
v___x_1387_ = 1;
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 1, v___x_1386_);
v___x_1389_ = v___x_1376_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_producers_1365_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_capacity_1367_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_size_1368_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_buffer_1369_);
lean_ctor_set(v_reuseFailAlloc_1394_, 5, v_write_1370_);
lean_ctor_set(v_reuseFailAlloc_1394_, 6, v_read_1371_);
lean_ctor_set(v_reuseFailAlloc_1394_, 7, v_receivers_1372_);
lean_ctor_set(v_reuseFailAlloc_1394_, 8, v_nextId_1373_);
lean_ctor_set(v_reuseFailAlloc_1394_, 9, v_pos_1374_);
v___x_1389_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*10, v___x_1387_);
v___x_1390_ = lean_st_ref_swap(v___y_1361_, v___x_1389_);
lean_dec(v___x_1390_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1379_);
v___x_1392_ = v___x_1384_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1379_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_del_object(v___x_1376_);
lean_dec(v_pos_1374_);
lean_dec(v_nextId_1373_);
lean_dec(v_receivers_1372_);
lean_dec(v_read_1371_);
lean_dec(v_write_1370_);
lean_dec_ref(v_buffer_1369_);
lean_dec(v_size_1368_);
lean_dec(v_capacity_1367_);
lean_dec_ref(v_producers_1365_);
return v___x_1382_;
}
}
}
else
{
uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec(v___x_1363_);
v___x_1398_ = 1;
v___x_1399_ = lean_box(v___x_1398_);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(v___y_1401_);
lean_dec(v___y_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(lean_object* v_ch_1405_){
_start:
{
lean_object* v___f_1407_; lean_object* v___x_1408_; 
v___f_1407_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0));
v___x_1408_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_ch_1405_, v___f_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___boxed(lean_object* v_ch_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_object* v_00_u03b1_1412_, lean_object* v_ch_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_ch_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close(v_00_u03b1_1416_, v_ch_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_object* v_00_u03b1_1420_, uint8_t v___x_1421_, lean_object* v_as_1422_, size_t v_sz_1423_, size_t v_i_1424_, lean_object* v_b_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1421_, v_as_1422_, v_sz_1423_, v_i_1424_, v_b_1425_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_1429_, lean_object* v___x_1430_, lean_object* v_as_1431_, lean_object* v_sz_1432_, lean_object* v_i_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
uint8_t v___x_1498__boxed_1437_; size_t v_sz_boxed_1438_; size_t v_i_boxed_1439_; lean_object* v_res_1440_; 
v___x_1498__boxed_1437_ = lean_unbox(v___x_1430_);
v_sz_boxed_1438_ = lean_unbox_usize(v_sz_1432_);
lean_dec(v_sz_1432_);
v_i_boxed_1439_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1429_, v___x_1498__boxed_1437_, v_as_1431_, v_sz_boxed_1438_, v_i_boxed_1439_, v_b_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v_as_1431_);
return v_res_1440_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; uint8_t v_closed_1444_; 
v___x_1443_ = lean_st_ref_get(v___y_1441_);
v_closed_1444_ = lean_ctor_get_uint8(v___x_1443_, sizeof(void*)*10);
lean_dec(v___x_1443_);
return v_closed_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(v___y_1445_);
lean_dec(v___y_1445_);
v_r_1448_ = lean_box(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object* v_ch_1450_){
_start:
{
lean_object* v___f_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___f_1452_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0));
v___x_1453_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1450_, v___f_1452_);
v___x_1454_ = lean_unbox(v___x_1453_);
lean_dec(v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___boxed(lean_object* v_ch_1455_, lean_object* v_a_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1455_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_object* v_00_u03b1_1459_, lean_object* v_ch_1460_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___boxed(lean_object* v_00_u03b1_1463_, lean_object* v_ch_1464_, lean_object* v_a_1465_){
_start:
{
uint8_t v_res_1466_; lean_object* v_r_1467_; 
v_res_1466_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(v_00_u03b1_1463_, v_ch_1464_);
v_r_1467_ = lean_box(v_res_1466_);
return v_r_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object* v_next_1468_, lean_object* v_slot_1469_){
_start:
{
lean_object* v_value_1470_; lean_object* v_pos_1471_; lean_object* v_remaining_1472_; uint8_t v___x_1473_; 
v_value_1470_ = lean_ctor_get(v_slot_1469_, 0);
v_pos_1471_ = lean_ctor_get(v_slot_1469_, 1);
v_remaining_1472_ = lean_ctor_get(v_slot_1469_, 2);
v___x_1473_ = lean_nat_dec_eq(v_next_1468_, v_pos_1471_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_box(v___x_1473_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v_slot_1469_);
return v___x_1477_;
}
else
{
lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1498_; 
lean_inc(v_remaining_1472_);
lean_inc(v_pos_1471_);
lean_inc(v_value_1470_);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_slot_1469_);
if (v_isSharedCheck_1498_ == 0)
{
lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; 
v_unused_1499_ = lean_ctor_get(v_slot_1469_, 2);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_slot_1469_, 1);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_slot_1469_, 0);
lean_dec(v_unused_1501_);
v___x_1479_ = v_slot_1469_;
v_isShared_1480_ = v_isSharedCheck_1498_;
goto v_resetjp_1478_;
}
else
{
lean_dec(v_slot_1469_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1498_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_dec_eq(v_remaining_1472_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1483_ = lean_box(v___x_1482_);
lean_inc(v_value_1470_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v_value_1470_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = lean_nat_sub(v_remaining_1472_, v___x_1481_);
lean_dec(v_remaining_1472_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 2, v___x_1485_);
v___x_1487_ = v___x_1479_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_value_1470_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_pos_1471_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1484_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
return v___x_1488_;
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_dec(v_remaining_1472_);
v___x_1490_ = lean_box(v___x_1473_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_value_1470_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_unsigned_to_nat(0u);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 2, v___x_1493_);
lean_ctor_set(v___x_1479_, 0, v___x_1492_);
v___x_1495_ = v___x_1479_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_pos_1471_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1491_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
return v___x_1496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object* v_next_1502_, lean_object* v_slot_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(v_next_1502_, v_slot_1503_);
lean_dec(v_next_1502_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object* v_inst_1505_, lean_object* v_slot_1506_, lean_object* v_next_1507_){
_start:
{
lean_object* v___f_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___f_1508_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1508_, 0, v_next_1507_);
v___x_1509_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1509_, 0, lean_box(0));
lean_closure_set(v___x_1509_, 1, lean_box(0));
lean_closure_set(v___x_1509_, 2, lean_box(0));
lean_closure_set(v___x_1509_, 3, v_slot_1506_);
lean_closure_set(v___x_1509_, 4, v___f_1508_);
v___x_1510_ = lean_apply_2(v_inst_1505_, lean_box(0), v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object* v_m_1511_, lean_object* v_00_u03b1_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_slot_1515_, lean_object* v_next_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1514_, v_slot_1515_, v_next_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object* v_m_1519_, lean_object* v_00_u03b1_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_slot_1523_, lean_object* v_next_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(v_m_1519_, v_00_u03b1_1520_, v_inst_1521_, v_inst_1522_, v_slot_1523_, v_next_1524_, v_a_1525_);
lean_dec(v_a_1525_);
lean_dec_ref(v_inst_1521_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object* v_toApplicative_1527_, lean_object* v_fst_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_toPure_1530_; lean_object* v___x_1531_; 
v_toPure_1530_ = lean_ctor_get(v_toApplicative_1527_, 1);
lean_inc(v_toPure_1530_);
lean_dec_ref(v_toApplicative_1527_);
v___x_1531_ = lean_apply_2(v_toPure_1530_, lean_box(0), v_fst_1528_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object* v_inst_1532_, lean_object* v_toBind_1533_, lean_object* v___f_1534_, lean_object* v_____r_1535_, lean_object* v_st_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_inc(v___y_1537_);
v___x_1538_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1538_, 0, lean_box(0));
lean_closure_set(v___x_1538_, 1, lean_box(0));
lean_closure_set(v___x_1538_, 2, v___y_1537_);
lean_closure_set(v___x_1538_, 3, v_st_1536_);
v___x_1539_ = lean_apply_2(v_inst_1532_, lean_box(0), v___x_1538_);
v___x_1540_ = lean_apply_4(v_toBind_1533_, lean_box(0), lean_box(0), v___x_1539_, v___f_1534_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed(lean_object* v_inst_1541_, lean_object* v_toBind_1542_, lean_object* v___f_1543_, lean_object* v_____r_1544_, lean_object* v_st_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1541_, v_toBind_1542_, v___f_1543_, v_____r_1544_, v_st_1545_, v___y_1546_);
lean_dec(v___y_1546_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object* v_snd_1548_, lean_object* v_waiters_1549_, lean_object* v_capacity_1550_, lean_object* v_size_1551_, lean_object* v_buffer_1552_, lean_object* v_write_1553_, lean_object* v_read_1554_, lean_object* v_receivers_1555_, lean_object* v_nextId_1556_, uint8_t v_closed_1557_, lean_object* v_pos_1558_, lean_object* v___f_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1562_, 0, v_snd_1548_);
lean_ctor_set(v___x_1562_, 1, v_waiters_1549_);
lean_ctor_set(v___x_1562_, 2, v_capacity_1550_);
lean_ctor_set(v___x_1562_, 3, v_size_1551_);
lean_ctor_set(v___x_1562_, 4, v_buffer_1552_);
lean_ctor_set(v___x_1562_, 5, v_write_1553_);
lean_ctor_set(v___x_1562_, 6, v_read_1554_);
lean_ctor_set(v___x_1562_, 7, v_receivers_1555_);
lean_ctor_set(v___x_1562_, 8, v_nextId_1556_);
lean_ctor_set(v___x_1562_, 9, v_pos_1558_);
lean_ctor_set_uint8(v___x_1562_, sizeof(void*)*10, v_closed_1557_);
v___x_1563_ = lean_box(0);
lean_inc(v_a_1560_);
v___x_1564_ = lean_apply_3(v___f_1559_, v___x_1563_, v___x_1562_, v_a_1560_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object* v_snd_1565_, lean_object* v_waiters_1566_, lean_object* v_capacity_1567_, lean_object* v_size_1568_, lean_object* v_buffer_1569_, lean_object* v_write_1570_, lean_object* v_read_1571_, lean_object* v_receivers_1572_, lean_object* v_nextId_1573_, lean_object* v_closed_1574_, lean_object* v_pos_1575_, lean_object* v___f_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
uint8_t v_closed_boxed_1579_; lean_object* v_res_1580_; 
v_closed_boxed_1579_ = lean_unbox(v_closed_1574_);
v_res_1580_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1565_, v_waiters_1566_, v_capacity_1567_, v_size_1568_, v_buffer_1569_, v_write_1570_, v_read_1571_, v_receivers_1572_, v_nextId_1573_, v_closed_boxed_1579_, v_pos_1575_, v___f_1576_, v_a_1577_, v_a_1578_);
lean_dec(v_a_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object* v_toApplicative_1581_, lean_object* v_inst_1582_, lean_object* v_toBind_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, uint8_t v___x_1586_, lean_object* v_inst_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_fst_1589_; 
v_fst_1589_ = lean_ctor_get(v_a_1588_, 0);
lean_inc(v_fst_1589_);
if (lean_obj_tag(v_fst_1589_) == 1)
{
lean_object* v_snd_1590_; lean_object* v___f_1591_; lean_object* v___f_1592_; uint8_t v___x_1593_; 
v_snd_1590_ = lean_ctor_get(v_a_1588_, 1);
lean_inc(v_snd_1590_);
lean_dec_ref(v_a_1588_);
v___f_1591_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1591_, 0, v_toApplicative_1581_);
lean_closure_set(v___f_1591_, 1, v_fst_1589_);
lean_inc_ref(v___f_1591_);
lean_inc(v_toBind_1583_);
lean_inc(v_inst_1582_);
v___f_1592_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1592_, 0, v_inst_1582_);
lean_closure_set(v___f_1592_, 1, v_toBind_1583_);
lean_closure_set(v___f_1592_, 2, v___f_1591_);
v___x_1593_ = lean_unbox(v_snd_1590_);
lean_dec(v_snd_1590_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v___f_1592_);
lean_dec(v_inst_1587_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1582_, v_toBind_1583_, v___f_1591_, v___x_1594_, v_a_1584_, v_a_1585_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; lean_object* v_producers_1597_; lean_object* v_waiters_1598_; lean_object* v_capacity_1599_; lean_object* v_size_1600_; lean_object* v_buffer_1601_; lean_object* v_write_1602_; lean_object* v_read_1603_; lean_object* v_receivers_1604_; lean_object* v_nextId_1605_; uint8_t v_closed_1606_; lean_object* v_pos_1607_; lean_object* v___x_1608_; 
v___x_1596_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_1584_);
v_producers_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_ref(v_producers_1597_);
v_waiters_1598_ = lean_ctor_get(v___x_1596_, 1);
lean_inc_ref(v_waiters_1598_);
v_capacity_1599_ = lean_ctor_get(v___x_1596_, 2);
lean_inc(v_capacity_1599_);
v_size_1600_ = lean_ctor_get(v___x_1596_, 3);
lean_inc(v_size_1600_);
v_buffer_1601_ = lean_ctor_get(v___x_1596_, 4);
lean_inc_ref(v_buffer_1601_);
v_write_1602_ = lean_ctor_get(v___x_1596_, 5);
lean_inc(v_write_1602_);
v_read_1603_ = lean_ctor_get(v___x_1596_, 6);
lean_inc(v_read_1603_);
v_receivers_1604_ = lean_ctor_get(v___x_1596_, 7);
lean_inc(v_receivers_1604_);
v_nextId_1605_ = lean_ctor_get(v___x_1596_, 8);
lean_inc(v_nextId_1605_);
v_closed_1606_ = lean_ctor_get_uint8(v___x_1596_, sizeof(void*)*10);
v_pos_1607_ = lean_ctor_get(v___x_1596_, 9);
lean_inc(v_pos_1607_);
v___x_1608_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1597_);
if (lean_obj_tag(v___x_1608_) == 1)
{
lean_object* v_val_1609_; lean_object* v_fst_1610_; lean_object* v_snd_1611_; lean_object* v___x_1612_; lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v___x_1596_);
lean_dec_ref(v___f_1591_);
lean_dec(v_inst_1582_);
v_val_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_val_1609_);
lean_dec_ref_known(v___x_1608_, 1);
v_fst_1610_ = lean_ctor_get(v_val_1609_, 0);
lean_inc(v_fst_1610_);
v_snd_1611_ = lean_ctor_get(v_val_1609_, 1);
lean_inc(v_snd_1611_);
lean_dec(v_val_1609_);
v___x_1612_ = lean_box(v_closed_1606_);
lean_inc(v_a_1585_);
v___f_1613_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1613_, 0, v_snd_1611_);
lean_closure_set(v___f_1613_, 1, v_waiters_1598_);
lean_closure_set(v___f_1613_, 2, v_capacity_1599_);
lean_closure_set(v___f_1613_, 3, v_size_1600_);
lean_closure_set(v___f_1613_, 4, v_buffer_1601_);
lean_closure_set(v___f_1613_, 5, v_write_1602_);
lean_closure_set(v___f_1613_, 6, v_read_1603_);
lean_closure_set(v___f_1613_, 7, v_receivers_1604_);
lean_closure_set(v___f_1613_, 8, v_nextId_1605_);
lean_closure_set(v___f_1613_, 9, v___x_1612_);
lean_closure_set(v___f_1613_, 10, v_pos_1607_);
lean_closure_set(v___f_1613_, 11, v___f_1592_);
lean_closure_set(v___f_1613_, 12, v_a_1585_);
v___x_1614_ = lean_box(v___x_1586_);
v___x_1615_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1615_, 0, lean_box(0));
lean_closure_set(v___x_1615_, 1, v___x_1614_);
lean_closure_set(v___x_1615_, 2, v_fst_1610_);
v___x_1616_ = lean_apply_2(v_inst_1587_, lean_box(0), v___x_1615_);
v___x_1617_ = lean_apply_4(v_toBind_1583_, lean_box(0), lean_box(0), v___x_1616_, v___f_1613_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
lean_dec(v___x_1608_);
lean_dec(v_pos_1607_);
lean_dec(v_nextId_1605_);
lean_dec(v_receivers_1604_);
lean_dec(v_read_1603_);
lean_dec(v_write_1602_);
lean_dec_ref(v_buffer_1601_);
lean_dec(v_size_1600_);
lean_dec(v_capacity_1599_);
lean_dec_ref(v_waiters_1598_);
lean_dec_ref(v___f_1592_);
lean_dec(v_inst_1587_);
v___x_1618_ = lean_box(0);
v___x_1619_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1582_, v_toBind_1583_, v___f_1591_, v___x_1618_, v___x_1596_, v_a_1585_);
return v___x_1619_;
}
}
}
else
{
lean_object* v_toPure_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec(v_fst_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_inst_1587_);
lean_dec_ref(v_a_1584_);
lean_dec(v_toBind_1583_);
lean_dec(v_inst_1582_);
v_toPure_1620_ = lean_ctor_get(v_toApplicative_1581_, 1);
lean_inc(v_toPure_1620_);
lean_dec_ref(v_toApplicative_1581_);
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_apply_2(v_toPure_1620_, lean_box(0), v___x_1621_);
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object* v_toApplicative_1623_, lean_object* v_inst_1624_, lean_object* v_toBind_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v___x_1628_, lean_object* v_inst_1629_, lean_object* v_a_1630_){
_start:
{
uint8_t v___x_784__boxed_1631_; lean_object* v_res_1632_; 
v___x_784__boxed_1631_ = lean_unbox(v___x_1628_);
v_res_1632_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1623_, v_inst_1624_, v_toBind_1625_, v_a_1626_, v_a_1627_, v___x_784__boxed_1631_, v_inst_1629_, v_a_1630_);
lean_dec(v_a_1627_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object* v_inst_1633_, lean_object* v_next_1634_, lean_object* v_toBind_1635_, lean_object* v___f_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1633_, v_a_1637_, v_next_1634_);
v___x_1639_ = lean_apply_4(v_toBind_1635_, lean_box(0), lean_box(0), v___x_1638_, v___f_1636_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object* v_a_1640_, lean_object* v_toApplicative_1641_, lean_object* v_inst_1642_, lean_object* v_toBind_1643_, lean_object* v_a_1644_, lean_object* v_inst_1645_, lean_object* v_next_1646_, lean_object* v_inst_1647_, uint8_t v_a_1648_){
_start:
{
if (v_a_1648_ == 0)
{
lean_object* v_capacity_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___f_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_capacity_1649_ = lean_ctor_get(v_a_1640_, 2);
lean_inc(v_capacity_1649_);
v___x_1650_ = 1;
v___x_1651_ = lean_box(v___x_1650_);
lean_inc(v_a_1644_);
lean_inc_n(v_toBind_1643_, 2);
lean_inc_n(v_inst_1642_, 2);
v___f_1652_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1652_, 0, v_toApplicative_1641_);
lean_closure_set(v___f_1652_, 1, v_inst_1642_);
lean_closure_set(v___f_1652_, 2, v_toBind_1643_);
lean_closure_set(v___f_1652_, 3, v_a_1640_);
lean_closure_set(v___f_1652_, 4, v_a_1644_);
lean_closure_set(v___f_1652_, 5, v___x_1651_);
lean_closure_set(v___f_1652_, 6, v_inst_1645_);
lean_inc(v_next_1646_);
v___f_1653_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1653_, 0, v_inst_1642_);
lean_closure_set(v___f_1653_, 1, v_next_1646_);
lean_closure_set(v___f_1653_, 2, v_toBind_1643_);
lean_closure_set(v___f_1653_, 3, v___f_1652_);
v___x_1654_ = lean_nat_mod(v_next_1646_, v_capacity_1649_);
lean_dec(v_capacity_1649_);
lean_dec(v_next_1646_);
v___x_1655_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1647_, v_inst_1642_, v___x_1654_, v_a_1644_);
v___x_1656_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1655_, v___f_1653_);
return v___x_1656_;
}
else
{
lean_object* v_toPure_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_dec_ref(v_inst_1647_);
lean_dec(v_next_1646_);
lean_dec(v_inst_1645_);
lean_dec(v_toBind_1643_);
lean_dec(v_inst_1642_);
lean_dec_ref(v_a_1640_);
v_toPure_1657_ = lean_ctor_get(v_toApplicative_1641_, 1);
lean_inc(v_toPure_1657_);
lean_dec_ref(v_toApplicative_1641_);
v___x_1658_ = lean_box(0);
v___x_1659_ = lean_apply_2(v_toPure_1657_, lean_box(0), v___x_1658_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object* v_a_1660_, lean_object* v_toApplicative_1661_, lean_object* v_inst_1662_, lean_object* v_toBind_1663_, lean_object* v_a_1664_, lean_object* v_inst_1665_, lean_object* v_next_1666_, lean_object* v_inst_1667_, lean_object* v_a_1668_){
_start:
{
uint8_t v_a_boxed_1669_; lean_object* v_res_1670_; 
v_a_boxed_1669_ = lean_unbox(v_a_1668_);
v_res_1670_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1660_, v_toApplicative_1661_, v_inst_1662_, v_toBind_1663_, v_a_1664_, v_inst_1665_, v_next_1666_, v_inst_1667_, v_a_boxed_1669_);
lean_dec(v_a_1664_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object* v_toApplicative_1671_, lean_object* v_inst_1672_, lean_object* v_toBind_1673_, lean_object* v_a_1674_, lean_object* v_inst_1675_, lean_object* v_next_1676_, lean_object* v_inst_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v___f_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_inc_ref(v_inst_1677_);
lean_inc(v_a_1674_);
lean_inc(v_toBind_1673_);
lean_inc(v_inst_1672_);
v___f_1679_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_1679_, 0, v_a_1678_);
lean_closure_set(v___f_1679_, 1, v_toApplicative_1671_);
lean_closure_set(v___f_1679_, 2, v_inst_1672_);
lean_closure_set(v___f_1679_, 3, v_toBind_1673_);
lean_closure_set(v___f_1679_, 4, v_a_1674_);
lean_closure_set(v___f_1679_, 5, v_inst_1675_);
lean_closure_set(v___f_1679_, 6, v_next_1676_);
lean_closure_set(v___f_1679_, 7, v_inst_1677_);
v___x_1680_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_1677_, v_inst_1672_, v_a_1674_);
v___x_1681_ = lean_apply_4(v_toBind_1673_, lean_box(0), lean_box(0), v___x_1680_, v___f_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed(lean_object* v_toApplicative_1682_, lean_object* v_inst_1683_, lean_object* v_toBind_1684_, lean_object* v_a_1685_, lean_object* v_inst_1686_, lean_object* v_next_1687_, lean_object* v_inst_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(v_toApplicative_1682_, v_inst_1683_, v_toBind_1684_, v_a_1685_, v_inst_1686_, v_next_1687_, v_inst_1688_, v_a_1689_);
lean_dec(v_a_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_next_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_toApplicative_1696_; lean_object* v_toBind_1697_; lean_object* v___f_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_toApplicative_1696_ = lean_ctor_get(v_inst_1691_, 0);
lean_inc_ref(v_toApplicative_1696_);
v_toBind_1697_ = lean_ctor_get(v_inst_1691_, 1);
lean_inc_n(v_toBind_1697_, 2);
lean_inc_n(v_a_1695_, 2);
lean_inc(v_inst_1692_);
v___f_1698_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_1698_, 0, v_toApplicative_1696_);
lean_closure_set(v___f_1698_, 1, v_inst_1692_);
lean_closure_set(v___f_1698_, 2, v_toBind_1697_);
lean_closure_set(v___f_1698_, 3, v_a_1695_);
lean_closure_set(v___f_1698_, 4, v_inst_1693_);
lean_closure_set(v___f_1698_, 5, v_next_1694_);
lean_closure_set(v___f_1698_, 6, v_inst_1691_);
v___x_1699_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1699_, 0, lean_box(0));
lean_closure_set(v___x_1699_, 1, lean_box(0));
lean_closure_set(v___x_1699_, 2, v_a_1695_);
v___x_1700_ = lean_apply_2(v_inst_1692_, lean_box(0), v___x_1699_);
v___x_1701_ = lean_apply_4(v_toBind_1697_, lean_box(0), lean_box(0), v___x_1700_, v___f_1698_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___boxed(lean_object* v_inst_1702_, lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_next_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1702_, v_inst_1703_, v_inst_1704_, v_next_1705_, v_a_1706_);
lean_dec(v_a_1706_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object* v_m_1708_, lean_object* v_00_u03b1_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_next_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1710_, v_inst_1711_, v_inst_1712_, v_next_1713_, v_a_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___boxed(lean_object* v_m_1716_, lean_object* v_00_u03b1_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_next_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(v_m_1716_, v_00_u03b1_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v_next_1721_, v_a_1722_);
lean_dec(v_a_1722_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v_capacity_1728_; lean_object* v_buffer_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1727_ = lean_st_ref_get(v_a_1725_);
v_capacity_1728_ = lean_ctor_get(v___x_1727_, 2);
lean_inc(v_capacity_1728_);
v_buffer_1729_ = lean_ctor_get(v___x_1727_, 4);
lean_inc_ref(v_buffer_1729_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_nat_mod(v_place_1724_, v_capacity_1728_);
lean_dec(v_capacity_1728_);
v___x_1731_ = lean_array_fget(v_buffer_1729_, v___x_1730_);
lean_dec(v___x_1730_);
lean_dec_ref(v_buffer_1729_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_1733_, lean_object* v_a_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_1733_, v_a_1734_);
lean_dec(v_a_1734_);
lean_dec(v_place_1733_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_1737_){
_start:
{
lean_object* v___x_1739_; lean_object* v_size_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1739_ = lean_st_ref_get(v_a_1737_);
v_size_1740_ = lean_ctor_get(v___x_1739_, 3);
lean_inc(v_size_1740_);
lean_dec(v___x_1739_);
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_nat_dec_eq(v_size_1740_, v___x_1741_);
lean_dec(v_size_1740_);
v___x_1743_ = lean_box(v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1745_);
lean_dec(v_a_1745_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_1748_, lean_object* v_next_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v_value_1757_; lean_object* v_pos_1758_; lean_object* v_remaining_1759_; uint8_t v___x_1760_; 
v___x_1751_ = lean_st_ref_take(v_slot_1748_);
v_value_1757_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_value_1757_);
v_pos_1758_ = lean_ctor_get(v___x_1751_, 1);
lean_inc(v_pos_1758_);
v_remaining_1759_ = lean_ctor_get(v___x_1751_, 2);
lean_inc(v_remaining_1759_);
v___x_1760_ = lean_nat_dec_eq(v_next_1749_, v_pos_1758_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_remaining_1759_);
lean_dec(v_pos_1758_);
lean_dec(v_value_1757_);
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_box(v___x_1760_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v_fst_1753_ = v___x_1763_;
v_snd_1754_ = v___x_1751_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1782_; 
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; lean_object* v_unused_1784_; lean_object* v_unused_1785_; 
v_unused_1783_ = lean_ctor_get(v___x_1751_, 2);
lean_dec(v_unused_1783_);
v_unused_1784_ = lean_ctor_get(v___x_1751_, 1);
lean_dec(v_unused_1784_);
v_unused_1785_ = lean_ctor_get(v___x_1751_, 0);
lean_dec(v_unused_1785_);
v___x_1765_ = v___x_1751_;
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v___x_1751_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = lean_nat_dec_eq(v_remaining_1759_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1769_ = lean_box(v___x_1768_);
lean_inc(v_value_1757_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_value_1757_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_nat_sub(v_remaining_1759_, v___x_1767_);
lean_dec(v_remaining_1759_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 2, v___x_1771_);
v___x_1773_ = v___x_1765_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_value_1757_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_pos_1758_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
v_fst_1753_ = v___x_1770_;
v_snd_1754_ = v___x_1773_;
goto v___jp_1752_;
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
lean_dec(v_remaining_1759_);
v___x_1775_ = lean_box(v___x_1760_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_value_1757_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_unsigned_to_nat(0u);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 2, v___x_1778_);
lean_ctor_set(v___x_1765_, 0, v___x_1777_);
v___x_1780_ = v___x_1765_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_pos_1758_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
v_fst_1753_ = v___x_1776_;
v_snd_1754_ = v___x_1780_;
goto v___jp_1752_;
}
}
}
}
v___jp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_st_ref_put(v_slot_1748_, v_snd_1754_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v_fst_1753_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_1786_, lean_object* v_next_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_1786_, v_next_1787_);
lean_dec(v_next_1787_);
lean_dec(v_slot_1786_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1866_; 
v___x_1793_ = lean_st_ref_get(v_a_1791_);
v___x_1794_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1791_);
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1866_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1866_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_unbox(v_a_1795_);
lean_dec(v_a_1795_);
if (v___x_1799_ == 0)
{
lean_object* v_capacity_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1861_; 
lean_del_object(v___x_1797_);
v_capacity_1800_ = lean_ctor_get(v___x_1793_, 2);
lean_inc(v_capacity_1800_);
v___x_1801_ = lean_nat_mod(v_next_1790_, v_capacity_1800_);
lean_dec(v_capacity_1800_);
v___x_1802_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_1801_, v_a_1791_);
lean_dec(v___x_1801_);
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1861_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1861_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1860_; 
v___x_1807_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_1803_, v_next_1790_);
lean_dec(v_a_1803_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1860_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1860_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_fst_1812_; lean_object* v_snd_1813_; lean_object* v_st_1815_; lean_object* v___y_1816_; 
v_fst_1812_ = lean_ctor_get(v_a_1808_, 0);
lean_inc(v_fst_1812_);
v_snd_1813_ = lean_ctor_get(v_a_1808_, 1);
lean_inc(v_snd_1813_);
lean_dec(v_a_1808_);
if (lean_obj_tag(v_fst_1812_) == 1)
{
uint8_t v___x_1821_; 
lean_del_object(v___x_1805_);
v___x_1821_ = lean_unbox(v_snd_1813_);
if (v___x_1821_ == 0)
{
lean_dec(v_snd_1813_);
v_st_1815_ = v___x_1793_;
v___y_1816_ = v_a_1791_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1822_; lean_object* v_producers_1823_; lean_object* v_waiters_1824_; lean_object* v_capacity_1825_; lean_object* v_size_1826_; lean_object* v_buffer_1827_; lean_object* v_write_1828_; lean_object* v_read_1829_; lean_object* v_receivers_1830_; lean_object* v_nextId_1831_; uint8_t v_closed_1832_; lean_object* v_pos_1833_; lean_object* v___x_1834_; 
v___x_1822_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_1793_);
v_producers_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc_ref(v_producers_1823_);
v_waiters_1824_ = lean_ctor_get(v___x_1822_, 1);
lean_inc_ref(v_waiters_1824_);
v_capacity_1825_ = lean_ctor_get(v___x_1822_, 2);
lean_inc(v_capacity_1825_);
v_size_1826_ = lean_ctor_get(v___x_1822_, 3);
lean_inc(v_size_1826_);
v_buffer_1827_ = lean_ctor_get(v___x_1822_, 4);
lean_inc_ref(v_buffer_1827_);
v_write_1828_ = lean_ctor_get(v___x_1822_, 5);
lean_inc(v_write_1828_);
v_read_1829_ = lean_ctor_get(v___x_1822_, 6);
lean_inc(v_read_1829_);
v_receivers_1830_ = lean_ctor_get(v___x_1822_, 7);
lean_inc(v_receivers_1830_);
v_nextId_1831_ = lean_ctor_get(v___x_1822_, 8);
lean_inc(v_nextId_1831_);
v_closed_1832_ = lean_ctor_get_uint8(v___x_1822_, sizeof(void*)*10);
v_pos_1833_ = lean_ctor_get(v___x_1822_, 9);
lean_inc(v_pos_1833_);
v___x_1834_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1823_);
if (lean_obj_tag(v___x_1834_) == 1)
{
lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1845_; 
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1845_ == 0)
{
lean_object* v_unused_1846_; lean_object* v_unused_1847_; lean_object* v_unused_1848_; lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; 
v_unused_1846_ = lean_ctor_get(v___x_1822_, 9);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v___x_1822_, 8);
lean_dec(v_unused_1847_);
v_unused_1848_ = lean_ctor_get(v___x_1822_, 7);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v___x_1822_, 6);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v___x_1822_, 5);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v___x_1822_, 4);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v___x_1822_, 3);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v___x_1822_, 2);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v___x_1822_, 1);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v___x_1822_, 0);
lean_dec(v_unused_1855_);
v___x_1836_ = v___x_1822_;
v_isShared_1837_ = v_isSharedCheck_1845_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v___x_1822_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1845_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_val_1838_; lean_object* v_fst_1839_; lean_object* v_snd_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v_val_1838_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v___x_1834_, 1);
v_fst_1839_ = lean_ctor_get(v_val_1838_, 0);
lean_inc(v_fst_1839_);
v_snd_1840_ = lean_ctor_get(v_val_1838_, 1);
lean_inc(v_snd_1840_);
lean_dec(v_val_1838_);
v___x_1841_ = lean_io_promise_resolve(v_snd_1813_, v_fst_1839_);
lean_dec(v_fst_1839_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v_snd_1840_);
v___x_1843_ = v___x_1836_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_snd_1840_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_waiters_1824_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_capacity_1825_);
lean_ctor_set(v_reuseFailAlloc_1844_, 3, v_size_1826_);
lean_ctor_set(v_reuseFailAlloc_1844_, 4, v_buffer_1827_);
lean_ctor_set(v_reuseFailAlloc_1844_, 5, v_write_1828_);
lean_ctor_set(v_reuseFailAlloc_1844_, 6, v_read_1829_);
lean_ctor_set(v_reuseFailAlloc_1844_, 7, v_receivers_1830_);
lean_ctor_set(v_reuseFailAlloc_1844_, 8, v_nextId_1831_);
lean_ctor_set(v_reuseFailAlloc_1844_, 9, v_pos_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*10, v_closed_1832_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
v_st_1815_ = v___x_1843_;
v___y_1816_ = v_a_1791_;
goto v___jp_1814_;
}
}
}
else
{
lean_dec(v___x_1834_);
lean_dec(v_pos_1833_);
lean_dec(v_nextId_1831_);
lean_dec(v_receivers_1830_);
lean_dec(v_read_1829_);
lean_dec(v_write_1828_);
lean_dec_ref(v_buffer_1827_);
lean_dec(v_size_1826_);
lean_dec(v_capacity_1825_);
lean_dec_ref(v_waiters_1824_);
lean_dec(v_snd_1813_);
v_st_1815_ = v___x_1822_;
v___y_1816_ = v_a_1791_;
goto v___jp_1814_;
}
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
lean_dec(v_snd_1813_);
lean_dec(v_fst_1812_);
lean_del_object(v___x_1810_);
lean_dec(v___x_1793_);
v___x_1856_ = lean_box(0);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1856_);
v___x_1858_ = v___x_1805_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
v___jp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_st_ref_swap(v___y_1816_, v_st_1815_);
lean_dec(v___x_1817_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v_fst_1812_);
v___x_1819_ = v___x_1810_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_fst_1812_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
lean_dec(v___x_1793_);
v___x_1862_ = lean_box(0);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1862_);
v___x_1864_ = v___x_1797_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_1867_, lean_object* v_a_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_1867_, v_a_1868_);
lean_dec(v_a_1868_);
lean_dec(v_next_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_a_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1917_; 
v_fst_1874_ = lean_ctor_get(v_a_1871_, 0);
v_snd_1875_ = lean_ctor_get(v_a_1871_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_a_1871_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1877_ = v_a_1871_;
v_isShared_1878_ = v_isSharedCheck_1917_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_snd_1875_);
lean_inc(v_fst_1874_);
lean_dec(v_a_1871_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1917_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
uint8_t v___y_1880_; lean_object* v_size_1912_; lean_object* v_pos_1913_; uint8_t v___x_1914_; 
v_size_1912_ = lean_ctor_get(v_fst_1874_, 3);
v_pos_1913_ = lean_ctor_get(v_fst_1874_, 9);
v___x_1914_ = lean_nat_dec_lt(v_snd_1875_, v_pos_1913_);
if (v___x_1914_ == 0)
{
v___y_1880_ = v___x_1914_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_nat_dec_lt(v___x_1915_, v_size_1912_);
v___y_1880_ = v___x_1916_;
goto v___jp_1879_;
}
v___jp_1879_:
{
if (v___y_1880_ == 0)
{
lean_object* v___x_1882_; 
if (v_isShared_1878_ == 0)
{
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_fst_1874_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_snd_1875_);
v___x_1882_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
else
{
lean_object* v___x_1885_; 
v___x_1885_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_1875_, v___y_1872_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1903_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1903_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1903_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
if (lean_obj_tag(v_a_1886_) == 1)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
lean_dec_ref_known(v_a_1886_, 1);
lean_del_object(v___x_1888_);
lean_dec(v_fst_1874_);
v___x_1890_ = lean_st_ref_get(v___y_1872_);
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = lean_nat_add(v_snd_1875_, v___x_1891_);
lean_dec(v_snd_1875_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1892_);
lean_ctor_set(v___x_1877_, 0, v___x_1890_);
v___x_1894_ = v___x_1877_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
v_a_1871_ = v___x_1894_;
goto _start;
}
}
else
{
lean_object* v___x_1898_; 
lean_dec(v_a_1886_);
if (v_isShared_1878_ == 0)
{
v___x_1898_ = v___x_1877_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_fst_1874_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_snd_1875_);
v___x_1898_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1898_);
v___x_1900_ = v___x_1888_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1877_);
lean_dec(v_snd_1875_);
lean_dec(v_fst_1874_);
v_a_1904_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1885_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1885_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_a_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_1918_, v___y_1919_);
lean_dec(v___y_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_1922_, lean_object* v_k_1923_){
_start:
{
if (lean_obj_tag(v_t_1922_) == 0)
{
lean_object* v_k_1924_; lean_object* v_v_1925_; lean_object* v_l_1926_; lean_object* v_r_1927_; uint8_t v___x_1928_; 
v_k_1924_ = lean_ctor_get(v_t_1922_, 1);
v_v_1925_ = lean_ctor_get(v_t_1922_, 2);
v_l_1926_ = lean_ctor_get(v_t_1922_, 3);
v_r_1927_ = lean_ctor_get(v_t_1922_, 4);
v___x_1928_ = lean_nat_dec_lt(v_k_1923_, v_k_1924_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; 
v___x_1929_ = lean_nat_dec_eq(v_k_1923_, v_k_1924_);
if (v___x_1929_ == 0)
{
v_t_1922_ = v_r_1927_;
goto _start;
}
else
{
lean_object* v___x_1931_; 
lean_inc(v_v_1925_);
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_v_1925_);
return v___x_1931_;
}
}
else
{
v_t_1922_ = v_l_1926_;
goto _start;
}
}
else
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_box(0);
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_1934_, lean_object* v_k_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_1934_, v_k_1935_);
lean_dec(v_k_1935_);
lean_dec(v_t_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_1937_, lean_object* v_t_1938_){
_start:
{
if (lean_obj_tag(v_t_1938_) == 0)
{
lean_object* v_k_1939_; lean_object* v_v_1940_; lean_object* v_l_1941_; lean_object* v_r_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_2597_; 
v_k_1939_ = lean_ctor_get(v_t_1938_, 1);
v_v_1940_ = lean_ctor_get(v_t_1938_, 2);
v_l_1941_ = lean_ctor_get(v_t_1938_, 3);
v_r_1942_ = lean_ctor_get(v_t_1938_, 4);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_t_1938_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v_t_1938_, 0);
lean_dec(v_unused_2598_);
v___x_1944_ = v_t_1938_;
v_isShared_1945_ = v_isSharedCheck_2597_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_r_1942_);
lean_inc(v_l_1941_);
lean_inc(v_v_1940_);
lean_inc(v_k_1939_);
lean_dec(v_t_1938_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_2597_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_lt(v_k_1937_, v_k_1939_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_nat_dec_eq(v_k_1937_, v_k_1939_);
if (v___x_1947_ == 0)
{
lean_object* v_impl_1948_; lean_object* v___x_1949_; 
v_impl_1948_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1937_, v_r_1942_);
v___x_1949_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1948_) == 0)
{
if (lean_obj_tag(v_l_1941_) == 0)
{
lean_object* v_size_1950_; lean_object* v_size_1951_; lean_object* v_k_1952_; lean_object* v_v_1953_; lean_object* v_l_1954_; lean_object* v_r_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_size_1950_ = lean_ctor_get(v_impl_1948_, 0);
lean_inc(v_size_1950_);
v_size_1951_ = lean_ctor_get(v_l_1941_, 0);
v_k_1952_ = lean_ctor_get(v_l_1941_, 1);
v_v_1953_ = lean_ctor_get(v_l_1941_, 2);
v_l_1954_ = lean_ctor_get(v_l_1941_, 3);
v_r_1955_ = lean_ctor_get(v_l_1941_, 4);
lean_inc(v_r_1955_);
v___x_1956_ = lean_unsigned_to_nat(3u);
v___x_1957_ = lean_nat_mul(v___x_1956_, v_size_1950_);
v___x_1958_ = lean_nat_dec_lt(v___x_1957_, v_size_1951_);
lean_dec(v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_dec(v_r_1955_);
v___x_1959_ = lean_nat_add(v___x_1949_, v_size_1951_);
v___x_1960_ = lean_nat_add(v___x_1959_, v_size_1950_);
lean_dec(v_size_1950_);
lean_dec(v___x_1959_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_impl_1948_);
lean_ctor_set(v___x_1944_, 0, v___x_1960_);
v___x_1962_ = v___x_1944_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v_impl_1948_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
else
{
lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2029_; 
lean_inc(v_l_1954_);
lean_inc(v_v_1953_);
lean_inc(v_k_1952_);
lean_inc(v_size_1951_);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; lean_object* v_unused_2034_; 
v_unused_2030_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_l_1941_, 2);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_l_1941_, 1);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_l_1941_, 0);
lean_dec(v_unused_2034_);
v___x_1965_ = v_l_1941_;
v_isShared_1966_ = v_isSharedCheck_2029_;
goto v_resetjp_1964_;
}
else
{
lean_dec(v_l_1941_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2029_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_size_1967_; lean_object* v_size_1968_; lean_object* v_k_1969_; lean_object* v_v_1970_; lean_object* v_l_1971_; lean_object* v_r_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_size_1967_ = lean_ctor_get(v_l_1954_, 0);
v_size_1968_ = lean_ctor_get(v_r_1955_, 0);
v_k_1969_ = lean_ctor_get(v_r_1955_, 1);
v_v_1970_ = lean_ctor_get(v_r_1955_, 2);
v_l_1971_ = lean_ctor_get(v_r_1955_, 3);
v_r_1972_ = lean_ctor_get(v_r_1955_, 4);
v___x_1973_ = lean_unsigned_to_nat(2u);
v___x_1974_ = lean_nat_mul(v___x_1973_, v_size_1967_);
v___x_1975_ = lean_nat_dec_lt(v_size_1968_, v___x_1974_);
lean_dec(v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2004_; 
lean_inc(v_r_1972_);
lean_inc(v_l_1971_);
lean_inc(v_v_1970_);
lean_inc(v_k_1969_);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_r_1955_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; lean_object* v_unused_2006_; lean_object* v_unused_2007_; lean_object* v_unused_2008_; lean_object* v_unused_2009_; 
v_unused_2005_ = lean_ctor_get(v_r_1955_, 4);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_r_1955_, 3);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_r_1955_, 2);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_r_1955_, 1);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_r_1955_, 0);
lean_dec(v_unused_2009_);
v___x_1977_ = v_r_1955_;
v_isShared_1978_ = v_isSharedCheck_2004_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v_r_1955_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2004_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___x_1992_; lean_object* v___y_1994_; 
v___x_1979_ = lean_nat_add(v___x_1949_, v_size_1951_);
lean_dec(v_size_1951_);
v___x_1980_ = lean_nat_add(v___x_1979_, v_size_1950_);
lean_dec(v___x_1979_);
v___x_1992_ = lean_nat_add(v___x_1949_, v_size_1967_);
if (lean_obj_tag(v_l_1971_) == 0)
{
lean_object* v_size_2002_; 
v_size_2002_ = lean_ctor_get(v_l_1971_, 0);
lean_inc(v_size_2002_);
v___y_1994_ = v_size_2002_;
goto v___jp_1993_;
}
else
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_unsigned_to_nat(0u);
v___y_1994_ = v___x_2003_;
goto v___jp_1993_;
}
v___jp_1981_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_nat_add(v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec(v___y_1983_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 4, v_impl_1948_);
lean_ctor_set(v___x_1977_, 3, v_r_1972_);
lean_ctor_set(v___x_1977_, 2, v_v_1940_);
lean_ctor_set(v___x_1977_, 1, v_k_1939_);
lean_ctor_set(v___x_1977_, 0, v___x_1985_);
v___x_1987_ = v___x_1977_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_r_1972_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v_impl_1948_);
v___x_1987_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 4, v___x_1987_);
lean_ctor_set(v___x_1965_, 3, v___y_1982_);
lean_ctor_set(v___x_1965_, 2, v_v_1970_);
lean_ctor_set(v___x_1965_, 1, v_k_1969_);
lean_ctor_set(v___x_1965_, 0, v___x_1980_);
v___x_1989_ = v___x_1965_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_k_1969_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_v_1970_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v___y_1982_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
v___jp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1995_ = lean_nat_add(v___x_1992_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec(v___x_1992_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_l_1971_);
lean_ctor_set(v___x_1944_, 3, v_l_1954_);
lean_ctor_set(v___x_1944_, 2, v_v_1953_);
lean_ctor_set(v___x_1944_, 1, v_k_1952_);
lean_ctor_set(v___x_1944_, 0, v___x_1995_);
v___x_1997_ = v___x_1944_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_k_1952_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_v_1953_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v_l_1954_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_l_1971_);
v___x_1997_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_nat_add(v___x_1949_, v_size_1950_);
lean_dec(v_size_1950_);
if (lean_obj_tag(v_r_1972_) == 0)
{
lean_object* v_size_1999_; 
v_size_1999_ = lean_ctor_get(v_r_1972_, 0);
lean_inc(v_size_1999_);
v___y_1982_ = v___x_1997_;
v___y_1983_ = v___x_1998_;
v___y_1984_ = v_size_1999_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_unsigned_to_nat(0u);
v___y_1982_ = v___x_1997_;
v___y_1983_ = v___x_1998_;
v___y_1984_ = v___x_2000_;
goto v___jp_1981_;
}
}
}
}
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
lean_del_object(v___x_1944_);
v___x_2010_ = lean_nat_add(v___x_1949_, v_size_1951_);
lean_dec(v_size_1951_);
v___x_2011_ = lean_nat_add(v___x_2010_, v_size_1950_);
lean_dec(v___x_2010_);
v___x_2012_ = lean_nat_add(v___x_1949_, v_size_1950_);
lean_dec(v_size_1950_);
v___x_2013_ = lean_nat_add(v___x_2012_, v_size_1968_);
lean_dec(v___x_2012_);
lean_inc_ref(v_impl_1948_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 4, v_impl_1948_);
lean_ctor_set(v___x_1965_, 3, v_r_1955_);
lean_ctor_set(v___x_1965_, 2, v_v_1940_);
lean_ctor_set(v___x_1965_, 1, v_k_1939_);
lean_ctor_set(v___x_1965_, 0, v___x_2013_);
v___x_2015_ = v___x_1965_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v_r_1955_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_impl_1948_);
v___x_2015_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
v_isSharedCheck_2022_ = !lean_is_exclusive(v_impl_1948_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; lean_object* v_unused_2024_; lean_object* v_unused_2025_; lean_object* v_unused_2026_; lean_object* v_unused_2027_; 
v_unused_2023_ = lean_ctor_get(v_impl_1948_, 4);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_impl_1948_, 3);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_impl_1948_, 2);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_impl_1948_, 1);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_impl_1948_, 0);
lean_dec(v_unused_2027_);
v___x_2017_ = v_impl_1948_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v_impl_1948_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 4, v___x_2015_);
lean_ctor_set(v___x_2017_, 3, v_l_1954_);
lean_ctor_set(v___x_2017_, 2, v_v_1953_);
lean_ctor_set(v___x_2017_, 1, v_k_1952_);
lean_ctor_set(v___x_2017_, 0, v___x_2011_);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_k_1952_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_v_1953_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v_l_1954_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v___x_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v_size_2035_ = lean_ctor_get(v_impl_1948_, 0);
lean_inc(v_size_2035_);
v___x_2036_ = lean_nat_add(v___x_1949_, v_size_2035_);
lean_dec(v_size_2035_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_impl_1948_);
lean_ctor_set(v___x_1944_, 0, v___x_2036_);
v___x_2038_ = v___x_1944_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_2039_, 4, v_impl_1948_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
else
{
if (lean_obj_tag(v_l_1941_) == 0)
{
lean_object* v_l_2040_; 
v_l_2040_ = lean_ctor_get(v_l_1941_, 3);
if (lean_obj_tag(v_l_2040_) == 0)
{
lean_object* v_r_2041_; 
lean_inc_ref(v_l_2040_);
v_r_2041_ = lean_ctor_get(v_l_1941_, 4);
lean_inc(v_r_2041_);
if (lean_obj_tag(v_r_2041_) == 0)
{
lean_object* v_size_2042_; lean_object* v_k_2043_; lean_object* v_v_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2057_; 
v_size_2042_ = lean_ctor_get(v_l_1941_, 0);
v_k_2043_ = lean_ctor_get(v_l_1941_, 1);
v_v_2044_ = lean_ctor_get(v_l_1941_, 2);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; lean_object* v_unused_2059_; 
v_unused_2058_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2059_);
v___x_2046_ = v_l_1941_;
v_isShared_2047_ = v_isSharedCheck_2057_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_v_2044_);
lean_inc(v_k_2043_);
lean_inc(v_size_2042_);
lean_dec(v_l_1941_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2057_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_size_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v_size_2048_ = lean_ctor_get(v_r_2041_, 0);
v___x_2049_ = lean_nat_add(v___x_1949_, v_size_2042_);
lean_dec(v_size_2042_);
v___x_2050_ = lean_nat_add(v___x_1949_, v_size_2048_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 4, v_impl_1948_);
lean_ctor_set(v___x_2046_, 3, v_r_2041_);
lean_ctor_set(v___x_2046_, 2, v_v_1940_);
lean_ctor_set(v___x_2046_, 1, v_k_1939_);
lean_ctor_set(v___x_2046_, 0, v___x_2050_);
v___x_2052_ = v___x_2046_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_r_2041_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_impl_1948_);
v___x_2052_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_2052_);
lean_ctor_set(v___x_1944_, 3, v_l_2040_);
lean_ctor_set(v___x_1944_, 2, v_v_2044_);
lean_ctor_set(v___x_1944_, 1, v_k_2043_);
lean_ctor_set(v___x_1944_, 0, v___x_2049_);
v___x_2054_ = v___x_1944_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_k_2043_);
lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_v_2044_);
lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_l_2040_);
lean_ctor_set(v_reuseFailAlloc_2055_, 4, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_k_2060_; lean_object* v_v_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2072_; 
v_k_2060_ = lean_ctor_get(v_l_1941_, 1);
v_v_2061_ = lean_ctor_get(v_l_1941_, 2);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; lean_object* v_unused_2074_; lean_object* v_unused_2075_; 
v_unused_2073_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_l_1941_, 0);
lean_dec(v_unused_2075_);
v___x_2063_ = v_l_1941_;
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_v_2061_);
lean_inc(v_k_2060_);
lean_dec(v_l_1941_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = lean_unsigned_to_nat(3u);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 3, v_r_2041_);
lean_ctor_set(v___x_2063_, 2, v_v_1940_);
lean_ctor_set(v___x_2063_, 1, v_k_1939_);
lean_ctor_set(v___x_2063_, 0, v___x_1949_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_r_2041_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_r_2041_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_2067_);
lean_ctor_set(v___x_1944_, 3, v_l_2040_);
lean_ctor_set(v___x_1944_, 2, v_v_2061_);
lean_ctor_set(v___x_1944_, 1, v_k_2060_);
lean_ctor_set(v___x_1944_, 0, v___x_2065_);
v___x_2069_ = v___x_1944_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_k_2060_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_v_2061_);
lean_ctor_set(v_reuseFailAlloc_2070_, 3, v_l_2040_);
lean_ctor_set(v_reuseFailAlloc_2070_, 4, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
else
{
lean_object* v_r_2076_; 
v_r_2076_ = lean_ctor_get(v_l_1941_, 4);
lean_inc(v_r_2076_);
if (lean_obj_tag(v_r_2076_) == 0)
{
lean_object* v_k_2077_; lean_object* v_v_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2101_; 
lean_inc(v_l_2040_);
v_k_2077_ = lean_ctor_get(v_l_1941_, 1);
v_v_2078_ = lean_ctor_get(v_l_1941_, 2);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; lean_object* v_unused_2103_; lean_object* v_unused_2104_; 
v_unused_2102_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2102_);
v_unused_2103_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2103_);
v_unused_2104_ = lean_ctor_get(v_l_1941_, 0);
lean_dec(v_unused_2104_);
v___x_2080_ = v_l_1941_;
v_isShared_2081_ = v_isSharedCheck_2101_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_v_2078_);
lean_inc(v_k_2077_);
lean_dec(v_l_1941_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2101_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_k_2082_; lean_object* v_v_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2097_; 
v_k_2082_ = lean_ctor_get(v_r_2076_, 1);
v_v_2083_ = lean_ctor_get(v_r_2076_, 2);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_r_2076_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; lean_object* v_unused_2099_; lean_object* v_unused_2100_; 
v_unused_2098_ = lean_ctor_get(v_r_2076_, 4);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_r_2076_, 3);
lean_dec(v_unused_2099_);
v_unused_2100_ = lean_ctor_get(v_r_2076_, 0);
lean_dec(v_unused_2100_);
v___x_2085_ = v_r_2076_;
v_isShared_2086_ = v_isSharedCheck_2097_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_v_2083_);
lean_inc(v_k_2082_);
lean_dec(v_r_2076_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2097_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_unsigned_to_nat(3u);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 4, v_l_2040_);
lean_ctor_set(v___x_2085_, 3, v_l_2040_);
lean_ctor_set(v___x_2085_, 2, v_v_2078_);
lean_ctor_set(v___x_2085_, 1, v_k_2077_);
lean_ctor_set(v___x_2085_, 0, v___x_1949_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_l_2040_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_l_2040_);
v___x_2089_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2091_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 4, v_l_2040_);
lean_ctor_set(v___x_2080_, 2, v_v_1940_);
lean_ctor_set(v___x_2080_, 1, v_k_1939_);
lean_ctor_set(v___x_2080_, 0, v___x_1949_);
v___x_2091_ = v___x_2080_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_l_2040_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_l_2040_);
v___x_2091_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_2091_);
lean_ctor_set(v___x_1944_, 3, v___x_2089_);
lean_ctor_set(v___x_1944_, 2, v_v_2083_);
lean_ctor_set(v___x_1944_, 1, v_k_2082_);
lean_ctor_set(v___x_1944_, 0, v___x_2087_);
v___x_2093_ = v___x_1944_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_k_2082_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_v_2083_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2094_, 4, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_unsigned_to_nat(2u);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_r_2076_);
lean_ctor_set(v___x_1944_, 0, v___x_2105_);
v___x_2107_ = v___x_1944_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_r_2076_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v___x_2110_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_l_1941_);
lean_ctor_set(v___x_1944_, 0, v___x_1949_);
v___x_2110_ = v___x_1944_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_l_1941_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_del_object(v___x_1944_);
lean_dec(v_v_1940_);
lean_dec(v_k_1939_);
if (lean_obj_tag(v_l_1941_) == 0)
{
if (lean_obj_tag(v_r_1942_) == 0)
{
lean_object* v_size_2112_; lean_object* v_k_2113_; lean_object* v_v_2114_; lean_object* v_l_2115_; lean_object* v_r_2116_; lean_object* v_size_2117_; lean_object* v_k_2118_; lean_object* v_v_2119_; lean_object* v_l_2120_; lean_object* v_r_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v_size_2112_ = lean_ctor_get(v_l_1941_, 0);
v_k_2113_ = lean_ctor_get(v_l_1941_, 1);
v_v_2114_ = lean_ctor_get(v_l_1941_, 2);
v_l_2115_ = lean_ctor_get(v_l_1941_, 3);
v_r_2116_ = lean_ctor_get(v_l_1941_, 4);
lean_inc(v_r_2116_);
v_size_2117_ = lean_ctor_get(v_r_1942_, 0);
v_k_2118_ = lean_ctor_get(v_r_1942_, 1);
v_v_2119_ = lean_ctor_get(v_r_1942_, 2);
v_l_2120_ = lean_ctor_get(v_r_1942_, 3);
lean_inc(v_l_2120_);
v_r_2121_ = lean_ctor_get(v_r_1942_, 4);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_dec_lt(v_size_2112_, v_size_2117_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2259_; 
lean_inc(v_l_2115_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; lean_object* v_unused_2261_; lean_object* v_unused_2262_; lean_object* v_unused_2263_; lean_object* v_unused_2264_; 
v_unused_2260_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_l_1941_, 2);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_l_1941_, 1);
lean_dec(v_unused_2263_);
v_unused_2264_ = lean_ctor_get(v_l_1941_, 0);
lean_dec(v_unused_2264_);
v___x_2125_ = v_l_1941_;
v_isShared_2126_ = v_isSharedCheck_2259_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v_l_1941_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2259_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v_tree_2128_; 
v___x_2127_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2113_, v_v_2114_, v_l_2115_, v_r_2116_);
v_tree_2128_ = lean_ctor_get(v___x_2127_, 2);
lean_inc(v_tree_2128_);
if (lean_obj_tag(v_tree_2128_) == 0)
{
lean_object* v_k_2129_; lean_object* v_v_2130_; lean_object* v_size_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v_k_2129_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_k_2129_);
v_v_2130_ = lean_ctor_get(v___x_2127_, 1);
lean_inc(v_v_2130_);
lean_dec_ref(v___x_2127_);
v_size_2131_ = lean_ctor_get(v_tree_2128_, 0);
v___x_2132_ = lean_unsigned_to_nat(3u);
v___x_2133_ = lean_nat_mul(v___x_2132_, v_size_2131_);
v___x_2134_ = lean_nat_dec_lt(v___x_2133_, v_size_2117_);
lean_dec(v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_dec(v_l_2120_);
v___x_2135_ = lean_nat_add(v___x_2122_, v_size_2131_);
v___x_2136_ = lean_nat_add(v___x_2135_, v_size_2117_);
lean_dec(v___x_2135_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v_r_1942_);
lean_ctor_set(v___x_2125_, 3, v_tree_2128_);
lean_ctor_set(v___x_2125_, 2, v_v_2130_);
lean_ctor_set(v___x_2125_, 1, v_k_2129_);
lean_ctor_set(v___x_2125_, 0, v___x_2136_);
v___x_2138_ = v___x_2125_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_k_2129_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_v_2130_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_tree_2128_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v_r_1942_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
else
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2194_; 
lean_inc(v_r_2121_);
lean_inc(v_v_2119_);
lean_inc(v_k_2118_);
lean_inc(v_size_2117_);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; lean_object* v_unused_2196_; lean_object* v_unused_2197_; lean_object* v_unused_2198_; lean_object* v_unused_2199_; 
v_unused_2195_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2195_);
v_unused_2196_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2196_);
v_unused_2197_ = lean_ctor_get(v_r_1942_, 2);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_r_1942_, 1);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_r_1942_, 0);
lean_dec(v_unused_2199_);
v___x_2141_ = v_r_1942_;
v_isShared_2142_ = v_isSharedCheck_2194_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_r_1942_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2194_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_size_2143_; lean_object* v_k_2144_; lean_object* v_v_2145_; lean_object* v_l_2146_; lean_object* v_r_2147_; lean_object* v_size_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v_size_2143_ = lean_ctor_get(v_l_2120_, 0);
v_k_2144_ = lean_ctor_get(v_l_2120_, 1);
v_v_2145_ = lean_ctor_get(v_l_2120_, 2);
v_l_2146_ = lean_ctor_get(v_l_2120_, 3);
v_r_2147_ = lean_ctor_get(v_l_2120_, 4);
v_size_2148_ = lean_ctor_get(v_r_2121_, 0);
v___x_2149_ = lean_unsigned_to_nat(2u);
v___x_2150_ = lean_nat_mul(v___x_2149_, v_size_2148_);
v___x_2151_ = lean_nat_dec_lt(v_size_2143_, v___x_2150_);
lean_dec(v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2179_; 
lean_inc(v_r_2147_);
lean_inc(v_l_2146_);
lean_inc(v_v_2145_);
lean_inc(v_k_2144_);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_l_2120_);
if (v_isSharedCheck_2179_ == 0)
{
lean_object* v_unused_2180_; lean_object* v_unused_2181_; lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; 
v_unused_2180_ = lean_ctor_get(v_l_2120_, 4);
lean_dec(v_unused_2180_);
v_unused_2181_ = lean_ctor_get(v_l_2120_, 3);
lean_dec(v_unused_2181_);
v_unused_2182_ = lean_ctor_get(v_l_2120_, 2);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_l_2120_, 1);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_l_2120_, 0);
lean_dec(v_unused_2184_);
v___x_2153_ = v_l_2120_;
v_isShared_2154_ = v_isSharedCheck_2179_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v_l_2120_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2179_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2169_; 
v___x_2155_ = lean_nat_add(v___x_2122_, v_size_2131_);
v___x_2156_ = lean_nat_add(v___x_2155_, v_size_2117_);
lean_dec(v_size_2117_);
if (lean_obj_tag(v_l_2146_) == 0)
{
lean_object* v_size_2177_; 
v_size_2177_ = lean_ctor_get(v_l_2146_, 0);
lean_inc(v_size_2177_);
v___y_2169_ = v_size_2177_;
goto v___jp_2168_;
}
else
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_unsigned_to_nat(0u);
v___y_2169_ = v___x_2178_;
goto v___jp_2168_;
}
v___jp_2157_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_nat_add(v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec(v___y_2159_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 4, v_r_2121_);
lean_ctor_set(v___x_2153_, 3, v_r_2147_);
lean_ctor_set(v___x_2153_, 2, v_v_2119_);
lean_ctor_set(v___x_2153_, 1, v_k_2118_);
lean_ctor_set(v___x_2153_, 0, v___x_2161_);
v___x_2163_ = v___x_2153_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_r_2147_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_r_2121_);
v___x_2163_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2165_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v___x_2163_);
lean_ctor_set(v___x_2141_, 3, v___y_2158_);
lean_ctor_set(v___x_2141_, 2, v_v_2145_);
lean_ctor_set(v___x_2141_, 1, v_k_2144_);
lean_ctor_set(v___x_2141_, 0, v___x_2156_);
v___x_2165_ = v___x_2141_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_k_2144_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_v_2145_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v___y_2158_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
v___jp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_nat_add(v___x_2155_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec(v___x_2155_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v_l_2146_);
lean_ctor_set(v___x_2125_, 3, v_tree_2128_);
lean_ctor_set(v___x_2125_, 2, v_v_2130_);
lean_ctor_set(v___x_2125_, 1, v_k_2129_);
lean_ctor_set(v___x_2125_, 0, v___x_2170_);
v___x_2172_ = v___x_2125_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_k_2129_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_v_2130_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_tree_2128_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_l_2146_);
v___x_2172_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_nat_add(v___x_2122_, v_size_2148_);
if (lean_obj_tag(v_r_2147_) == 0)
{
lean_object* v_size_2174_; 
v_size_2174_ = lean_ctor_get(v_r_2147_, 0);
lean_inc(v_size_2174_);
v___y_2158_ = v___x_2172_;
v___y_2159_ = v___x_2173_;
v___y_2160_ = v_size_2174_;
goto v___jp_2157_;
}
else
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___y_2158_ = v___x_2172_;
v___y_2159_ = v___x_2173_;
v___y_2160_ = v___x_2175_;
goto v___jp_2157_;
}
}
}
}
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2185_ = lean_nat_add(v___x_2122_, v_size_2131_);
v___x_2186_ = lean_nat_add(v___x_2185_, v_size_2117_);
lean_dec(v_size_2117_);
v___x_2187_ = lean_nat_add(v___x_2185_, v_size_2143_);
lean_dec(v___x_2185_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v_l_2120_);
lean_ctor_set(v___x_2141_, 3, v_tree_2128_);
lean_ctor_set(v___x_2141_, 2, v_v_2130_);
lean_ctor_set(v___x_2141_, 1, v_k_2129_);
lean_ctor_set(v___x_2141_, 0, v___x_2187_);
v___x_2189_ = v___x_2141_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_k_2129_);
lean_ctor_set(v_reuseFailAlloc_2193_, 2, v_v_2130_);
lean_ctor_set(v_reuseFailAlloc_2193_, 3, v_tree_2128_);
lean_ctor_set(v_reuseFailAlloc_2193_, 4, v_l_2120_);
v___x_2189_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v_r_2121_);
lean_ctor_set(v___x_2125_, 3, v___x_2189_);
lean_ctor_set(v___x_2125_, 2, v_v_2119_);
lean_ctor_set(v___x_2125_, 1, v_k_2118_);
lean_ctor_set(v___x_2125_, 0, v___x_2186_);
v___x_2191_ = v___x_2125_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2192_, 3, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2192_, 4, v_r_2121_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
}
else
{
lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2253_; 
lean_inc(v_r_2121_);
lean_inc(v_v_2119_);
lean_inc(v_k_2118_);
lean_inc(v_size_2117_);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; lean_object* v_unused_2255_; lean_object* v_unused_2256_; lean_object* v_unused_2257_; lean_object* v_unused_2258_; 
v_unused_2254_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_r_1942_, 2);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_r_1942_, 1);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_r_1942_, 0);
lean_dec(v_unused_2258_);
v___x_2201_ = v_r_1942_;
v_isShared_2202_ = v_isSharedCheck_2253_;
goto v_resetjp_2200_;
}
else
{
lean_dec(v_r_1942_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2253_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
if (lean_obj_tag(v_l_2120_) == 0)
{
if (lean_obj_tag(v_r_2121_) == 0)
{
lean_object* v_k_2203_; lean_object* v_v_2204_; lean_object* v_size_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v_k_2203_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_k_2203_);
v_v_2204_ = lean_ctor_get(v___x_2127_, 1);
lean_inc(v_v_2204_);
lean_dec_ref(v___x_2127_);
v_size_2205_ = lean_ctor_get(v_l_2120_, 0);
v___x_2206_ = lean_nat_add(v___x_2122_, v_size_2117_);
lean_dec(v_size_2117_);
v___x_2207_ = lean_nat_add(v___x_2122_, v_size_2205_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_l_2120_);
lean_ctor_set(v___x_2201_, 3, v_tree_2128_);
lean_ctor_set(v___x_2201_, 2, v_v_2204_);
lean_ctor_set(v___x_2201_, 1, v_k_2203_);
lean_ctor_set(v___x_2201_, 0, v___x_2207_);
v___x_2209_ = v___x_2201_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_k_2203_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_v_2204_);
lean_ctor_set(v_reuseFailAlloc_2213_, 3, v_tree_2128_);
lean_ctor_set(v_reuseFailAlloc_2213_, 4, v_l_2120_);
v___x_2209_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2211_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v_r_2121_);
lean_ctor_set(v___x_2125_, 3, v___x_2209_);
lean_ctor_set(v___x_2125_, 2, v_v_2119_);
lean_ctor_set(v___x_2125_, 1, v_k_2118_);
lean_ctor_set(v___x_2125_, 0, v___x_2206_);
v___x_2211_ = v___x_2125_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2212_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2212_, 3, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2212_, 4, v_r_2121_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
else
{
lean_object* v_k_2214_; lean_object* v_v_2215_; lean_object* v_k_2216_; lean_object* v_v_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_size_2117_);
v_k_2214_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_k_2214_);
v_v_2215_ = lean_ctor_get(v___x_2127_, 1);
lean_inc(v_v_2215_);
lean_dec_ref(v___x_2127_);
v_k_2216_ = lean_ctor_get(v_l_2120_, 1);
v_v_2217_ = lean_ctor_get(v_l_2120_, 2);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_l_2120_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; lean_object* v_unused_2233_; lean_object* v_unused_2234_; 
v_unused_2232_ = lean_ctor_get(v_l_2120_, 4);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_l_2120_, 3);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_l_2120_, 0);
lean_dec(v_unused_2234_);
v___x_2219_ = v_l_2120_;
v_isShared_2220_ = v_isSharedCheck_2231_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_v_2217_);
lean_inc(v_k_2216_);
lean_dec(v_l_2120_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2231_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2221_ = lean_unsigned_to_nat(3u);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 4, v_r_2121_);
lean_ctor_set(v___x_2219_, 3, v_r_2121_);
lean_ctor_set(v___x_2219_, 2, v_v_2215_);
lean_ctor_set(v___x_2219_, 1, v_k_2214_);
lean_ctor_set(v___x_2219_, 0, v___x_2122_);
v___x_2223_ = v___x_2219_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_k_2214_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_v_2215_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_r_2121_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_r_2121_);
v___x_2223_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2225_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 3, v_r_2121_);
lean_ctor_set(v___x_2201_, 0, v___x_2122_);
v___x_2225_ = v___x_2201_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_r_2121_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_r_2121_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v___x_2225_);
lean_ctor_set(v___x_2125_, 3, v___x_2223_);
lean_ctor_set(v___x_2125_, 2, v_v_2217_);
lean_ctor_set(v___x_2125_, 1, v_k_2216_);
lean_ctor_set(v___x_2125_, 0, v___x_2221_);
v___x_2227_ = v___x_2125_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_k_2216_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_v_2217_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2121_) == 0)
{
lean_object* v_k_2235_; lean_object* v_v_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
lean_dec(v_size_2117_);
v_k_2235_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_k_2235_);
v_v_2236_ = lean_ctor_get(v___x_2127_, 1);
lean_inc(v_v_2236_);
lean_dec_ref(v___x_2127_);
v___x_2237_ = lean_unsigned_to_nat(3u);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 4, v_l_2120_);
lean_ctor_set(v___x_2201_, 2, v_v_2236_);
lean_ctor_set(v___x_2201_, 1, v_k_2235_);
lean_ctor_set(v___x_2201_, 0, v___x_2122_);
v___x_2239_ = v___x_2201_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_k_2235_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_v_2236_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v_l_2120_);
lean_ctor_set(v_reuseFailAlloc_2243_, 4, v_l_2120_);
v___x_2239_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2241_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v_r_2121_);
lean_ctor_set(v___x_2125_, 3, v___x_2239_);
lean_ctor_set(v___x_2125_, 2, v_v_2119_);
lean_ctor_set(v___x_2125_, 1, v_k_2118_);
lean_ctor_set(v___x_2125_, 0, v___x_2237_);
v___x_2241_ = v___x_2125_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2242_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2242_, 3, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2242_, 4, v_r_2121_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_object* v_k_2244_; lean_object* v_v_2245_; lean_object* v___x_2247_; 
v_k_2244_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_k_2244_);
v_v_2245_ = lean_ctor_get(v___x_2127_, 1);
lean_inc(v_v_2245_);
lean_dec_ref(v___x_2127_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 3, v_r_2121_);
v___x_2247_ = v___x_2201_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_size_2117_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_2118_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_2119_);
lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_r_2121_);
lean_ctor_set(v_reuseFailAlloc_2252_, 4, v_r_2121_);
v___x_2247_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = lean_unsigned_to_nat(2u);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v___x_2247_);
lean_ctor_set(v___x_2125_, 3, v_r_2121_);
lean_ctor_set(v___x_2125_, 2, v_v_2245_);
lean_ctor_set(v___x_2125_, 1, v_k_2244_);
lean_ctor_set(v___x_2125_, 0, v___x_2248_);
v___x_2250_ = v___x_2125_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_k_2244_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_v_2245_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_r_2121_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v___x_2247_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2417_; 
lean_inc(v_r_2121_);
lean_inc(v_v_2119_);
lean_inc(v_k_2118_);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; lean_object* v_unused_2421_; lean_object* v_unused_2422_; 
v_unused_2418_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_r_1942_, 2);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_r_1942_, 1);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_r_1942_, 0);
lean_dec(v_unused_2422_);
v___x_2266_ = v_r_1942_;
v_isShared_2267_ = v_isSharedCheck_2417_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v_r_1942_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2417_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v_tree_2269_; 
v___x_2268_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2118_, v_v_2119_, v_l_2120_, v_r_2121_);
v_tree_2269_ = lean_ctor_get(v___x_2268_, 2);
lean_inc(v_tree_2269_);
if (lean_obj_tag(v_tree_2269_) == 0)
{
lean_object* v_k_2270_; lean_object* v_v_2271_; lean_object* v_size_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_k_2270_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_k_2270_);
v_v_2271_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_v_2271_);
lean_dec_ref(v___x_2268_);
v_size_2272_ = lean_ctor_get(v_tree_2269_, 0);
v___x_2273_ = lean_unsigned_to_nat(3u);
v___x_2274_ = lean_nat_mul(v___x_2273_, v_size_2272_);
v___x_2275_ = lean_nat_dec_lt(v___x_2274_, v_size_2112_);
lean_dec(v___x_2274_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
lean_dec(v_r_2116_);
v___x_2276_ = lean_nat_add(v___x_2122_, v_size_2112_);
v___x_2277_ = lean_nat_add(v___x_2276_, v_size_2272_);
lean_dec(v___x_2276_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v_tree_2269_);
lean_ctor_set(v___x_2266_, 3, v_l_1941_);
lean_ctor_set(v___x_2266_, 2, v_v_2271_);
lean_ctor_set(v___x_2266_, 1, v_k_2270_);
lean_ctor_set(v___x_2266_, 0, v___x_2277_);
v___x_2279_ = v___x_2266_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_k_2270_);
lean_ctor_set(v_reuseFailAlloc_2280_, 2, v_v_2271_);
lean_ctor_set(v_reuseFailAlloc_2280_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_2280_, 4, v_tree_2269_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
else
{
lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2346_; 
lean_inc(v_l_2115_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
lean_inc(v_size_2112_);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; lean_object* v_unused_2348_; lean_object* v_unused_2349_; lean_object* v_unused_2350_; lean_object* v_unused_2351_; 
v_unused_2347_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2347_);
v_unused_2348_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2348_);
v_unused_2349_ = lean_ctor_get(v_l_1941_, 2);
lean_dec(v_unused_2349_);
v_unused_2350_ = lean_ctor_get(v_l_1941_, 1);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_l_1941_, 0);
lean_dec(v_unused_2351_);
v___x_2282_ = v_l_1941_;
v_isShared_2283_ = v_isSharedCheck_2346_;
goto v_resetjp_2281_;
}
else
{
lean_dec(v_l_1941_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2346_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v_size_2284_; lean_object* v_size_2285_; lean_object* v_k_2286_; lean_object* v_v_2287_; lean_object* v_l_2288_; lean_object* v_r_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
v_size_2284_ = lean_ctor_get(v_l_2115_, 0);
v_size_2285_ = lean_ctor_get(v_r_2116_, 0);
v_k_2286_ = lean_ctor_get(v_r_2116_, 1);
v_v_2287_ = lean_ctor_get(v_r_2116_, 2);
v_l_2288_ = lean_ctor_get(v_r_2116_, 3);
v_r_2289_ = lean_ctor_get(v_r_2116_, 4);
v___x_2290_ = lean_unsigned_to_nat(2u);
v___x_2291_ = lean_nat_mul(v___x_2290_, v_size_2284_);
v___x_2292_ = lean_nat_dec_lt(v_size_2285_, v___x_2291_);
lean_dec(v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2330_; 
lean_inc(v_r_2289_);
lean_inc(v_l_2288_);
lean_inc(v_v_2287_);
lean_inc(v_k_2286_);
lean_del_object(v___x_2282_);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_r_2116_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; lean_object* v_unused_2332_; lean_object* v_unused_2333_; lean_object* v_unused_2334_; lean_object* v_unused_2335_; 
v_unused_2331_ = lean_ctor_get(v_r_2116_, 4);
lean_dec(v_unused_2331_);
v_unused_2332_ = lean_ctor_get(v_r_2116_, 3);
lean_dec(v_unused_2332_);
v_unused_2333_ = lean_ctor_get(v_r_2116_, 2);
lean_dec(v_unused_2333_);
v_unused_2334_ = lean_ctor_get(v_r_2116_, 1);
lean_dec(v_unused_2334_);
v_unused_2335_ = lean_ctor_get(v_r_2116_, 0);
lean_dec(v_unused_2335_);
v___x_2294_ = v_r_2116_;
v_isShared_2295_ = v_isSharedCheck_2330_;
goto v_resetjp_2293_;
}
else
{
lean_dec(v_r_2116_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2330_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___x_2318_; lean_object* v___y_2320_; 
v___x_2296_ = lean_nat_add(v___x_2122_, v_size_2112_);
lean_dec(v_size_2112_);
v___x_2297_ = lean_nat_add(v___x_2296_, v_size_2272_);
lean_dec(v___x_2296_);
v___x_2318_ = lean_nat_add(v___x_2122_, v_size_2284_);
if (lean_obj_tag(v_l_2288_) == 0)
{
lean_object* v_size_2328_; 
v_size_2328_ = lean_ctor_get(v_l_2288_, 0);
lean_inc(v_size_2328_);
v___y_2320_ = v_size_2328_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_unsigned_to_nat(0u);
v___y_2320_ = v___x_2329_;
goto v___jp_2319_;
}
v___jp_2298_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = lean_nat_add(v___y_2299_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec(v___y_2299_);
lean_inc_ref(v_tree_2269_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 4, v_tree_2269_);
lean_ctor_set(v___x_2294_, 3, v_r_2289_);
lean_ctor_set(v___x_2294_, 2, v_v_2271_);
lean_ctor_set(v___x_2294_, 1, v_k_2270_);
lean_ctor_set(v___x_2294_, 0, v___x_2302_);
v___x_2304_ = v___x_2294_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_k_2270_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_v_2271_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_r_2289_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v_tree_2269_);
v___x_2304_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
v_isSharedCheck_2311_ = !lean_is_exclusive(v_tree_2269_);
if (v_isSharedCheck_2311_ == 0)
{
lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; lean_object* v_unused_2316_; 
v_unused_2312_ = lean_ctor_get(v_tree_2269_, 4);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_tree_2269_, 3);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_tree_2269_, 2);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_tree_2269_, 1);
lean_dec(v_unused_2315_);
v_unused_2316_ = lean_ctor_get(v_tree_2269_, 0);
lean_dec(v_unused_2316_);
v___x_2306_ = v_tree_2269_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_dec(v_tree_2269_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 4, v___x_2304_);
lean_ctor_set(v___x_2306_, 3, v___y_2300_);
lean_ctor_set(v___x_2306_, 2, v_v_2287_);
lean_ctor_set(v___x_2306_, 1, v_k_2286_);
lean_ctor_set(v___x_2306_, 0, v___x_2297_);
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v___y_2300_);
lean_ctor_set(v_reuseFailAlloc_2310_, 4, v___x_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_nat_add(v___x_2318_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec(v___x_2318_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v_l_2288_);
lean_ctor_set(v___x_2266_, 3, v_l_2115_);
lean_ctor_set(v___x_2266_, 2, v_v_2114_);
lean_ctor_set(v___x_2266_, 1, v_k_2113_);
lean_ctor_set(v___x_2266_, 0, v___x_2321_);
v___x_2323_ = v___x_2266_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_l_2115_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_l_2288_);
v___x_2323_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_nat_add(v___x_2122_, v_size_2272_);
if (lean_obj_tag(v_r_2289_) == 0)
{
lean_object* v_size_2325_; 
v_size_2325_ = lean_ctor_get(v_r_2289_, 0);
lean_inc(v_size_2325_);
v___y_2299_ = v___x_2324_;
v___y_2300_ = v___x_2323_;
v___y_2301_ = v_size_2325_;
goto v___jp_2298_;
}
else
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v___y_2299_ = v___x_2324_;
v___y_2300_ = v___x_2323_;
v___y_2301_ = v___x_2326_;
goto v___jp_2298_;
}
}
}
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2336_ = lean_nat_add(v___x_2122_, v_size_2112_);
lean_dec(v_size_2112_);
v___x_2337_ = lean_nat_add(v___x_2336_, v_size_2272_);
lean_dec(v___x_2336_);
v___x_2338_ = lean_nat_add(v___x_2122_, v_size_2272_);
v___x_2339_ = lean_nat_add(v___x_2338_, v_size_2285_);
lean_dec(v___x_2338_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v_tree_2269_);
lean_ctor_set(v___x_2266_, 3, v_r_2116_);
lean_ctor_set(v___x_2266_, 2, v_v_2271_);
lean_ctor_set(v___x_2266_, 1, v_k_2270_);
lean_ctor_set(v___x_2266_, 0, v___x_2339_);
v___x_2341_ = v___x_2266_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_k_2270_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_v_2271_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2345_, 4, v_tree_2269_);
v___x_2341_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 4, v___x_2341_);
lean_ctor_set(v___x_2282_, 0, v___x_2337_);
v___x_2343_ = v___x_2282_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_l_2115_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2115_) == 0)
{
lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2375_; 
lean_inc_ref(v_l_2115_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
lean_inc(v_size_2112_);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; lean_object* v_unused_2377_; lean_object* v_unused_2378_; lean_object* v_unused_2379_; lean_object* v_unused_2380_; 
v_unused_2376_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2376_);
v_unused_2377_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_l_1941_, 2);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_l_1941_, 1);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_l_1941_, 0);
lean_dec(v_unused_2380_);
v___x_2353_ = v_l_1941_;
v_isShared_2354_ = v_isSharedCheck_2375_;
goto v_resetjp_2352_;
}
else
{
lean_dec(v_l_1941_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2375_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
if (lean_obj_tag(v_r_2116_) == 0)
{
lean_object* v_k_2355_; lean_object* v_v_2356_; lean_object* v_size_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v_k_2355_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_k_2355_);
v_v_2356_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_v_2356_);
lean_dec_ref(v___x_2268_);
v_size_2357_ = lean_ctor_get(v_r_2116_, 0);
v___x_2358_ = lean_nat_add(v___x_2122_, v_size_2112_);
lean_dec(v_size_2112_);
v___x_2359_ = lean_nat_add(v___x_2122_, v_size_2357_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v_tree_2269_);
lean_ctor_set(v___x_2266_, 3, v_r_2116_);
lean_ctor_set(v___x_2266_, 2, v_v_2356_);
lean_ctor_set(v___x_2266_, 1, v_k_2355_);
lean_ctor_set(v___x_2266_, 0, v___x_2359_);
v___x_2361_ = v___x_2266_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_k_2355_);
lean_ctor_set(v_reuseFailAlloc_2365_, 2, v_v_2356_);
lean_ctor_set(v_reuseFailAlloc_2365_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2365_, 4, v_tree_2269_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 4, v___x_2361_);
lean_ctor_set(v___x_2353_, 0, v___x_2358_);
v___x_2363_ = v___x_2353_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2364_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2364_, 3, v_l_2115_);
lean_ctor_set(v_reuseFailAlloc_2364_, 4, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
else
{
lean_object* v_k_2366_; lean_object* v_v_2367_; lean_object* v___x_2368_; lean_object* v___x_2370_; 
lean_dec(v_size_2112_);
v_k_2366_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_k_2366_);
v_v_2367_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_v_2367_);
lean_dec_ref(v___x_2268_);
v___x_2368_ = lean_unsigned_to_nat(3u);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v_r_2116_);
lean_ctor_set(v___x_2266_, 3, v_r_2116_);
lean_ctor_set(v___x_2266_, 2, v_v_2367_);
lean_ctor_set(v___x_2266_, 1, v_k_2366_);
lean_ctor_set(v___x_2266_, 0, v___x_2122_);
v___x_2370_ = v___x_2266_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_k_2366_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_v_2367_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v_r_2116_);
v___x_2370_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 4, v___x_2370_);
lean_ctor_set(v___x_2353_, 0, v___x_2368_);
v___x_2372_ = v___x_2353_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_l_2115_);
lean_ctor_set(v_reuseFailAlloc_2373_, 4, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2116_) == 0)
{
lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2405_; 
lean_inc(v_l_2115_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; lean_object* v_unused_2407_; lean_object* v_unused_2408_; lean_object* v_unused_2409_; lean_object* v_unused_2410_; 
v_unused_2406_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_l_1941_, 2);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_l_1941_, 1);
lean_dec(v_unused_2409_);
v_unused_2410_ = lean_ctor_get(v_l_1941_, 0);
lean_dec(v_unused_2410_);
v___x_2382_ = v_l_1941_;
v_isShared_2383_ = v_isSharedCheck_2405_;
goto v_resetjp_2381_;
}
else
{
lean_dec(v_l_1941_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2405_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_k_2384_; lean_object* v_v_2385_; lean_object* v_k_2386_; lean_object* v_v_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2401_; 
v_k_2384_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_k_2384_);
v_v_2385_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_v_2385_);
lean_dec_ref(v___x_2268_);
v_k_2386_ = lean_ctor_get(v_r_2116_, 1);
v_v_2387_ = lean_ctor_get(v_r_2116_, 2);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_r_2116_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; lean_object* v_unused_2403_; lean_object* v_unused_2404_; 
v_unused_2402_ = lean_ctor_get(v_r_2116_, 4);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_r_2116_, 3);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_r_2116_, 0);
lean_dec(v_unused_2404_);
v___x_2389_ = v_r_2116_;
v_isShared_2390_ = v_isSharedCheck_2401_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_v_2387_);
lean_inc(v_k_2386_);
lean_dec(v_r_2116_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2401_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2391_ = lean_unsigned_to_nat(3u);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 4, v_l_2115_);
lean_ctor_set(v___x_2389_, 3, v_l_2115_);
lean_ctor_set(v___x_2389_, 2, v_v_2114_);
lean_ctor_set(v___x_2389_, 1, v_k_2113_);
lean_ctor_set(v___x_2389_, 0, v___x_2122_);
v___x_2393_ = v___x_2389_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_l_2115_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_l_2115_);
v___x_2393_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2395_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v_l_2115_);
lean_ctor_set(v___x_2266_, 3, v_l_2115_);
lean_ctor_set(v___x_2266_, 2, v_v_2385_);
lean_ctor_set(v___x_2266_, 1, v_k_2384_);
lean_ctor_set(v___x_2266_, 0, v___x_2122_);
v___x_2395_ = v___x_2266_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_k_2384_);
lean_ctor_set(v_reuseFailAlloc_2399_, 2, v_v_2385_);
lean_ctor_set(v_reuseFailAlloc_2399_, 3, v_l_2115_);
lean_ctor_set(v_reuseFailAlloc_2399_, 4, v_l_2115_);
v___x_2395_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2397_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v___x_2395_);
lean_ctor_set(v___x_2382_, 3, v___x_2393_);
lean_ctor_set(v___x_2382_, 2, v_v_2387_);
lean_ctor_set(v___x_2382_, 1, v_k_2386_);
lean_ctor_set(v___x_2382_, 0, v___x_2391_);
v___x_2397_ = v___x_2382_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_k_2386_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_v_2387_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
}
else
{
lean_object* v_k_2411_; lean_object* v_v_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v_k_2411_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_k_2411_);
v_v_2412_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_v_2412_);
lean_dec_ref(v___x_2268_);
v___x_2413_ = lean_unsigned_to_nat(2u);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v_r_2116_);
lean_ctor_set(v___x_2266_, 3, v_l_1941_);
lean_ctor_set(v___x_2266_, 2, v_v_2412_);
lean_ctor_set(v___x_2266_, 1, v_k_2411_);
lean_ctor_set(v___x_2266_, 0, v___x_2413_);
v___x_2415_ = v___x_2266_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_k_2411_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_v_2412_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_2416_, 4, v_r_2116_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
}
}
else
{
return v_l_1941_;
}
}
else
{
return v_r_1942_;
}
}
}
else
{
lean_object* v_impl_2423_; lean_object* v___x_2424_; 
v_impl_2423_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1937_, v_l_1941_);
v___x_2424_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2423_) == 0)
{
if (lean_obj_tag(v_r_1942_) == 0)
{
lean_object* v_size_2425_; lean_object* v_size_2426_; lean_object* v_k_2427_; lean_object* v_v_2428_; lean_object* v_l_2429_; lean_object* v_r_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v_size_2425_ = lean_ctor_get(v_impl_2423_, 0);
lean_inc(v_size_2425_);
v_size_2426_ = lean_ctor_get(v_r_1942_, 0);
v_k_2427_ = lean_ctor_get(v_r_1942_, 1);
v_v_2428_ = lean_ctor_get(v_r_1942_, 2);
v_l_2429_ = lean_ctor_get(v_r_1942_, 3);
lean_inc(v_l_2429_);
v_r_2430_ = lean_ctor_get(v_r_1942_, 4);
v___x_2431_ = lean_unsigned_to_nat(3u);
v___x_2432_ = lean_nat_mul(v___x_2431_, v_size_2425_);
v___x_2433_ = lean_nat_dec_lt(v___x_2432_, v_size_2426_);
lean_dec(v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec(v_l_2429_);
v___x_2434_ = lean_nat_add(v___x_2424_, v_size_2425_);
lean_dec(v_size_2425_);
v___x_2435_ = lean_nat_add(v___x_2434_, v_size_2426_);
lean_dec(v___x_2434_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 3, v_impl_2423_);
lean_ctor_set(v___x_1944_, 0, v___x_2435_);
v___x_2437_ = v___x_1944_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2438_, 3, v_impl_2423_);
lean_ctor_set(v_reuseFailAlloc_2438_, 4, v_r_1942_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
else
{
lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2502_; 
lean_inc(v_r_2430_);
lean_inc(v_v_2428_);
lean_inc(v_k_2427_);
lean_inc(v_size_2426_);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; lean_object* v_unused_2504_; lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; 
v_unused_2503_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2503_);
v_unused_2504_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_r_1942_, 2);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_r_1942_, 1);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_r_1942_, 0);
lean_dec(v_unused_2507_);
v___x_2440_ = v_r_1942_;
v_isShared_2441_ = v_isSharedCheck_2502_;
goto v_resetjp_2439_;
}
else
{
lean_dec(v_r_1942_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2502_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_size_2442_; lean_object* v_k_2443_; lean_object* v_v_2444_; lean_object* v_l_2445_; lean_object* v_r_2446_; lean_object* v_size_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v_size_2442_ = lean_ctor_get(v_l_2429_, 0);
v_k_2443_ = lean_ctor_get(v_l_2429_, 1);
v_v_2444_ = lean_ctor_get(v_l_2429_, 2);
v_l_2445_ = lean_ctor_get(v_l_2429_, 3);
v_r_2446_ = lean_ctor_get(v_l_2429_, 4);
v_size_2447_ = lean_ctor_get(v_r_2430_, 0);
v___x_2448_ = lean_unsigned_to_nat(2u);
v___x_2449_ = lean_nat_mul(v___x_2448_, v_size_2447_);
v___x_2450_ = lean_nat_dec_lt(v_size_2442_, v___x_2449_);
lean_dec(v___x_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2478_; 
lean_inc(v_r_2446_);
lean_inc(v_l_2445_);
lean_inc(v_v_2444_);
lean_inc(v_k_2443_);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_l_2429_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; lean_object* v_unused_2480_; lean_object* v_unused_2481_; lean_object* v_unused_2482_; lean_object* v_unused_2483_; 
v_unused_2479_ = lean_ctor_get(v_l_2429_, 4);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_l_2429_, 3);
lean_dec(v_unused_2480_);
v_unused_2481_ = lean_ctor_get(v_l_2429_, 2);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v_l_2429_, 1);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_l_2429_, 0);
lean_dec(v_unused_2483_);
v___x_2452_ = v_l_2429_;
v_isShared_2453_ = v_isSharedCheck_2478_;
goto v_resetjp_2451_;
}
else
{
lean_dec(v_l_2429_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2478_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2468_; 
v___x_2454_ = lean_nat_add(v___x_2424_, v_size_2425_);
lean_dec(v_size_2425_);
v___x_2455_ = lean_nat_add(v___x_2454_, v_size_2426_);
lean_dec(v_size_2426_);
if (lean_obj_tag(v_l_2445_) == 0)
{
lean_object* v_size_2476_; 
v_size_2476_ = lean_ctor_get(v_l_2445_, 0);
lean_inc(v_size_2476_);
v___y_2468_ = v_size_2476_;
goto v___jp_2467_;
}
else
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_unsigned_to_nat(0u);
v___y_2468_ = v___x_2477_;
goto v___jp_2467_;
}
v___jp_2456_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = lean_nat_add(v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec(v___y_2458_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 4, v_r_2430_);
lean_ctor_set(v___x_2452_, 3, v_r_2446_);
lean_ctor_set(v___x_2452_, 2, v_v_2428_);
lean_ctor_set(v___x_2452_, 1, v_k_2427_);
lean_ctor_set(v___x_2452_, 0, v___x_2460_);
v___x_2462_ = v___x_2452_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2466_, 3, v_r_2446_);
lean_ctor_set(v_reuseFailAlloc_2466_, 4, v_r_2430_);
v___x_2462_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2464_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 4, v___x_2462_);
lean_ctor_set(v___x_2440_, 3, v___y_2457_);
lean_ctor_set(v___x_2440_, 2, v_v_2444_);
lean_ctor_set(v___x_2440_, 1, v_k_2443_);
lean_ctor_set(v___x_2440_, 0, v___x_2455_);
v___x_2464_ = v___x_2440_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_k_2443_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_v_2444_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v___y_2457_);
lean_ctor_set(v_reuseFailAlloc_2465_, 4, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
v___jp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = lean_nat_add(v___x_2454_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec(v___x_2454_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_l_2445_);
lean_ctor_set(v___x_1944_, 3, v_impl_2423_);
lean_ctor_set(v___x_1944_, 0, v___x_2469_);
v___x_2471_ = v___x_1944_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_impl_2423_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_l_2445_);
v___x_2471_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_nat_add(v___x_2424_, v_size_2447_);
if (lean_obj_tag(v_r_2446_) == 0)
{
lean_object* v_size_2473_; 
v_size_2473_ = lean_ctor_get(v_r_2446_, 0);
lean_inc(v_size_2473_);
v___y_2457_ = v___x_2471_;
v___y_2458_ = v___x_2472_;
v___y_2459_ = v_size_2473_;
goto v___jp_2456_;
}
else
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_unsigned_to_nat(0u);
v___y_2457_ = v___x_2471_;
v___y_2458_ = v___x_2472_;
v___y_2459_ = v___x_2474_;
goto v___jp_2456_;
}
}
}
}
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
lean_del_object(v___x_1944_);
v___x_2484_ = lean_nat_add(v___x_2424_, v_size_2425_);
lean_dec(v_size_2425_);
v___x_2485_ = lean_nat_add(v___x_2484_, v_size_2426_);
lean_dec(v_size_2426_);
v___x_2486_ = lean_nat_add(v___x_2484_, v_size_2442_);
lean_dec(v___x_2484_);
lean_inc_ref(v_impl_2423_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 4, v_l_2429_);
lean_ctor_set(v___x_2440_, 3, v_impl_2423_);
lean_ctor_set(v___x_2440_, 2, v_v_1940_);
lean_ctor_set(v___x_2440_, 1, v_k_1939_);
lean_ctor_set(v___x_2440_, 0, v___x_2486_);
v___x_2488_ = v___x_2440_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_impl_2423_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_l_2429_);
v___x_2488_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
v_isSharedCheck_2495_ = !lean_is_exclusive(v_impl_2423_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; lean_object* v_unused_2497_; lean_object* v_unused_2498_; lean_object* v_unused_2499_; lean_object* v_unused_2500_; 
v_unused_2496_ = lean_ctor_get(v_impl_2423_, 4);
lean_dec(v_unused_2496_);
v_unused_2497_ = lean_ctor_get(v_impl_2423_, 3);
lean_dec(v_unused_2497_);
v_unused_2498_ = lean_ctor_get(v_impl_2423_, 2);
lean_dec(v_unused_2498_);
v_unused_2499_ = lean_ctor_get(v_impl_2423_, 1);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_impl_2423_, 0);
lean_dec(v_unused_2500_);
v___x_2490_ = v_impl_2423_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_dec(v_impl_2423_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 4, v_r_2430_);
lean_ctor_set(v___x_2490_, 3, v___x_2488_);
lean_ctor_set(v___x_2490_, 2, v_v_2428_);
lean_ctor_set(v___x_2490_, 1, v_k_2427_);
lean_ctor_set(v___x_2490_, 0, v___x_2485_);
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_k_2427_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_v_2428_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_r_2430_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v_size_2508_ = lean_ctor_get(v_impl_2423_, 0);
lean_inc(v_size_2508_);
v___x_2509_ = lean_nat_add(v___x_2424_, v_size_2508_);
lean_dec(v_size_2508_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 3, v_impl_2423_);
lean_ctor_set(v___x_1944_, 0, v___x_2509_);
v___x_2511_ = v___x_1944_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_impl_2423_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_r_1942_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
else
{
if (lean_obj_tag(v_r_1942_) == 0)
{
lean_object* v_l_2513_; 
v_l_2513_ = lean_ctor_get(v_r_1942_, 3);
lean_inc(v_l_2513_);
if (lean_obj_tag(v_l_2513_) == 0)
{
lean_object* v_r_2514_; 
v_r_2514_ = lean_ctor_get(v_r_1942_, 4);
lean_inc(v_r_2514_);
if (lean_obj_tag(v_r_2514_) == 0)
{
lean_object* v_size_2515_; lean_object* v_k_2516_; lean_object* v_v_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2530_; 
v_size_2515_ = lean_ctor_get(v_r_1942_, 0);
v_k_2516_ = lean_ctor_get(v_r_1942_, 1);
v_v_2517_ = lean_ctor_get(v_r_1942_, 2);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; lean_object* v_unused_2532_; 
v_unused_2531_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2532_);
v___x_2519_ = v_r_1942_;
v_isShared_2520_ = v_isSharedCheck_2530_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_v_2517_);
lean_inc(v_k_2516_);
lean_inc(v_size_2515_);
lean_dec(v_r_1942_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2530_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v_size_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2525_; 
v_size_2521_ = lean_ctor_get(v_l_2513_, 0);
v___x_2522_ = lean_nat_add(v___x_2424_, v_size_2515_);
lean_dec(v_size_2515_);
v___x_2523_ = lean_nat_add(v___x_2424_, v_size_2521_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 4, v_l_2513_);
lean_ctor_set(v___x_2519_, 3, v_impl_2423_);
lean_ctor_set(v___x_2519_, 2, v_v_1940_);
lean_ctor_set(v___x_2519_, 1, v_k_1939_);
lean_ctor_set(v___x_2519_, 0, v___x_2523_);
v___x_2525_ = v___x_2519_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_impl_2423_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_l_2513_);
v___x_2525_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
lean_object* v___x_2527_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_r_2514_);
lean_ctor_set(v___x_1944_, 3, v___x_2525_);
lean_ctor_set(v___x_1944_, 2, v_v_2517_);
lean_ctor_set(v___x_1944_, 1, v_k_2516_);
lean_ctor_set(v___x_1944_, 0, v___x_2522_);
v___x_2527_ = v___x_1944_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_k_2516_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_v_2517_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_r_2514_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_k_2533_; lean_object* v_v_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2557_; 
v_k_2533_ = lean_ctor_get(v_r_1942_, 1);
v_v_2534_ = lean_ctor_get(v_r_1942_, 2);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; 
v_unused_2558_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_r_1942_, 0);
lean_dec(v_unused_2560_);
v___x_2536_ = v_r_1942_;
v_isShared_2537_ = v_isSharedCheck_2557_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_v_2534_);
lean_inc(v_k_2533_);
lean_dec(v_r_1942_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2557_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v_k_2538_; lean_object* v_v_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2553_; 
v_k_2538_ = lean_ctor_get(v_l_2513_, 1);
v_v_2539_ = lean_ctor_get(v_l_2513_, 2);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_l_2513_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; lean_object* v_unused_2555_; lean_object* v_unused_2556_; 
v_unused_2554_ = lean_ctor_get(v_l_2513_, 4);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_l_2513_, 3);
lean_dec(v_unused_2555_);
v_unused_2556_ = lean_ctor_get(v_l_2513_, 0);
lean_dec(v_unused_2556_);
v___x_2541_ = v_l_2513_;
v_isShared_2542_ = v_isSharedCheck_2553_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_v_2539_);
lean_inc(v_k_2538_);
lean_dec(v_l_2513_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2553_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = lean_unsigned_to_nat(3u);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 4, v_r_2514_);
lean_ctor_set(v___x_2541_, 3, v_r_2514_);
lean_ctor_set(v___x_2541_, 2, v_v_1940_);
lean_ctor_set(v___x_2541_, 1, v_k_1939_);
lean_ctor_set(v___x_2541_, 0, v___x_2424_);
v___x_2545_ = v___x_2541_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_r_2514_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_r_2514_);
v___x_2545_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 3, v_r_2514_);
lean_ctor_set(v___x_2536_, 0, v___x_2424_);
v___x_2547_ = v___x_2536_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_k_2533_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_v_2534_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v_r_2514_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v_r_2514_);
v___x_2547_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2549_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_2547_);
lean_ctor_set(v___x_1944_, 3, v___x_2545_);
lean_ctor_set(v___x_1944_, 2, v_v_2539_);
lean_ctor_set(v___x_1944_, 1, v_k_2538_);
lean_ctor_set(v___x_1944_, 0, v___x_2543_);
v___x_2549_ = v___x_1944_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_k_2538_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v_v_2539_);
lean_ctor_set(v_reuseFailAlloc_2550_, 3, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2550_, 4, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2561_; 
v_r_2561_ = lean_ctor_get(v_r_1942_, 4);
lean_inc(v_r_2561_);
if (lean_obj_tag(v_r_2561_) == 0)
{
lean_object* v_k_2562_; lean_object* v_v_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2574_; 
v_k_2562_ = lean_ctor_get(v_r_1942_, 1);
v_v_2563_ = lean_ctor_get(v_r_1942_, 2);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; lean_object* v_unused_2576_; lean_object* v_unused_2577_; 
v_unused_2575_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2575_);
v_unused_2576_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2576_);
v_unused_2577_ = lean_ctor_get(v_r_1942_, 0);
lean_dec(v_unused_2577_);
v___x_2565_ = v_r_1942_;
v_isShared_2566_ = v_isSharedCheck_2574_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_v_2563_);
lean_inc(v_k_2562_);
lean_dec(v_r_1942_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2574_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = lean_unsigned_to_nat(3u);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 4, v_l_2513_);
lean_ctor_set(v___x_2565_, 2, v_v_1940_);
lean_ctor_set(v___x_2565_, 1, v_k_1939_);
lean_ctor_set(v___x_2565_, 0, v___x_2424_);
v___x_2569_ = v___x_2565_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2573_, 3, v_l_2513_);
lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_l_2513_);
v___x_2569_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
lean_object* v___x_2571_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_r_2561_);
lean_ctor_set(v___x_1944_, 3, v___x_2569_);
lean_ctor_set(v___x_1944_, 2, v_v_2563_);
lean_ctor_set(v___x_1944_, 1, v_k_2562_);
lean_ctor_set(v___x_1944_, 0, v___x_2567_);
v___x_2571_ = v___x_1944_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v___x_2567_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_k_2562_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_v_2563_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_r_2561_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v_size_2578_; lean_object* v_k_2579_; lean_object* v_v_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2591_; 
v_size_2578_ = lean_ctor_get(v_r_1942_, 0);
v_k_2579_ = lean_ctor_get(v_r_1942_, 1);
v_v_2580_ = lean_ctor_get(v_r_1942_, 2);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; lean_object* v_unused_2593_; 
v_unused_2592_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2593_);
v___x_2582_ = v_r_1942_;
v_isShared_2583_ = v_isSharedCheck_2591_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_v_2580_);
lean_inc(v_k_2579_);
lean_inc(v_size_2578_);
lean_dec(v_r_1942_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2591_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 3, v_r_2561_);
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_size_2578_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_k_2579_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_v_2580_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_r_2561_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_r_2561_);
v___x_2585_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = lean_unsigned_to_nat(2u);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_2585_);
lean_ctor_set(v___x_1944_, 3, v_r_2561_);
lean_ctor_set(v___x_1944_, 0, v___x_2586_);
v___x_2588_ = v___x_1944_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_r_2561_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v___x_2585_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
}
else
{
lean_object* v___x_2595_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 3, v_r_1942_);
lean_ctor_set(v___x_1944_, 0, v___x_2424_);
v___x_2595_ = v___x_1944_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_r_1942_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_r_1942_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
}
else
{
return v_t_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2599_, lean_object* v_t_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2599_, v_t_2600_);
lean_dec(v_k_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object* v_id_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; lean_object* v_receivers_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_st_ref_get(v___y_2608_);
v_receivers_2611_ = lean_ctor_get(v___x_2610_, 7);
lean_inc(v_receivers_2611_);
v___x_2612_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2611_, v_id_2607_);
lean_dec(v_receivers_2611_);
if (lean_obj_tag(v___x_2612_) == 1)
{
lean_object* v_val_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v_val_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_val_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2610_);
lean_ctor_set(v___x_2614_, 1, v_val_2613_);
v___x_2615_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2614_, v___y_2608_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2645_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2645_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2645_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_fst_2620_; lean_object* v_producers_2621_; lean_object* v_waiters_2622_; lean_object* v_capacity_2623_; lean_object* v_size_2624_; lean_object* v_buffer_2625_; lean_object* v_write_2626_; lean_object* v_read_2627_; lean_object* v_receivers_2628_; lean_object* v_nextId_2629_; uint8_t v_closed_2630_; lean_object* v_pos_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2644_; 
v_fst_2620_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_fst_2620_);
lean_dec(v_a_2616_);
v_producers_2621_ = lean_ctor_get(v_fst_2620_, 0);
v_waiters_2622_ = lean_ctor_get(v_fst_2620_, 1);
v_capacity_2623_ = lean_ctor_get(v_fst_2620_, 2);
v_size_2624_ = lean_ctor_get(v_fst_2620_, 3);
v_buffer_2625_ = lean_ctor_get(v_fst_2620_, 4);
v_write_2626_ = lean_ctor_get(v_fst_2620_, 5);
v_read_2627_ = lean_ctor_get(v_fst_2620_, 6);
v_receivers_2628_ = lean_ctor_get(v_fst_2620_, 7);
v_nextId_2629_ = lean_ctor_get(v_fst_2620_, 8);
v_closed_2630_ = lean_ctor_get_uint8(v_fst_2620_, sizeof(void*)*10);
v_pos_2631_ = lean_ctor_get(v_fst_2620_, 9);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_fst_2620_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2633_ = v_fst_2620_;
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_pos_2631_);
lean_inc(v_nextId_2629_);
lean_inc(v_receivers_2628_);
lean_inc(v_read_2627_);
lean_inc(v_write_2626_);
lean_inc(v_buffer_2625_);
lean_inc(v_size_2624_);
lean_inc(v_capacity_2623_);
lean_inc(v_waiters_2622_);
lean_inc(v_producers_2621_);
lean_dec(v_fst_2620_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2635_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_id_2607_, v_receivers_2628_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 7, v___x_2635_);
v___x_2637_ = v___x_2633_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_producers_2621_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_waiters_2622_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_capacity_2623_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_size_2624_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_buffer_2625_);
lean_ctor_set(v_reuseFailAlloc_2643_, 5, v_write_2626_);
lean_ctor_set(v_reuseFailAlloc_2643_, 6, v_read_2627_);
lean_ctor_set(v_reuseFailAlloc_2643_, 7, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2643_, 8, v_nextId_2629_);
lean_ctor_set(v_reuseFailAlloc_2643_, 9, v_pos_2631_);
lean_ctor_set_uint8(v_reuseFailAlloc_2643_, sizeof(void*)*10, v_closed_2630_);
v___x_2637_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2638_ = lean_st_ref_swap(v___y_2608_, v___x_2637_);
lean_dec(v___x_2638_);
v___x_2639_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0));
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2639_);
v___x_2641_ = v___x_2618_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
v_a_2646_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2615_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2615_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec(v___x_2612_);
lean_dec(v___x_2610_);
v___x_2654_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1));
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
return v___x_2655_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object* v_id_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec(v_id_2656_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object* v_bd_2660_){
_start:
{
lean_object* v_state_2662_; lean_object* v_id_2663_; lean_object* v___f_2664_; lean_object* v___x_2665_; 
v_state_2662_ = lean_ctor_get(v_bd_2660_, 0);
lean_inc_ref(v_state_2662_);
v_id_2663_ = lean_ctor_get(v_bd_2660_, 1);
lean_inc(v_id_2663_);
lean_dec_ref(v_bd_2660_);
v___f_2664_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2664_, 0, v_id_2663_);
v___x_2665_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_2662_, v___f_2664_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2690_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2690_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2690_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___y_2671_; 
if (lean_obj_tag(v_a_2666_) == 0)
{
lean_object* v_a_2676_; uint8_t v___x_2677_; 
v_a_2676_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v_a_2666_, 1);
v___x_2677_ = lean_unbox(v_a_2676_);
lean_dec(v_a_2676_);
switch(v___x_2677_)
{
case 0:
{
lean_object* v___x_2678_; 
v___x_2678_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_2671_ = v___x_2678_;
goto v___jp_2670_;
}
case 1:
{
lean_object* v___x_2679_; 
v___x_2679_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_2671_ = v___x_2679_;
goto v___jp_2670_;
}
default: 
{
lean_object* v___x_2680_; 
v___x_2680_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_2671_ = v___x_2680_;
goto v___jp_2670_;
}
}
}
else
{
lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2688_; 
lean_del_object(v___x_2668_);
v_isSharedCheck_2688_ = !lean_is_exclusive(v_a_2666_);
if (v_isSharedCheck_2688_ == 0)
{
lean_object* v_unused_2689_; 
v_unused_2689_ = lean_ctor_get(v_a_2666_, 0);
lean_dec(v_unused_2689_);
v___x_2682_ = v_a_2666_;
v_isShared_2683_ = v_isSharedCheck_2688_;
goto v_resetjp_2681_;
}
else
{
lean_dec(v_a_2666_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2688_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
v___x_2684_ = lean_box(0);
if (v_isShared_2683_ == 0)
{
lean_ctor_set_tag(v___x_2682_, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2684_);
v___x_2686_ = v___x_2682_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
v___jp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2674_; 
lean_inc_ref(v___y_2671_);
v___x_2672_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___y_2671_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 1);
lean_ctor_set(v___x_2668_, 0, v___x_2672_);
v___x_2674_ = v___x_2668_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
v_a_2691_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2665_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2665_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object* v_bd_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2699_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object* v_00_u03b1_2702_, lean_object* v_bd_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_bd_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(v_00_u03b1_2706_, v_bd_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object* v_00_u03b1_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_a_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(v_00_u03b1_2714_, v_a_2715_);
lean_dec(v_a_2715_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object* v_00_u03b1_2718_, lean_object* v_place_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2719_, v_a_2720_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_place_2724_, lean_object* v_a_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(v_00_u03b1_2723_, v_place_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec(v_place_2724_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object* v_00_u03b1_2728_, lean_object* v_slot_2729_, lean_object* v_next_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2729_, v_next_2730_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2734_, lean_object* v_slot_2735_, lean_object* v_next_2736_, lean_object* v_a_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(v_00_u03b1_2734_, v_slot_2735_, v_next_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec(v_next_2736_);
lean_dec(v_slot_2735_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object* v_00_u03b1_2740_, lean_object* v_next_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2741_, v_a_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_next_2746_, lean_object* v_a_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(v_00_u03b1_2745_, v_next_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec(v_next_2746_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object* v_00_u03b4_2750_, lean_object* v_t_2751_, lean_object* v_k_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2751_, v_k_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object* v_00_u03b4_2754_, lean_object* v_t_2755_, lean_object* v_k_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(v_00_u03b4_2754_, v_t_2755_, v_k_2756_);
lean_dec(v_k_2756_);
lean_dec(v_t_2755_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2758_, lean_object* v_inst_2759_, lean_object* v_a_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_2760_, v___y_2761_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2764_, lean_object* v_inst_2765_, lean_object* v_a_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2764_, v_inst_2765_, v_a_2766_, v___y_2767_);
lean_dec(v___y_2767_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2770_, lean_object* v_k_2771_, lean_object* v_t_2772_, lean_object* v_h_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2771_, v_t_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2775_, lean_object* v_k_2776_, lean_object* v_t_2777_, lean_object* v_h_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2775_, v_k_2776_, v_t_2777_, v_h_2778_);
lean_dec(v_k_2776_);
return v_res_2779_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2780_, lean_object* v_y_2781_){
_start:
{
uint8_t v___x_2782_; 
v___x_2782_ = lean_nat_dec_lt(v_x_2780_, v_y_2781_);
if (v___x_2782_ == 0)
{
uint8_t v___x_2783_; 
v___x_2783_ = lean_nat_dec_eq(v_x_2780_, v_y_2781_);
if (v___x_2783_ == 0)
{
uint8_t v___x_2784_; 
v___x_2784_ = 2;
return v___x_2784_;
}
else
{
uint8_t v___x_2785_; 
v___x_2785_ = 1;
return v___x_2785_;
}
}
else
{
uint8_t v___x_2786_; 
v___x_2786_ = 0;
return v___x_2786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2787_, lean_object* v_y_2788_){
_start:
{
uint8_t v_res_2789_; lean_object* v_r_2790_; 
v_res_2789_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2787_, v_y_2788_);
lean_dec(v_y_2788_);
lean_dec(v_x_2787_);
v_r_2790_ = lean_box(v_res_2789_);
return v_r_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2791_){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = lean_unsigned_to_nat(1u);
v___x_2793_ = lean_nat_add(v_x_2791_, v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2794_);
lean_dec(v_x_2794_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2796_, lean_object* v_receiverId_2797_, lean_object* v___f_2798_, lean_object* v_receivers_2799_, lean_object* v_s_2800_){
_start:
{
lean_object* v_producers_2801_; lean_object* v_waiters_2802_; lean_object* v_capacity_2803_; lean_object* v_size_2804_; lean_object* v_buffer_2805_; lean_object* v_write_2806_; lean_object* v_read_2807_; lean_object* v_nextId_2808_; uint8_t v_closed_2809_; lean_object* v_pos_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2820_; 
v_producers_2801_ = lean_ctor_get(v_s_2800_, 0);
v_waiters_2802_ = lean_ctor_get(v_s_2800_, 1);
v_capacity_2803_ = lean_ctor_get(v_s_2800_, 2);
v_size_2804_ = lean_ctor_get(v_s_2800_, 3);
v_buffer_2805_ = lean_ctor_get(v_s_2800_, 4);
v_write_2806_ = lean_ctor_get(v_s_2800_, 5);
v_read_2807_ = lean_ctor_get(v_s_2800_, 6);
v_nextId_2808_ = lean_ctor_get(v_s_2800_, 8);
v_closed_2809_ = lean_ctor_get_uint8(v_s_2800_, sizeof(void*)*10);
v_pos_2810_ = lean_ctor_get(v_s_2800_, 9);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_s_2800_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v_s_2800_, 7);
lean_dec(v_unused_2821_);
v___x_2812_ = v_s_2800_;
v_isShared_2813_ = v_isSharedCheck_2820_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_pos_2810_);
lean_inc(v_nextId_2808_);
lean_inc(v_read_2807_);
lean_inc(v_write_2806_);
lean_inc(v_buffer_2805_);
lean_inc(v_size_2804_);
lean_inc(v_capacity_2803_);
lean_inc(v_waiters_2802_);
lean_inc(v_producers_2801_);
lean_dec(v_s_2800_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2820_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2814_ = lean_box(0);
v___x_2815_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2796_, v_receiverId_2797_, v___f_2798_, v_receivers_2799_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 7, v___x_2815_);
v___x_2817_ = v___x_2812_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_producers_2801_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_waiters_2802_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_capacity_2803_);
lean_ctor_set(v_reuseFailAlloc_2819_, 3, v_size_2804_);
lean_ctor_set(v_reuseFailAlloc_2819_, 4, v_buffer_2805_);
lean_ctor_set(v_reuseFailAlloc_2819_, 5, v_write_2806_);
lean_ctor_set(v_reuseFailAlloc_2819_, 6, v_read_2807_);
lean_ctor_set(v_reuseFailAlloc_2819_, 7, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2819_, 8, v_nextId_2808_);
lean_ctor_set(v_reuseFailAlloc_2819_, 9, v_pos_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2819_, sizeof(void*)*10, v_closed_2809_);
v___x_2817_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2814_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
return v___x_2818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_toPure_2825_; lean_object* v___x_2826_; 
v_toPure_2825_ = lean_ctor_get(v_toApplicative_2822_, 1);
lean_inc(v_toPure_2825_);
lean_dec_ref(v_toApplicative_2822_);
v___x_2826_ = lean_apply_2(v_toPure_2825_, lean_box(0), v_a_2823_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2827_, lean_object* v_a_2828_, lean_object* v___f_2829_, lean_object* v_inst_2830_, lean_object* v_toBind_2831_, lean_object* v_a_2832_){
_start:
{
if (lean_obj_tag(v_a_2832_) == 1)
{
lean_object* v___f_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___f_2833_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2833_, 0, v_toApplicative_2827_);
lean_closure_set(v___f_2833_, 1, v_a_2832_);
lean_inc(v_a_2828_);
v___x_2834_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2834_, 0, lean_box(0));
lean_closure_set(v___x_2834_, 1, lean_box(0));
lean_closure_set(v___x_2834_, 2, lean_box(0));
lean_closure_set(v___x_2834_, 3, v_a_2828_);
lean_closure_set(v___x_2834_, 4, v___f_2829_);
v___x_2835_ = lean_apply_2(v_inst_2830_, lean_box(0), v___x_2834_);
v___x_2836_ = lean_apply_4(v_toBind_2831_, lean_box(0), lean_box(0), v___x_2835_, v___f_2833_);
return v___x_2836_;
}
else
{
lean_object* v_toPure_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec(v_a_2832_);
lean_dec(v_toBind_2831_);
lean_dec(v_inst_2830_);
lean_dec_ref(v___f_2829_);
v_toPure_2837_ = lean_ctor_get(v_toApplicative_2827_, 1);
lean_inc(v_toPure_2837_);
lean_dec_ref(v_toApplicative_2827_);
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_apply_2(v_toPure_2837_, lean_box(0), v___x_2838_);
return v___x_2839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_2840_, lean_object* v_a_2841_, lean_object* v___f_2842_, lean_object* v_inst_2843_, lean_object* v_toBind_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(v_toApplicative_2840_, v_a_2841_, v___f_2842_, v_inst_2843_, v_toBind_2844_, v_a_2845_);
lean_dec(v_a_2841_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2847_, lean_object* v_receiverId_2848_, lean_object* v___f_2849_, lean_object* v___f_2850_, lean_object* v_toApplicative_2851_, lean_object* v_a_2852_, lean_object* v_inst_2853_, lean_object* v_toBind_2854_, lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v_receivers_2858_; lean_object* v___x_2859_; 
v_receivers_2858_ = lean_ctor_get(v_a_2857_, 7);
lean_inc_n(v_receivers_2858_, 2);
lean_dec_ref(v_a_2857_);
lean_inc(v_receiverId_2848_);
v___x_2859_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2847_, v_receivers_2858_, v_receiverId_2848_);
if (lean_obj_tag(v___x_2859_) == 1)
{
lean_object* v_val_2860_; lean_object* v___f_2861_; lean_object* v___f_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_val_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_val_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___f_2861_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2861_, 0, v___f_2849_);
lean_closure_set(v___f_2861_, 1, v_receiverId_2848_);
lean_closure_set(v___f_2861_, 2, v___f_2850_);
lean_closure_set(v___f_2861_, 3, v_receivers_2858_);
lean_inc(v_toBind_2854_);
lean_inc(v_inst_2853_);
lean_inc(v_a_2852_);
v___f_2862_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2862_, 0, v_toApplicative_2851_);
lean_closure_set(v___f_2862_, 1, v_a_2852_);
lean_closure_set(v___f_2862_, 2, v___f_2861_);
lean_closure_set(v___f_2862_, 3, v_inst_2853_);
lean_closure_set(v___f_2862_, 4, v_toBind_2854_);
v___x_2863_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2855_, v_inst_2853_, v_inst_2856_, v_val_2860_, v_a_2852_);
v___x_2864_ = lean_apply_4(v_toBind_2854_, lean_box(0), lean_box(0), v___x_2863_, v___f_2862_);
return v___x_2864_;
}
else
{
lean_object* v_toPure_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_dec(v___x_2859_);
lean_dec(v_receivers_2858_);
lean_dec(v_inst_2856_);
lean_dec_ref(v_inst_2855_);
lean_dec(v_toBind_2854_);
lean_dec(v_inst_2853_);
lean_dec_ref(v___f_2850_);
lean_dec_ref(v___f_2849_);
lean_dec(v_receiverId_2848_);
v_toPure_2865_ = lean_ctor_get(v_toApplicative_2851_, 1);
lean_inc(v_toPure_2865_);
lean_dec_ref(v_toApplicative_2851_);
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_apply_2(v_toPure_2865_, lean_box(0), v___x_2866_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object* v___f_2868_, lean_object* v_receiverId_2869_, lean_object* v___f_2870_, lean_object* v___f_2871_, lean_object* v_toApplicative_2872_, lean_object* v_a_2873_, lean_object* v_inst_2874_, lean_object* v_toBind_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(v___f_2868_, v_receiverId_2869_, v___f_2870_, v___f_2871_, v_toApplicative_2872_, v_a_2873_, v_inst_2874_, v_toBind_2875_, v_inst_2876_, v_inst_2877_, v_a_2878_);
lean_dec(v_a_2873_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_2882_, lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_receiverId_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_toApplicative_2887_; lean_object* v_toBind_2888_; lean_object* v___f_2889_; lean_object* v___f_2890_; lean_object* v___f_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_toApplicative_2887_ = lean_ctor_get(v_inst_2882_, 0);
lean_inc_ref(v_toApplicative_2887_);
v_toBind_2888_ = lean_ctor_get(v_inst_2882_, 1);
lean_inc_n(v_toBind_2888_, 2);
v___f_2889_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_2890_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_inst_2883_);
lean_inc_n(v_a_2886_, 2);
v___f_2891_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_2891_, 0, v___f_2889_);
lean_closure_set(v___f_2891_, 1, v_receiverId_2885_);
lean_closure_set(v___f_2891_, 2, v___f_2889_);
lean_closure_set(v___f_2891_, 3, v___f_2890_);
lean_closure_set(v___f_2891_, 4, v_toApplicative_2887_);
lean_closure_set(v___f_2891_, 5, v_a_2886_);
lean_closure_set(v___f_2891_, 6, v_inst_2883_);
lean_closure_set(v___f_2891_, 7, v_toBind_2888_);
lean_closure_set(v___f_2891_, 8, v_inst_2882_);
lean_closure_set(v___f_2891_, 9, v_inst_2884_);
v___x_2892_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2892_, 0, lean_box(0));
lean_closure_set(v___x_2892_, 1, lean_box(0));
lean_closure_set(v___x_2892_, 2, v_a_2886_);
v___x_2893_ = lean_apply_2(v_inst_2883_, lean_box(0), v___x_2892_);
v___x_2894_ = lean_apply_4(v_toBind_2888_, lean_box(0), lean_box(0), v___x_2893_, v___f_2891_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_receiverId_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2895_, v_inst_2896_, v_inst_2897_, v_receiverId_2898_, v_a_2899_);
lean_dec(v_a_2899_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_2901_, lean_object* v_00_u03b1_2902_, lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_receiverId_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2903_, v_inst_2904_, v_inst_2905_, v_receiverId_2906_, v_a_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object* v_m_2909_, lean_object* v_00_u03b1_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_receiverId_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(v_m_2909_, v_00_u03b1_2910_, v_inst_2911_, v_inst_2912_, v_inst_2913_, v_receiverId_2914_, v_a_2915_);
lean_dec(v_a_2915_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_2917_, lean_object* v_t_2918_){
_start:
{
if (lean_obj_tag(v_t_2918_) == 0)
{
lean_object* v_size_2919_; lean_object* v_k_2920_; lean_object* v_v_2921_; lean_object* v_l_2922_; lean_object* v_r_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2942_; 
v_size_2919_ = lean_ctor_get(v_t_2918_, 0);
v_k_2920_ = lean_ctor_get(v_t_2918_, 1);
v_v_2921_ = lean_ctor_get(v_t_2918_, 2);
v_l_2922_ = lean_ctor_get(v_t_2918_, 3);
v_r_2923_ = lean_ctor_get(v_t_2918_, 4);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_t_2918_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2925_ = v_t_2918_;
v_isShared_2926_ = v_isSharedCheck_2942_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_r_2923_);
lean_inc(v_l_2922_);
lean_inc(v_v_2921_);
lean_inc(v_k_2920_);
lean_inc(v_size_2919_);
lean_dec(v_t_2918_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2942_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_nat_dec_lt(v_k_2917_, v_k_2920_);
if (v___x_2927_ == 0)
{
uint8_t v___x_2928_; 
v___x_2928_ = lean_nat_dec_eq(v_k_2917_, v_k_2920_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2929_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2917_, v_r_2923_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 4, v___x_2929_);
v___x_2931_ = v___x_2925_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_size_2919_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_k_2920_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_v_2921_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_l_2922_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v___x_2929_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
lean_dec(v_k_2920_);
v___x_2933_ = lean_unsigned_to_nat(1u);
v___x_2934_ = lean_nat_add(v_v_2921_, v___x_2933_);
lean_dec(v_v_2921_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 2, v___x_2934_);
lean_ctor_set(v___x_2925_, 1, v_k_2917_);
v___x_2936_ = v___x_2925_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_size_2919_);
lean_ctor_set(v_reuseFailAlloc_2937_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_2937_, 2, v___x_2934_);
lean_ctor_set(v_reuseFailAlloc_2937_, 3, v_l_2922_);
lean_ctor_set(v_reuseFailAlloc_2937_, 4, v_r_2923_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2917_, v_l_2922_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 3, v___x_2938_);
v___x_2940_ = v___x_2925_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_size_2919_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_k_2920_);
lean_ctor_set(v_reuseFailAlloc_2941_, 2, v_v_2921_);
lean_ctor_set(v_reuseFailAlloc_2941_, 3, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2941_, 4, v_r_2923_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
else
{
lean_dec(v_k_2917_);
return v_t_2918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_2943_, lean_object* v_next_2944_){
_start:
{
lean_object* v___x_2946_; lean_object* v_fst_2948_; lean_object* v_snd_2949_; lean_object* v_value_2951_; lean_object* v_pos_2952_; lean_object* v_remaining_2953_; uint8_t v___x_2954_; 
v___x_2946_ = lean_st_ref_take(v_slot_2943_);
v_value_2951_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_value_2951_);
v_pos_2952_ = lean_ctor_get(v___x_2946_, 1);
lean_inc(v_pos_2952_);
v_remaining_2953_ = lean_ctor_get(v___x_2946_, 2);
lean_inc(v_remaining_2953_);
v___x_2954_ = lean_nat_dec_eq(v_next_2944_, v_pos_2952_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec(v_remaining_2953_);
lean_dec(v_pos_2952_);
lean_dec(v_value_2951_);
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_box(v___x_2954_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v_fst_2948_ = v___x_2957_;
v_snd_2949_ = v___x_2946_;
goto v___jp_2947_;
}
else
{
lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2976_; 
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; lean_object* v_unused_2978_; lean_object* v_unused_2979_; 
v_unused_2977_ = lean_ctor_get(v___x_2946_, 2);
lean_dec(v_unused_2977_);
v_unused_2978_ = lean_ctor_get(v___x_2946_, 1);
lean_dec(v_unused_2978_);
v_unused_2979_ = lean_ctor_get(v___x_2946_, 0);
lean_dec(v_unused_2979_);
v___x_2959_ = v___x_2946_;
v_isShared_2960_ = v_isSharedCheck_2976_;
goto v_resetjp_2958_;
}
else
{
lean_dec(v___x_2946_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2976_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = lean_unsigned_to_nat(1u);
v___x_2962_ = lean_nat_dec_eq(v_remaining_2953_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2963_ = lean_box(v___x_2962_);
lean_inc(v_value_2951_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_value_2951_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_nat_sub(v_remaining_2953_, v___x_2961_);
lean_dec(v_remaining_2953_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 2, v___x_2965_);
v___x_2967_ = v___x_2959_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_value_2951_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_pos_2952_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
v_fst_2948_ = v___x_2964_;
v_snd_2949_ = v___x_2967_;
goto v___jp_2947_;
}
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_remaining_2953_);
v___x_2969_ = lean_box(v___x_2954_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_value_2951_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_unsigned_to_nat(0u);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 2, v___x_2972_);
lean_ctor_set(v___x_2959_, 0, v___x_2971_);
v___x_2974_ = v___x_2959_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_pos_2952_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
v_fst_2948_ = v___x_2970_;
v_snd_2949_ = v___x_2974_;
goto v___jp_2947_;
}
}
}
}
v___jp_2947_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_st_ref_put(v_slot_2943_, v_snd_2949_);
return v_fst_2948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_2980_, lean_object* v_next_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_2980_, v_next_2981_);
lean_dec(v_next_2981_);
lean_dec(v_slot_2980_);
return v_res_2983_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_2984_){
_start:
{
lean_object* v___x_2986_; lean_object* v_size_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2986_ = lean_st_ref_get(v_a_2984_);
v_size_2987_ = lean_ctor_get(v___x_2986_, 3);
lean_inc(v_size_2987_);
lean_dec(v___x_2986_);
v___x_2988_ = lean_unsigned_to_nat(0u);
v___x_2989_ = lean_nat_dec_eq(v_size_2987_, v___x_2988_);
lean_dec(v_size_2987_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_2990_, lean_object* v___y_2991_){
_start:
{
uint8_t v_res_2992_; lean_object* v_r_2993_; 
v_res_2992_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_2990_);
lean_dec(v_a_2990_);
v_r_2993_ = lean_box(v_res_2992_);
return v_r_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___x_2997_; lean_object* v_capacity_2998_; lean_object* v_buffer_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2997_ = lean_st_ref_get(v_a_2995_);
v_capacity_2998_ = lean_ctor_get(v___x_2997_, 2);
lean_inc(v_capacity_2998_);
v_buffer_2999_ = lean_ctor_get(v___x_2997_, 4);
lean_inc_ref(v_buffer_2999_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_nat_mod(v_place_2994_, v_capacity_2998_);
lean_dec(v_capacity_2998_);
v___x_3001_ = lean_array_fget(v_buffer_2999_, v___x_3000_);
lean_dec(v___x_3000_);
lean_dec_ref(v_buffer_2999_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_3002_, lean_object* v_a_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3002_, v_a_3003_);
lean_dec(v_a_3003_);
lean_dec(v_place_3002_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = lean_st_ref_get(v_a_3007_);
v___x_3010_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3007_);
if (v___x_3010_ == 0)
{
lean_object* v_capacity_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v_fst_3015_; lean_object* v_snd_3016_; lean_object* v_st_3018_; lean_object* v___y_3019_; 
v_capacity_3011_ = lean_ctor_get(v___x_3009_, 2);
lean_inc(v_capacity_3011_);
v___x_3012_ = lean_nat_mod(v_next_3006_, v_capacity_3011_);
lean_dec(v_capacity_3011_);
v___x_3013_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_3012_, v_a_3007_);
lean_dec(v___x_3012_);
v___x_3014_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_3013_, v_next_3006_);
lean_dec(v___x_3013_);
v_fst_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_fst_3015_);
v_snd_3016_ = lean_ctor_get(v___x_3014_, 1);
lean_inc(v_snd_3016_);
lean_dec_ref(v___x_3014_);
if (lean_obj_tag(v_fst_3015_) == 1)
{
uint8_t v___x_3021_; 
v___x_3021_ = lean_unbox(v_snd_3016_);
if (v___x_3021_ == 0)
{
lean_dec(v_snd_3016_);
v_st_3018_ = v___x_3009_;
v___y_3019_ = v_a_3007_;
goto v___jp_3017_;
}
else
{
lean_object* v___x_3022_; lean_object* v_producers_3023_; lean_object* v_waiters_3024_; lean_object* v_capacity_3025_; lean_object* v_size_3026_; lean_object* v_buffer_3027_; lean_object* v_write_3028_; lean_object* v_read_3029_; lean_object* v_receivers_3030_; lean_object* v_nextId_3031_; uint8_t v_closed_3032_; lean_object* v_pos_3033_; lean_object* v___x_3034_; 
v___x_3022_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_3009_);
v_producers_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc_ref(v_producers_3023_);
v_waiters_3024_ = lean_ctor_get(v___x_3022_, 1);
lean_inc_ref(v_waiters_3024_);
v_capacity_3025_ = lean_ctor_get(v___x_3022_, 2);
lean_inc(v_capacity_3025_);
v_size_3026_ = lean_ctor_get(v___x_3022_, 3);
lean_inc(v_size_3026_);
v_buffer_3027_ = lean_ctor_get(v___x_3022_, 4);
lean_inc_ref(v_buffer_3027_);
v_write_3028_ = lean_ctor_get(v___x_3022_, 5);
lean_inc(v_write_3028_);
v_read_3029_ = lean_ctor_get(v___x_3022_, 6);
lean_inc(v_read_3029_);
v_receivers_3030_ = lean_ctor_get(v___x_3022_, 7);
lean_inc(v_receivers_3030_);
v_nextId_3031_ = lean_ctor_get(v___x_3022_, 8);
lean_inc(v_nextId_3031_);
v_closed_3032_ = lean_ctor_get_uint8(v___x_3022_, sizeof(void*)*10);
v_pos_3033_ = lean_ctor_get(v___x_3022_, 9);
lean_inc(v_pos_3033_);
v___x_3034_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3023_);
if (lean_obj_tag(v___x_3034_) == 1)
{
lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3045_; 
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3045_ == 0)
{
lean_object* v_unused_3046_; lean_object* v_unused_3047_; lean_object* v_unused_3048_; lean_object* v_unused_3049_; lean_object* v_unused_3050_; lean_object* v_unused_3051_; lean_object* v_unused_3052_; lean_object* v_unused_3053_; lean_object* v_unused_3054_; lean_object* v_unused_3055_; 
v_unused_3046_ = lean_ctor_get(v___x_3022_, 9);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v___x_3022_, 8);
lean_dec(v_unused_3047_);
v_unused_3048_ = lean_ctor_get(v___x_3022_, 7);
lean_dec(v_unused_3048_);
v_unused_3049_ = lean_ctor_get(v___x_3022_, 6);
lean_dec(v_unused_3049_);
v_unused_3050_ = lean_ctor_get(v___x_3022_, 5);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v___x_3022_, 4);
lean_dec(v_unused_3051_);
v_unused_3052_ = lean_ctor_get(v___x_3022_, 3);
lean_dec(v_unused_3052_);
v_unused_3053_ = lean_ctor_get(v___x_3022_, 2);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v___x_3022_, 1);
lean_dec(v_unused_3054_);
v_unused_3055_ = lean_ctor_get(v___x_3022_, 0);
lean_dec(v_unused_3055_);
v___x_3036_ = v___x_3022_;
v_isShared_3037_ = v_isSharedCheck_3045_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v___x_3022_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3045_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v_val_3038_; lean_object* v_fst_3039_; lean_object* v_snd_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v_val_3038_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_val_3038_);
lean_dec_ref_known(v___x_3034_, 1);
v_fst_3039_ = lean_ctor_get(v_val_3038_, 0);
lean_inc(v_fst_3039_);
v_snd_3040_ = lean_ctor_get(v_val_3038_, 1);
lean_inc(v_snd_3040_);
lean_dec(v_val_3038_);
v___x_3041_ = lean_io_promise_resolve(v_snd_3016_, v_fst_3039_);
lean_dec(v_fst_3039_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v_snd_3040_);
v___x_3043_ = v___x_3036_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_snd_3040_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v_waiters_3024_);
lean_ctor_set(v_reuseFailAlloc_3044_, 2, v_capacity_3025_);
lean_ctor_set(v_reuseFailAlloc_3044_, 3, v_size_3026_);
lean_ctor_set(v_reuseFailAlloc_3044_, 4, v_buffer_3027_);
lean_ctor_set(v_reuseFailAlloc_3044_, 5, v_write_3028_);
lean_ctor_set(v_reuseFailAlloc_3044_, 6, v_read_3029_);
lean_ctor_set(v_reuseFailAlloc_3044_, 7, v_receivers_3030_);
lean_ctor_set(v_reuseFailAlloc_3044_, 8, v_nextId_3031_);
lean_ctor_set(v_reuseFailAlloc_3044_, 9, v_pos_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3044_, sizeof(void*)*10, v_closed_3032_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
v_st_3018_ = v___x_3043_;
v___y_3019_ = v_a_3007_;
goto v___jp_3017_;
}
}
}
else
{
lean_dec(v___x_3034_);
lean_dec(v_pos_3033_);
lean_dec(v_nextId_3031_);
lean_dec(v_receivers_3030_);
lean_dec(v_read_3029_);
lean_dec(v_write_3028_);
lean_dec_ref(v_buffer_3027_);
lean_dec(v_size_3026_);
lean_dec(v_capacity_3025_);
lean_dec_ref(v_waiters_3024_);
lean_dec(v_snd_3016_);
v_st_3018_ = v___x_3022_;
v___y_3019_ = v_a_3007_;
goto v___jp_3017_;
}
}
}
else
{
lean_object* v___x_3056_; 
lean_dec(v_snd_3016_);
lean_dec(v_fst_3015_);
lean_dec(v___x_3009_);
v___x_3056_ = lean_box(0);
return v___x_3056_;
}
v___jp_3017_:
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_st_ref_swap(v___y_3019_, v_st_3018_);
lean_dec(v___x_3020_);
return v_fst_3015_;
}
}
else
{
lean_object* v___x_3057_; 
lean_dec(v___x_3009_);
v___x_3057_ = lean_box(0);
return v___x_3057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_3058_, lean_object* v_a_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3058_, v_a_3059_);
lean_dec(v_a_3059_);
lean_dec(v_next_3058_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3065_; lean_object* v_receivers_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_st_ref_get(v_a_3063_);
v_receivers_3066_ = lean_ctor_get(v___x_3065_, 7);
lean_inc(v_receivers_3066_);
lean_dec(v___x_3065_);
v___x_3067_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3066_, v_receiverId_3062_);
if (lean_obj_tag(v___x_3067_) == 1)
{
lean_object* v_val_3068_; lean_object* v___x_3069_; 
v_val_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_3068_, v_a_3063_);
lean_dec(v_val_3068_);
if (lean_obj_tag(v___x_3069_) == 1)
{
lean_object* v___x_3070_; lean_object* v_producers_3071_; lean_object* v_waiters_3072_; lean_object* v_capacity_3073_; lean_object* v_size_3074_; lean_object* v_buffer_3075_; lean_object* v_write_3076_; lean_object* v_read_3077_; lean_object* v_nextId_3078_; uint8_t v_closed_3079_; lean_object* v_pos_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3089_; 
v___x_3070_ = lean_st_ref_take(v_a_3063_);
v_producers_3071_ = lean_ctor_get(v___x_3070_, 0);
v_waiters_3072_ = lean_ctor_get(v___x_3070_, 1);
v_capacity_3073_ = lean_ctor_get(v___x_3070_, 2);
v_size_3074_ = lean_ctor_get(v___x_3070_, 3);
v_buffer_3075_ = lean_ctor_get(v___x_3070_, 4);
v_write_3076_ = lean_ctor_get(v___x_3070_, 5);
v_read_3077_ = lean_ctor_get(v___x_3070_, 6);
v_nextId_3078_ = lean_ctor_get(v___x_3070_, 8);
v_closed_3079_ = lean_ctor_get_uint8(v___x_3070_, sizeof(void*)*10);
v_pos_3080_ = lean_ctor_get(v___x_3070_, 9);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3070_, 7);
lean_dec(v_unused_3090_);
v___x_3082_ = v___x_3070_;
v_isShared_3083_ = v_isSharedCheck_3089_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_pos_3080_);
lean_inc(v_nextId_3078_);
lean_inc(v_read_3077_);
lean_inc(v_write_3076_);
lean_inc(v_buffer_3075_);
lean_inc(v_size_3074_);
lean_inc(v_capacity_3073_);
lean_inc(v_waiters_3072_);
lean_inc(v_producers_3071_);
lean_dec(v___x_3070_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3089_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3084_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3062_, v_receivers_3066_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 7, v___x_3084_);
v___x_3086_ = v___x_3082_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_producers_3071_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_waiters_3072_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_capacity_3073_);
lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_size_3074_);
lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_buffer_3075_);
lean_ctor_set(v_reuseFailAlloc_3088_, 5, v_write_3076_);
lean_ctor_set(v_reuseFailAlloc_3088_, 6, v_read_3077_);
lean_ctor_set(v_reuseFailAlloc_3088_, 7, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3088_, 8, v_nextId_3078_);
lean_ctor_set(v_reuseFailAlloc_3088_, 9, v_pos_3080_);
lean_ctor_set_uint8(v_reuseFailAlloc_3088_, sizeof(void*)*10, v_closed_3079_);
v___x_3086_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_st_ref_put(v_a_3063_, v___x_3086_);
return v___x_3069_;
}
}
}
else
{
lean_object* v___x_3091_; 
lean_dec(v___x_3069_);
lean_dec(v_receivers_3066_);
lean_dec(v_receiverId_3062_);
v___x_3091_ = lean_box(0);
return v___x_3091_;
}
}
else
{
lean_object* v___x_3092_; 
lean_dec(v___x_3067_);
lean_dec(v_receivers_3066_);
lean_dec(v_receiverId_3062_);
v___x_3092_ = lean_box(0);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3093_, lean_object* v_a_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3093_, v_a_3094_);
lean_dec(v_a_3094_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3097_, v___y_3098_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3101_, v___y_3102_);
lean_dec(v___y_3102_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3105_){
_start:
{
lean_object* v_state_3107_; lean_object* v_id_3108_; lean_object* v___f_3109_; lean_object* v___x_3110_; 
v_state_3107_ = lean_ctor_get(v_ch_3105_, 0);
lean_inc_ref(v_state_3107_);
v_id_3108_ = lean_ctor_get(v_ch_3105_, 1);
lean_inc(v_id_3108_);
lean_dec_ref(v_ch_3105_);
v___f_3109_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3109_, 0, v_id_3108_);
v___x_3110_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3107_, v___f_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3111_, lean_object* v_a_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3111_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3114_, lean_object* v_ch_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3118_, lean_object* v_ch_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3118_, v_ch_3119_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3122_, lean_object* v_receiverId_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3123_, v_a_3124_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3127_, lean_object* v_receiverId_3128_, lean_object* v_a_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3127_, v_receiverId_3128_, v_a_3129_);
lean_dec(v_a_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3132_, lean_object* v_a_3133_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3133_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3136_, lean_object* v_a_3137_, lean_object* v___y_3138_){
_start:
{
uint8_t v_res_3139_; lean_object* v_r_3140_; 
v_res_3139_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3136_, v_a_3137_);
lean_dec(v_a_3137_);
v_r_3140_ = lean_box(v_res_3139_);
return v_r_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3141_, lean_object* v_place_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3142_, v_a_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3146_, lean_object* v_place_3147_, lean_object* v_a_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3146_, v_place_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec(v_place_3147_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3151_, lean_object* v_slot_3152_, lean_object* v_next_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3152_, v_next_3153_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3157_, lean_object* v_slot_3158_, lean_object* v_next_3159_, lean_object* v_a_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3157_, v_slot_3158_, v_next_3159_, v_a_3160_);
lean_dec(v_a_3160_);
lean_dec(v_next_3159_);
lean_dec(v_slot_3158_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3163_, lean_object* v_next_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3164_, v_a_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3168_, lean_object* v_next_3169_, lean_object* v_a_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3168_, v_next_3169_, v_a_3170_);
lean_dec(v_a_3170_);
lean_dec(v_next_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3173_, lean_object* v_t_3174_){
_start:
{
if (lean_obj_tag(v_t_3174_) == 0)
{
lean_object* v_k_3175_; lean_object* v_l_3176_; lean_object* v_r_3177_; uint8_t v___x_3178_; 
v_k_3175_ = lean_ctor_get(v_t_3174_, 1);
v_l_3176_ = lean_ctor_get(v_t_3174_, 3);
v_r_3177_ = lean_ctor_get(v_t_3174_, 4);
v___x_3178_ = lean_nat_dec_lt(v_k_3173_, v_k_3175_);
if (v___x_3178_ == 0)
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_nat_dec_eq(v_k_3173_, v_k_3175_);
if (v___x_3179_ == 0)
{
v_t_3174_ = v_r_3177_;
goto _start;
}
else
{
return v___x_3179_;
}
}
else
{
v_t_3174_ = v_l_3176_;
goto _start;
}
}
else
{
uint8_t v___x_3182_; 
v___x_3182_ = 0;
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3183_, lean_object* v_t_3184_){
_start:
{
uint8_t v_res_3185_; lean_object* v_r_3186_; 
v_res_3185_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3183_, v_t_3184_);
lean_dec(v_t_3184_);
lean_dec(v_k_3183_);
v_r_3186_ = lean_box(v_res_3185_);
return v_r_3186_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_box(0);
v___x_3188_ = lean_task_pure(v___x_3187_);
return v___x_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3189_, lean_object* v___f_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___x_3193_; lean_object* v_receivers_3194_; uint8_t v___x_3195_; 
v___x_3193_ = lean_st_ref_get(v___y_3191_);
v_receivers_3194_ = lean_ctor_get(v___x_3193_, 7);
lean_inc(v_receivers_3194_);
lean_dec(v___x_3193_);
v___x_3195_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3189_, v_receivers_3194_);
lean_dec(v_receivers_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
lean_dec_ref(v___f_3190_);
lean_dec(v_id_3189_);
v___x_3196_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; 
v___x_3197_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3189_, v___y_3191_);
if (lean_obj_tag(v___x_3197_) == 1)
{
lean_object* v___x_3198_; 
lean_dec_ref(v___f_3190_);
v___x_3198_ = lean_task_pure(v___x_3197_);
return v___x_3198_;
}
else
{
lean_object* v___x_3199_; uint8_t v_closed_3200_; 
lean_dec(v___x_3197_);
v___x_3199_ = lean_st_ref_get(v___y_3191_);
v_closed_3200_ = lean_ctor_get_uint8(v___x_3199_, sizeof(void*)*10);
lean_dec(v___x_3199_);
if (v_closed_3200_ == 0)
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_producers_3203_; lean_object* v_waiters_3204_; lean_object* v_capacity_3205_; lean_object* v_size_3206_; lean_object* v_buffer_3207_; lean_object* v_write_3208_; lean_object* v_read_3209_; lean_object* v_receivers_3210_; lean_object* v_nextId_3211_; uint8_t v_closed_3212_; lean_object* v_pos_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3227_; 
v___x_3201_ = lean_io_promise_new();
v___x_3202_ = lean_st_ref_take(v___y_3191_);
v_producers_3203_ = lean_ctor_get(v___x_3202_, 0);
v_waiters_3204_ = lean_ctor_get(v___x_3202_, 1);
v_capacity_3205_ = lean_ctor_get(v___x_3202_, 2);
v_size_3206_ = lean_ctor_get(v___x_3202_, 3);
v_buffer_3207_ = lean_ctor_get(v___x_3202_, 4);
v_write_3208_ = lean_ctor_get(v___x_3202_, 5);
v_read_3209_ = lean_ctor_get(v___x_3202_, 6);
v_receivers_3210_ = lean_ctor_get(v___x_3202_, 7);
v_nextId_3211_ = lean_ctor_get(v___x_3202_, 8);
v_closed_3212_ = lean_ctor_get_uint8(v___x_3202_, sizeof(void*)*10);
v_pos_3213_ = lean_ctor_get(v___x_3202_, 9);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3215_ = v___x_3202_;
v_isShared_3216_ = v_isSharedCheck_3227_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_pos_3213_);
lean_inc(v_nextId_3211_);
lean_inc(v_receivers_3210_);
lean_inc(v_read_3209_);
lean_inc(v_write_3208_);
lean_inc(v_buffer_3207_);
lean_inc(v_size_3206_);
lean_inc(v_capacity_3205_);
lean_inc(v_waiters_3204_);
lean_inc(v_producers_3203_);
lean_dec(v___x_3202_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3227_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3217_ = lean_box(0);
lean_inc(v___x_3201_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3201_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = l_Std_Queue_enqueue___redArg(v___x_3218_, v_waiters_3204_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 1, v___x_3219_);
v___x_3221_ = v___x_3215_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_producers_3203_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_capacity_3205_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_size_3206_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v_buffer_3207_);
lean_ctor_set(v_reuseFailAlloc_3226_, 5, v_write_3208_);
lean_ctor_set(v_reuseFailAlloc_3226_, 6, v_read_3209_);
lean_ctor_set(v_reuseFailAlloc_3226_, 7, v_receivers_3210_);
lean_ctor_set(v_reuseFailAlloc_3226_, 8, v_nextId_3211_);
lean_ctor_set(v_reuseFailAlloc_3226_, 9, v_pos_3213_);
lean_ctor_set_uint8(v_reuseFailAlloc_3226_, sizeof(void*)*10, v_closed_3212_);
v___x_3221_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3222_ = lean_st_ref_put(v___y_3191_, v___x_3221_);
v___x_3223_ = lean_io_promise_result_opt(v___x_3201_);
lean_dec(v___x_3201_);
v___x_3224_ = lean_unsigned_to_nat(0u);
v___x_3225_ = lean_io_bind_task(v___x_3223_, v___f_3190_, v___x_3224_, v_closed_3200_);
return v___x_3225_;
}
}
}
else
{
lean_object* v___x_3228_; 
lean_dec_ref(v___f_3190_);
v___x_3228_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3229_, lean_object* v___f_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3229_, v___f_3230_, v___y_3231_);
lean_dec(v___y_3231_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3234_, lean_object* v_res_3235_){
_start:
{
if (lean_obj_tag(v_res_3235_) == 0)
{
lean_dec_ref(v_ch_3234_);
goto v___jp_3237_;
}
else
{
lean_object* v_val_3239_; uint8_t v___x_3240_; 
v_val_3239_ = lean_ctor_get(v_res_3235_, 0);
v___x_3240_ = lean_unbox(v_val_3239_);
if (v___x_3240_ == 0)
{
lean_dec_ref(v_ch_3234_);
goto v___jp_3237_;
}
else
{
lean_object* v___x_3241_; 
v___x_3241_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3234_);
return v___x_3241_;
}
}
v___jp_3237_:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3242_, lean_object* v_res_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3242_, v_res_3243_);
lean_dec(v_res_3243_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3246_){
_start:
{
lean_object* v_state_3248_; lean_object* v_id_3249_; lean_object* v___f_3250_; lean_object* v___f_3251_; lean_object* v___x_3252_; 
v_state_3248_ = lean_ctor_get(v_ch_3246_, 0);
lean_inc_ref(v_state_3248_);
v_id_3249_ = lean_ctor_get(v_ch_3246_, 1);
lean_inc(v_id_3249_);
v___f_3250_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3250_, 0, v_ch_3246_);
v___f_3251_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3251_, 0, v_id_3249_);
lean_closure_set(v___f_3251_, 1, v___f_3250_);
v___x_3252_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3248_, v___f_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3256_, lean_object* v_ch_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3260_, lean_object* v_ch_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3260_, v_ch_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3264_, lean_object* v_k_3265_, lean_object* v_t_3266_){
_start:
{
uint8_t v___x_3267_; 
v___x_3267_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3265_, v_t_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3268_, lean_object* v_k_3269_, lean_object* v_t_3270_){
_start:
{
uint8_t v_res_3271_; lean_object* v_r_3272_; 
v_res_3271_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3268_, v_k_3269_, v_t_3270_);
lean_dec(v_t_3270_);
lean_dec(v_k_3269_);
v_r_3272_ = lean_box(v_res_3271_);
return v_r_3272_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_box(0);
v___x_3274_ = lean_task_pure(v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3275_, lean_object* v_ch_3276_, lean_object* v_prio_3277_, lean_object* v_x_3278_){
_start:
{
if (lean_obj_tag(v_x_3278_) == 0)
{
lean_object* v___x_3280_; 
lean_dec(v_prio_3277_);
lean_dec_ref(v_ch_3276_);
lean_dec_ref(v_f_3275_);
v___x_3280_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3280_;
}
else
{
lean_object* v_val_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_val_3281_ = lean_ctor_get(v_x_3278_, 0);
lean_inc(v_val_3281_);
lean_dec_ref_known(v_x_3278_, 1);
lean_inc_ref(v_f_3275_);
v___x_3282_ = lean_apply_2(v_f_3275_, v_val_3281_, lean_box(0));
v___x_3283_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3275_, v_ch_3276_, v_prio_3277_);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3284_, lean_object* v_ch_3285_, lean_object* v_prio_3286_, lean_object* v_x_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3284_, v_ch_3285_, v_prio_3286_, v_x_3287_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3290_, lean_object* v_ch_3291_, lean_object* v_prio_3292_){
_start:
{
lean_object* v___x_3294_; lean_object* v___f_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; 
lean_inc_ref(v_ch_3291_);
v___x_3294_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3291_);
lean_inc(v_prio_3292_);
v___f_3295_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3295_, 0, v_f_3290_);
lean_closure_set(v___f_3295_, 1, v_ch_3291_);
lean_closure_set(v___f_3295_, 2, v_prio_3292_);
v___x_3296_ = 0;
v___x_3297_ = lean_io_bind_task(v___x_3294_, v___f_3295_, v_prio_3292_, v___x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3298_, lean_object* v_ch_3299_, lean_object* v_prio_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3298_, v_ch_3299_, v_prio_3300_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3303_, lean_object* v_f_3304_, lean_object* v_ch_3305_, lean_object* v_prio_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3304_, v_ch_3305_, v_prio_3306_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3309_, lean_object* v_f_3310_, lean_object* v_ch_3311_, lean_object* v_prio_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3309_, v_f_3310_, v_ch_3311_, v_prio_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3315_, lean_object* v_val_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_pos_3318_; lean_object* v_toPure_3319_; uint8_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_pos_3318_ = lean_ctor_get(v_a_3317_, 1);
v_toPure_3319_ = lean_ctor_get(v_toApplicative_3315_, 1);
lean_inc(v_toPure_3319_);
lean_dec_ref(v_toApplicative_3315_);
v___x_3320_ = lean_nat_dec_eq(v_pos_3318_, v_val_3316_);
v___x_3321_ = lean_box(v___x_3320_);
v___x_3322_ = lean_apply_2(v_toPure_3319_, lean_box(0), v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3323_, lean_object* v_val_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3323_, v_val_3324_, v_a_3325_);
lean_dec_ref(v_a_3325_);
lean_dec(v_val_3324_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3327_, lean_object* v_toBind_3328_, lean_object* v___f_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3331_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3331_, 0, lean_box(0));
lean_closure_set(v___x_3331_, 1, lean_box(0));
lean_closure_set(v___x_3331_, 2, v_a_3330_);
v___x_3332_ = lean_apply_2(v_inst_3327_, lean_box(0), v___x_3331_);
v___x_3333_ = lean_apply_4(v_toBind_3328_, lean_box(0), lean_box(0), v___x_3332_, v___f_3329_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3334_, lean_object* v_receiverId_3335_, lean_object* v_toApplicative_3336_, lean_object* v_inst_3337_, lean_object* v_toBind_3338_, lean_object* v_inst_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
uint8_t v_closed_3342_; 
v_closed_3342_ = lean_ctor_get_uint8(v_a_3341_, sizeof(void*)*10);
if (v_closed_3342_ == 0)
{
lean_object* v_capacity_3343_; lean_object* v_size_3344_; lean_object* v_receivers_3345_; lean_object* v___x_3346_; 
v_capacity_3343_ = lean_ctor_get(v_a_3341_, 2);
lean_inc(v_capacity_3343_);
v_size_3344_ = lean_ctor_get(v_a_3341_, 3);
lean_inc(v_size_3344_);
v_receivers_3345_ = lean_ctor_get(v_a_3341_, 7);
lean_inc(v_receivers_3345_);
lean_dec_ref(v_a_3341_);
v___x_3346_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3334_, v_receivers_3345_, v_receiverId_3335_);
if (lean_obj_tag(v___x_3346_) == 1)
{
lean_object* v_val_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v_val_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_val_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___x_3348_ = lean_unsigned_to_nat(0u);
v___x_3349_ = lean_nat_dec_eq(v_size_3344_, v___x_3348_);
lean_dec(v_size_3344_);
if (v___x_3349_ == 0)
{
lean_object* v___f_3350_; lean_object* v___f_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
lean_inc(v_val_3347_);
v___f_3350_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3350_, 0, v_toApplicative_3336_);
lean_closure_set(v___f_3350_, 1, v_val_3347_);
lean_inc(v_toBind_3338_);
lean_inc(v_inst_3337_);
v___f_3351_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3351_, 0, v_inst_3337_);
lean_closure_set(v___f_3351_, 1, v_toBind_3338_);
lean_closure_set(v___f_3351_, 2, v___f_3350_);
v___x_3352_ = lean_nat_mod(v_val_3347_, v_capacity_3343_);
lean_dec(v_capacity_3343_);
lean_dec(v_val_3347_);
v___x_3353_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3339_, v_inst_3337_, v___x_3352_, v_a_3340_);
v___x_3354_ = lean_apply_4(v_toBind_3338_, lean_box(0), lean_box(0), v___x_3353_, v___f_3351_);
return v___x_3354_;
}
else
{
lean_object* v_toPure_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec(v_val_3347_);
lean_dec(v_capacity_3343_);
lean_dec_ref(v_inst_3339_);
lean_dec(v_toBind_3338_);
lean_dec(v_inst_3337_);
v_toPure_3355_ = lean_ctor_get(v_toApplicative_3336_, 1);
lean_inc(v_toPure_3355_);
lean_dec_ref(v_toApplicative_3336_);
v___x_3356_ = lean_box(v_closed_3342_);
v___x_3357_ = lean_apply_2(v_toPure_3355_, lean_box(0), v___x_3356_);
return v___x_3357_;
}
}
else
{
lean_object* v_toPure_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec(v___x_3346_);
lean_dec(v_size_3344_);
lean_dec(v_capacity_3343_);
lean_dec_ref(v_inst_3339_);
lean_dec(v_toBind_3338_);
lean_dec(v_inst_3337_);
v_toPure_3358_ = lean_ctor_get(v_toApplicative_3336_, 1);
lean_inc(v_toPure_3358_);
lean_dec_ref(v_toApplicative_3336_);
v___x_3359_ = lean_box(v_closed_3342_);
v___x_3360_ = lean_apply_2(v_toPure_3358_, lean_box(0), v___x_3359_);
return v___x_3360_;
}
}
else
{
lean_object* v_toPure_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_dec_ref(v_a_3341_);
lean_dec_ref(v_inst_3339_);
lean_dec(v_toBind_3338_);
lean_dec(v_inst_3337_);
lean_dec(v_receiverId_3335_);
lean_dec_ref(v___f_3334_);
v_toPure_3361_ = lean_ctor_get(v_toApplicative_3336_, 1);
lean_inc(v_toPure_3361_);
lean_dec_ref(v_toApplicative_3336_);
v___x_3362_ = lean_box(v_closed_3342_);
v___x_3363_ = lean_apply_2(v_toPure_3361_, lean_box(0), v___x_3362_);
return v___x_3363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object* v___f_3364_, lean_object* v_receiverId_3365_, lean_object* v_toApplicative_3366_, lean_object* v_inst_3367_, lean_object* v_toBind_3368_, lean_object* v_inst_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(v___f_3364_, v_receiverId_3365_, v_toApplicative_3366_, v_inst_3367_, v_toBind_3368_, v_inst_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3373_, lean_object* v_inst_3374_, lean_object* v_receiverId_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_toApplicative_3377_; lean_object* v_toBind_3378_; lean_object* v___f_3379_; lean_object* v___f_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v_toApplicative_3377_ = lean_ctor_get(v_inst_3373_, 0);
lean_inc_ref(v_toApplicative_3377_);
v_toBind_3378_ = lean_ctor_get(v_inst_3373_, 1);
lean_inc_n(v_toBind_3378_, 2);
v___f_3379_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3376_, 2);
lean_inc(v_inst_3374_);
v___f_3380_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3380_, 0, v___f_3379_);
lean_closure_set(v___f_3380_, 1, v_receiverId_3375_);
lean_closure_set(v___f_3380_, 2, v_toApplicative_3377_);
lean_closure_set(v___f_3380_, 3, v_inst_3374_);
lean_closure_set(v___f_3380_, 4, v_toBind_3378_);
lean_closure_set(v___f_3380_, 5, v_inst_3373_);
lean_closure_set(v___f_3380_, 6, v_a_3376_);
v___x_3381_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3381_, 0, lean_box(0));
lean_closure_set(v___x_3381_, 1, lean_box(0));
lean_closure_set(v___x_3381_, 2, v_a_3376_);
v___x_3382_ = lean_apply_2(v_inst_3374_, lean_box(0), v___x_3381_);
v___x_3383_ = lean_apply_4(v_toBind_3378_, lean_box(0), lean_box(0), v___x_3382_, v___f_3380_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_receiverId_3386_, lean_object* v_a_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(v_inst_3384_, v_inst_3385_, v_receiverId_3386_, v_a_3387_);
lean_dec(v_a_3387_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3389_, lean_object* v_00_u03b1_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_inst_3394_, lean_object* v_receiverId_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_toApplicative_3397_; lean_object* v_toBind_3398_; lean_object* v___f_3399_; lean_object* v___f_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_toApplicative_3397_ = lean_ctor_get(v_inst_3391_, 0);
lean_inc_ref(v_toApplicative_3397_);
v_toBind_3398_ = lean_ctor_get(v_inst_3391_, 1);
lean_inc_n(v_toBind_3398_, 2);
v___f_3399_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3396_, 2);
lean_inc(v_inst_3392_);
v___f_3400_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3400_, 0, v___f_3399_);
lean_closure_set(v___f_3400_, 1, v_receiverId_3395_);
lean_closure_set(v___f_3400_, 2, v_toApplicative_3397_);
lean_closure_set(v___f_3400_, 3, v_inst_3392_);
lean_closure_set(v___f_3400_, 4, v_toBind_3398_);
lean_closure_set(v___f_3400_, 5, v_inst_3391_);
lean_closure_set(v___f_3400_, 6, v_a_3396_);
v___x_3401_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3401_, 0, lean_box(0));
lean_closure_set(v___x_3401_, 1, lean_box(0));
lean_closure_set(v___x_3401_, 2, v_a_3396_);
v___x_3402_ = lean_apply_2(v_inst_3392_, lean_box(0), v___x_3401_);
v___x_3403_ = lean_apply_4(v_toBind_3398_, lean_box(0), lean_box(0), v___x_3402_, v___f_3400_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3404_, lean_object* v_00_u03b1_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_inst_3409_, lean_object* v_receiverId_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3404_, v_00_u03b1_3405_, v_inst_3406_, v_inst_3407_, v_inst_3408_, v_inst_3409_, v_receiverId_3410_, v_a_3411_);
lean_dec(v_a_3411_);
lean_dec(v_inst_3409_);
lean_dec(v_inst_3408_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3415_, lean_object* v_lose_3416_){
_start:
{
lean_object* v_finished_3418_; lean_object* v_promise_3419_; lean_object* v___x_3420_; uint8_t v___y_3422_; uint8_t v___x_3430_; 
v_finished_3418_ = lean_ctor_get(v_w_3415_, 0);
v_promise_3419_ = lean_ctor_get(v_w_3415_, 1);
v___x_3420_ = lean_st_ref_take(v_finished_3418_);
v___x_3430_ = lean_unbox(v___x_3420_);
lean_dec(v___x_3420_);
if (v___x_3430_ == 0)
{
uint8_t v___x_3431_; 
v___x_3431_ = 1;
v___y_3422_ = v___x_3431_;
goto v___jp_3421_;
}
else
{
uint8_t v___x_3432_; 
v___x_3432_ = 0;
v___y_3422_ = v___x_3432_;
goto v___jp_3421_;
}
v___jp_3421_:
{
uint8_t v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3423_ = 1;
v___x_3424_ = lean_box(v___x_3423_);
v___x_3425_ = lean_st_ref_put(v_finished_3418_, v___x_3424_);
if (v___y_3422_ == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_apply_1(v_lose_3416_, lean_box(0));
return v___x_3426_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec_ref(v_lose_3416_);
v___x_3427_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3428_ = lean_io_promise_resolve(v___x_3427_, v_promise_3419_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3433_, lean_object* v_lose_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3433_, v_lose_3434_);
lean_dec_ref(v_w_3433_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3437_, lean_object* v_w_3438_, lean_object* v_lose_3439_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3438_, v_lose_3439_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3442_, lean_object* v_w_3443_, lean_object* v_lose_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3442_, v_w_3443_, v_lose_3444_);
lean_dec_ref(v_w_3443_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v___x_3450_; lean_object* v_receivers_3451_; lean_object* v___x_3452_; 
v___x_3450_ = lean_st_ref_get(v_a_3448_);
v_receivers_3451_ = lean_ctor_get(v___x_3450_, 7);
lean_inc(v_receivers_3451_);
lean_dec(v___x_3450_);
v___x_3452_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3451_, v_receiverId_3447_);
if (lean_obj_tag(v___x_3452_) == 1)
{
lean_object* v_val_3453_; lean_object* v___x_3454_; 
v_val_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_val_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3454_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3453_, v_a_3448_);
lean_dec(v_val_3453_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3487_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3487_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3487_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
if (lean_obj_tag(v_a_3455_) == 1)
{
lean_object* v___x_3459_; lean_object* v_producers_3460_; lean_object* v_waiters_3461_; lean_object* v_capacity_3462_; lean_object* v_size_3463_; lean_object* v_buffer_3464_; lean_object* v_write_3465_; lean_object* v_read_3466_; lean_object* v_nextId_3467_; uint8_t v_closed_3468_; lean_object* v_pos_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3481_; 
v___x_3459_ = lean_st_ref_take(v_a_3448_);
v_producers_3460_ = lean_ctor_get(v___x_3459_, 0);
v_waiters_3461_ = lean_ctor_get(v___x_3459_, 1);
v_capacity_3462_ = lean_ctor_get(v___x_3459_, 2);
v_size_3463_ = lean_ctor_get(v___x_3459_, 3);
v_buffer_3464_ = lean_ctor_get(v___x_3459_, 4);
v_write_3465_ = lean_ctor_get(v___x_3459_, 5);
v_read_3466_ = lean_ctor_get(v___x_3459_, 6);
v_nextId_3467_ = lean_ctor_get(v___x_3459_, 8);
v_closed_3468_ = lean_ctor_get_uint8(v___x_3459_, sizeof(void*)*10);
v_pos_3469_ = lean_ctor_get(v___x_3459_, 9);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; 
v_unused_3482_ = lean_ctor_get(v___x_3459_, 7);
lean_dec(v_unused_3482_);
v___x_3471_ = v___x_3459_;
v_isShared_3472_ = v_isSharedCheck_3481_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_pos_3469_);
lean_inc(v_nextId_3467_);
lean_inc(v_read_3466_);
lean_inc(v_write_3465_);
lean_inc(v_buffer_3464_);
lean_inc(v_size_3463_);
lean_inc(v_capacity_3462_);
lean_inc(v_waiters_3461_);
lean_inc(v_producers_3460_);
lean_dec(v___x_3459_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3481_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3473_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3447_, v_receivers_3451_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 7, v___x_3473_);
v___x_3475_ = v___x_3471_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_producers_3460_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_waiters_3461_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_capacity_3462_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_size_3463_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_buffer_3464_);
lean_ctor_set(v_reuseFailAlloc_3480_, 5, v_write_3465_);
lean_ctor_set(v_reuseFailAlloc_3480_, 6, v_read_3466_);
lean_ctor_set(v_reuseFailAlloc_3480_, 7, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3480_, 8, v_nextId_3467_);
lean_ctor_set(v_reuseFailAlloc_3480_, 9, v_pos_3469_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, sizeof(void*)*10, v_closed_3468_);
v___x_3475_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_st_ref_put(v_a_3448_, v___x_3475_);
if (v_isShared_3458_ == 0)
{
v___x_3478_ = v___x_3457_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3455_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
lean_dec(v_a_3455_);
lean_dec(v_receivers_3451_);
lean_dec(v_receiverId_3447_);
v___x_3483_ = lean_box(0);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3483_);
v___x_3485_ = v___x_3457_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_dec(v_receivers_3451_);
lean_dec(v_receiverId_3447_);
return v___x_3454_;
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec(v___x_3452_);
lean_dec(v_receivers_3451_);
lean_dec(v_receiverId_3447_);
v___x_3488_ = lean_box(0);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3490_, lean_object* v_a_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3490_, v_a_3491_);
lean_dec(v_a_3491_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3494_, lean_object* v_w_3495_, lean_object* v_lose_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_finished_3499_; lean_object* v_promise_3500_; lean_object* v___x_3501_; uint8_t v___y_3503_; uint8_t v___x_3527_; 
v_finished_3499_ = lean_ctor_get(v_w_3495_, 0);
v_promise_3500_ = lean_ctor_get(v_w_3495_, 1);
v___x_3501_ = lean_st_ref_take(v_finished_3499_);
v___x_3527_ = lean_unbox(v___x_3501_);
lean_dec(v___x_3501_);
if (v___x_3527_ == 0)
{
uint8_t v___x_3528_; 
v___x_3528_ = 1;
v___y_3503_ = v___x_3528_;
goto v___jp_3502_;
}
else
{
uint8_t v___x_3529_; 
v___x_3529_ = 0;
v___y_3503_ = v___x_3529_;
goto v___jp_3502_;
}
v___jp_3502_:
{
uint8_t v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = 1;
v___x_3505_ = lean_box(v___x_3504_);
v___x_3506_ = lean_st_ref_put(v_finished_3499_, v___x_3505_);
if (v___y_3503_ == 0)
{
lean_object* v___x_3507_; 
lean_dec(v___x_3494_);
lean_inc(v___y_3497_);
v___x_3507_ = lean_apply_2(v_lose_3496_, v___y_3497_, lean_box(0));
return v___x_3507_;
}
else
{
lean_object* v___x_3508_; 
lean_dec_ref(v_lose_3496_);
v___x_3508_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3494_, v___y_3497_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3518_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3511_ = v___x_3508_;
v_isShared_3512_ = v_isSharedCheck_3518_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3518_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3513_, 0, v_a_3509_);
v___x_3514_ = lean_io_promise_resolve(v___x_3513_, v_promise_3500_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3514_);
v___x_3516_ = v___x_3511_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
v_a_3519_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3508_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3508_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3530_, lean_object* v_w_3531_, lean_object* v_lose_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3530_, v_w_3531_, v_lose_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v_w_3531_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3536_, lean_object* v___x_3537_, lean_object* v_w_3538_, lean_object* v_lose_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3537_, v_w_3538_, v_lose_3539_, v___y_3540_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3543_, lean_object* v___x_3544_, lean_object* v_w_3545_, lean_object* v_lose_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3543_, v___x_3544_, v_w_3545_, v_lose_3546_, v___y_3547_);
lean_dec(v___y_3547_);
lean_dec_ref(v_w_3545_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3553_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3556_, lean_object* v___f_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; uint8_t v_closed_3561_; 
v___x_3560_ = lean_st_ref_get(v___y_3558_);
v_closed_3561_ = lean_ctor_get_uint8(v___x_3560_, sizeof(void*)*10);
if (v_closed_3561_ == 0)
{
lean_object* v_capacity_3562_; lean_object* v_size_3563_; lean_object* v_receivers_3564_; lean_object* v___x_3565_; 
v_capacity_3562_ = lean_ctor_get(v___x_3560_, 2);
lean_inc(v_capacity_3562_);
v_size_3563_ = lean_ctor_get(v___x_3560_, 3);
lean_inc(v_size_3563_);
v_receivers_3564_ = lean_ctor_get(v___x_3560_, 7);
lean_inc(v_receivers_3564_);
lean_dec(v___x_3560_);
v___x_3565_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3564_, v_id_3556_);
lean_dec(v_receivers_3564_);
if (lean_obj_tag(v___x_3565_) == 1)
{
lean_object* v_val_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v_val_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_val_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v___x_3567_ = lean_unsigned_to_nat(0u);
v___x_3568_ = lean_nat_dec_eq(v_size_3563_, v___x_3567_);
lean_dec(v_size_3563_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = lean_nat_mod(v_val_3566_, v_capacity_3562_);
lean_dec(v_capacity_3562_);
v___x_3570_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3569_, v___y_3558_);
lean_dec(v___x_3569_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; lean_object* v_pos_3573_; uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
v___x_3572_ = lean_st_ref_get(v_a_3571_);
lean_dec(v_a_3571_);
v_pos_3573_ = lean_ctor_get(v___x_3572_, 1);
lean_inc(v_pos_3573_);
lean_dec(v___x_3572_);
v___x_3574_ = lean_nat_dec_eq(v_pos_3573_, v_val_3566_);
lean_dec(v_val_3566_);
lean_dec(v_pos_3573_);
v___x_3575_ = lean_box(v___x_3574_);
lean_inc(v___y_3558_);
v___x_3576_ = lean_apply_3(v___f_3557_, v___x_3575_, v___y_3558_, lean_box(0));
return v___x_3576_;
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_val_3566_);
lean_dec_ref(v___f_3557_);
v_a_3577_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3570_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3570_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec(v_val_3566_);
lean_dec(v_capacity_3562_);
v___x_3585_ = lean_box(v_closed_3561_);
lean_inc(v___y_3558_);
v___x_3586_ = lean_apply_3(v___f_3557_, v___x_3585_, v___y_3558_, lean_box(0));
return v___x_3586_;
}
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec(v___x_3565_);
lean_dec(v_size_3563_);
lean_dec(v_capacity_3562_);
v___x_3587_ = lean_box(v_closed_3561_);
lean_inc(v___y_3558_);
v___x_3588_ = lean_apply_3(v___f_3557_, v___x_3587_, v___y_3558_, lean_box(0));
return v___x_3588_;
}
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
lean_dec(v___x_3560_);
v___x_3589_ = lean_box(v_closed_3561_);
lean_inc(v___y_3558_);
v___x_3590_ = lean_apply_3(v___f_3557_, v___x_3589_, v___y_3558_, lean_box(0));
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3591_, lean_object* v___f_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3591_, v___f_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec(v_id_3591_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v___x_3599_; lean_object* v_producers_3600_; lean_object* v_waiters_3601_; lean_object* v_capacity_3602_; lean_object* v_size_3603_; lean_object* v_buffer_3604_; lean_object* v_write_3605_; lean_object* v_read_3606_; lean_object* v_receivers_3607_; lean_object* v_nextId_3608_; uint8_t v_closed_3609_; lean_object* v_pos_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3633_; 
v___x_3599_ = lean_st_ref_get(v___y_3597_);
v_producers_3600_ = lean_ctor_get(v___x_3599_, 0);
v_waiters_3601_ = lean_ctor_get(v___x_3599_, 1);
v_capacity_3602_ = lean_ctor_get(v___x_3599_, 2);
v_size_3603_ = lean_ctor_get(v___x_3599_, 3);
v_buffer_3604_ = lean_ctor_get(v___x_3599_, 4);
v_write_3605_ = lean_ctor_get(v___x_3599_, 5);
v_read_3606_ = lean_ctor_get(v___x_3599_, 6);
v_receivers_3607_ = lean_ctor_get(v___x_3599_, 7);
v_nextId_3608_ = lean_ctor_get(v___x_3599_, 8);
v_closed_3609_ = lean_ctor_get_uint8(v___x_3599_, sizeof(void*)*10);
v_pos_3610_ = lean_ctor_get(v___x_3599_, 9);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3612_ = v___x_3599_;
v_isShared_3613_ = v_isSharedCheck_3633_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_pos_3610_);
lean_inc(v_nextId_3608_);
lean_inc(v_receivers_3607_);
lean_inc(v_read_3606_);
lean_inc(v_write_3605_);
lean_inc(v_buffer_3604_);
lean_inc(v_size_3603_);
lean_inc(v_capacity_3602_);
lean_inc(v_waiters_3601_);
lean_inc(v_producers_3600_);
lean_dec(v___x_3599_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3633_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3601_);
if (lean_obj_tag(v___x_3614_) == 1)
{
lean_object* v_val_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3630_; 
v_val_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3630_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_val_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3630_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v_fst_3619_; lean_object* v_snd_3620_; lean_object* v___x_3621_; lean_object* v___x_3623_; 
v_fst_3619_ = lean_ctor_get(v_val_3615_, 0);
lean_inc(v_fst_3619_);
v_snd_3620_ = lean_ctor_get(v_val_3615_, 1);
lean_inc(v_snd_3620_);
lean_dec(v_val_3615_);
v___x_3621_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3619_, v_____do__lift_3596_);
lean_dec(v_fst_3619_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v_snd_3620_);
v___x_3623_ = v___x_3612_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_producers_3600_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_snd_3620_);
lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_capacity_3602_);
lean_ctor_set(v_reuseFailAlloc_3629_, 3, v_size_3603_);
lean_ctor_set(v_reuseFailAlloc_3629_, 4, v_buffer_3604_);
lean_ctor_set(v_reuseFailAlloc_3629_, 5, v_write_3605_);
lean_ctor_set(v_reuseFailAlloc_3629_, 6, v_read_3606_);
lean_ctor_set(v_reuseFailAlloc_3629_, 7, v_receivers_3607_);
lean_ctor_set(v_reuseFailAlloc_3629_, 8, v_nextId_3608_);
lean_ctor_set(v_reuseFailAlloc_3629_, 9, v_pos_3610_);
lean_ctor_set_uint8(v_reuseFailAlloc_3629_, sizeof(void*)*10, v_closed_3609_);
v___x_3623_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
v___x_3624_ = lean_st_ref_swap(v___y_3597_, v___x_3623_);
lean_dec(v___x_3624_);
v___x_3625_ = lean_box(0);
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3625_);
v___x_3627_ = v___x_3617_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
lean_dec(v___x_3614_);
lean_del_object(v___x_3612_);
lean_dec(v_pos_3610_);
lean_dec(v_nextId_3608_);
lean_dec(v_receivers_3607_);
lean_dec(v_read_3606_);
lean_dec(v_write_3605_);
lean_dec_ref(v_buffer_3604_);
lean_dec(v_size_3603_);
lean_dec(v_capacity_3602_);
lean_dec_ref(v_producers_3600_);
v___x_3631_ = lean_box(0);
v___x_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
return v___x_3632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
uint8_t v_____do__lift_3755__boxed_3637_; lean_object* v_res_3638_; 
v_____do__lift_3755__boxed_3637_ = lean_unbox(v_____do__lift_3634_);
v_res_3638_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3755__boxed_3637_, v___y_3635_);
lean_dec(v___y_3635_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3639_, lean_object* v___f_3640_, lean_object* v_id_3641_, uint8_t v_____do__lift_3642_, lean_object* v___y_3643_){
_start:
{
if (v_____do__lift_3642_ == 0)
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_producers_3647_; lean_object* v_waiters_3648_; lean_object* v_capacity_3649_; lean_object* v_size_3650_; lean_object* v_buffer_3651_; lean_object* v_write_3652_; lean_object* v_read_3653_; lean_object* v_receivers_3654_; lean_object* v_nextId_3655_; uint8_t v_closed_3656_; lean_object* v_pos_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_id_3641_);
v___x_3645_ = lean_io_promise_new();
v___x_3646_ = lean_st_ref_take(v___y_3643_);
v_producers_3647_ = lean_ctor_get(v___x_3646_, 0);
v_waiters_3648_ = lean_ctor_get(v___x_3646_, 1);
v_capacity_3649_ = lean_ctor_get(v___x_3646_, 2);
v_size_3650_ = lean_ctor_get(v___x_3646_, 3);
v_buffer_3651_ = lean_ctor_get(v___x_3646_, 4);
v_write_3652_ = lean_ctor_get(v___x_3646_, 5);
v_read_3653_ = lean_ctor_get(v___x_3646_, 6);
v_receivers_3654_ = lean_ctor_get(v___x_3646_, 7);
v_nextId_3655_ = lean_ctor_get(v___x_3646_, 8);
v_closed_3656_ = lean_ctor_get_uint8(v___x_3646_, sizeof(void*)*10);
v_pos_3657_ = lean_ctor_get(v___x_3646_, 9);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3659_ = v___x_3646_;
v_isShared_3660_ = v_isSharedCheck_3671_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_pos_3657_);
lean_inc(v_nextId_3655_);
lean_inc(v_receivers_3654_);
lean_inc(v_read_3653_);
lean_inc(v_write_3652_);
lean_inc(v_buffer_3651_);
lean_inc(v_size_3650_);
lean_inc(v_capacity_3649_);
lean_inc(v_waiters_3648_);
lean_inc(v_producers_3647_);
lean_dec(v___x_3646_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3671_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_waiter_3639_);
lean_inc(v___x_3645_);
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3645_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = l_Std_Queue_enqueue___redArg(v___x_3662_, v_waiters_3648_);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 1, v___x_3663_);
v___x_3665_ = v___x_3659_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_producers_3647_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_capacity_3649_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_size_3650_);
lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_buffer_3651_);
lean_ctor_set(v_reuseFailAlloc_3670_, 5, v_write_3652_);
lean_ctor_set(v_reuseFailAlloc_3670_, 6, v_read_3653_);
lean_ctor_set(v_reuseFailAlloc_3670_, 7, v_receivers_3654_);
lean_ctor_set(v_reuseFailAlloc_3670_, 8, v_nextId_3655_);
lean_ctor_set(v_reuseFailAlloc_3670_, 9, v_pos_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3670_, sizeof(void*)*10, v_closed_3656_);
v___x_3665_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3666_ = lean_st_ref_put(v___y_3643_, v___x_3665_);
v___x_3667_ = lean_io_promise_result_opt(v___x_3645_);
lean_dec(v___x_3645_);
v___x_3668_ = lean_unsigned_to_nat(0u);
v___x_3669_ = l_EIO_chainTask___redArg(v___x_3667_, v___f_3640_, v___x_3668_, v_____do__lift_3642_);
return v___x_3669_;
}
}
}
else
{
lean_object* v___x_3672_; lean_object* v_lose_3673_; lean_object* v___x_3674_; 
lean_dec_ref(v___f_3640_);
v___x_3672_ = lean_box(v_____do__lift_3642_);
v_lose_3673_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3673_, 0, v___x_3672_);
v___x_3674_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3641_, v_waiter_3639_, v_lose_3673_, v___y_3643_);
lean_dec_ref(v_waiter_3639_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3675_, lean_object* v___f_3676_, lean_object* v_id_3677_, lean_object* v_____do__lift_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
uint8_t v_____do__lift_3813__boxed_3681_; lean_object* v_res_3682_; 
v_____do__lift_3813__boxed_3681_ = lean_unbox(v_____do__lift_3678_);
v_res_3682_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3675_, v___f_3676_, v_id_3677_, v_____do__lift_3813__boxed_3681_, v___y_3679_);
lean_dec(v___y_3679_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3685_, lean_object* v_ch_3686_, lean_object* v_res_x3f_3687_){
_start:
{
if (lean_obj_tag(v_res_x3f_3687_) == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_dec_ref(v_ch_3686_);
lean_dec_ref(v_waiter_3685_);
v___x_3689_ = lean_box(0);
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
return v___x_3690_;
}
else
{
lean_object* v_val_3691_; uint8_t v___x_3692_; 
v_val_3691_ = lean_ctor_get(v_res_x3f_3687_, 0);
v___x_3692_ = lean_unbox(v_val_3691_);
if (v___x_3692_ == 0)
{
lean_object* v___f_3693_; lean_object* v___x_3694_; 
lean_dec_ref(v_ch_3686_);
v___f_3693_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3694_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3685_, v___f_3693_);
lean_dec_ref(v_waiter_3685_);
return v___x_3694_;
}
else
{
lean_object* v___x_3695_; 
v___x_3695_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3686_, v_waiter_3685_);
return v___x_3695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3696_, lean_object* v_ch_3697_, lean_object* v_res_x3f_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v_res_3700_; 
v_res_3700_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3696_, v_ch_3697_, v_res_x3f_3698_);
lean_dec(v_res_x3f_3698_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3701_, lean_object* v_waiter_3702_){
_start:
{
lean_object* v_state_3704_; lean_object* v_id_3705_; lean_object* v___f_3706_; lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___x_3709_; 
v_state_3704_ = lean_ctor_get(v_ch_3701_, 0);
lean_inc_ref(v_state_3704_);
v_id_3705_ = lean_ctor_get(v_ch_3701_, 1);
lean_inc_n(v_id_3705_, 2);
lean_inc_ref(v_waiter_3702_);
v___f_3706_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3706_, 0, v_waiter_3702_);
lean_closure_set(v___f_3706_, 1, v_ch_3701_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3707_, 0, v_waiter_3702_);
lean_closure_set(v___f_3707_, 1, v___f_3706_);
lean_closure_set(v___f_3707_, 2, v_id_3705_);
v___f_3708_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3708_, 0, v_id_3705_);
lean_closure_set(v___f_3708_, 1, v___f_3707_);
v___x_3709_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3704_, v___f_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3710_, lean_object* v_waiter_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3710_, v_waiter_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3714_, lean_object* v_ch_3715_, lean_object* v_waiter_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3715_, v_waiter_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3719_, lean_object* v_ch_3720_, lean_object* v_waiter_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3719_, v_ch_3720_, v_waiter_3721_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3724_, lean_object* v_receiverId_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3725_, v_a_3726_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3729_, lean_object* v_receiverId_3730_, lean_object* v_a_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3729_, v_receiverId_3730_, v_a_3731_);
lean_dec(v_a_3731_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3734_, lean_object* v_x_3735_){
_start:
{
if (lean_obj_tag(v_x_3735_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3745_; 
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
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3758_; 
v_a_3746_ = lean_ctor_get(v_x_3735_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_x_3735_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3748_ = v_x_3735_;
v_isShared_3749_ = v_isSharedCheck_3758_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v_x_3735_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3758_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v_capacity_3750_; lean_object* v_buffer_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v_capacity_3750_ = lean_ctor_get(v_a_3746_, 2);
lean_inc(v_capacity_3750_);
v_buffer_3751_ = lean_ctor_get(v_a_3746_, 4);
lean_inc_ref(v_buffer_3751_);
lean_dec(v_a_3746_);
v___x_3752_ = lean_nat_mod(v_place_3734_, v_capacity_3750_);
lean_dec(v_capacity_3750_);
v___x_3753_ = lean_array_fget(v_buffer_3751_, v___x_3752_);
lean_dec(v___x_3752_);
lean_dec_ref(v_buffer_3751_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3753_);
v___x_3755_ = v___x_3748_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
return v___x_3756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3759_, lean_object* v_x_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3759_, v_x_3760_);
lean_dec(v_place_3759_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3763_, lean_object* v_a_3764_){
_start:
{
lean_object* v___x_3766_; lean_object* v___f_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; lean_object* v___x_3772_; 
v___x_3766_ = lean_st_ref_get(v_a_3764_);
v___f_3767_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3767_, 0, v_place_3763_);
v___x_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
v___x_3770_ = lean_unsigned_to_nat(0u);
v___x_3771_ = 0;
v___x_3772_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3770_, v___x_3771_, v___x_3769_, v___f_3767_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3773_, lean_object* v_a_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3773_, v_a_3774_);
lean_dec(v_a_3774_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3777_, lean_object* v_place_3778_, lean_object* v_a_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3778_, v_a_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3782_, lean_object* v_place_3783_, lean_object* v_a_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3782_, v_place_3783_, v_a_3784_);
lean_dec(v_a_3784_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_3787_, lean_object* v_x_3788_){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_io_basemutex_unlock(v_mutex_3787_);
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_3793_, lean_object* v_x_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(v_mutex_3793_, v_x_3794_);
lean_dec(v_x_3794_);
lean_dec(v_mutex_3793_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_3797_, lean_object* v_ref_3798_, lean_object* v_x_3799_){
_start:
{
if (lean_obj_tag(v_x_3799_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3809_; 
lean_dec(v_ref_3798_);
lean_dec_ref(v_k_3797_);
v_a_3801_ = lean_ctor_get(v_x_3799_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_x_3799_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3803_ = v_x_3799_;
v_isShared_3804_ = v_isSharedCheck_3809_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v_x_3799_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3809_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3807_; 
v___x_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
return v___x_3807_;
}
}
}
else
{
lean_object* v___x_3810_; 
lean_dec_ref_known(v_x_3799_, 1);
v___x_3810_ = lean_apply_2(v_k_3797_, v_ref_3798_, lean_box(0));
return v___x_3810_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_3811_, lean_object* v_ref_3812_, lean_object* v_x_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_k_3811_, v_ref_3812_, v_x_3813_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_3816_, lean_object* v___f_3817_){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; lean_object* v___x_3824_; 
v___x_3819_ = lean_io_basemutex_lock(v_mutex_3816_);
v___x_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
v___x_3822_ = lean_unsigned_to_nat(0u);
v___x_3823_ = 0;
v___x_3824_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3822_, v___x_3823_, v___x_3821_, v___f_3817_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_3825_, lean_object* v___f_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_mutex_3825_, v___f_3826_);
lean_dec(v_mutex_3825_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_3829_){
_start:
{
if (lean_obj_tag(v___y_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
v_a_3830_ = lean_ctor_get(v___y_3829_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___y_3829_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___y_3829_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___y_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3846_; 
v_a_3838_ = lean_ctor_get(v___y_3829_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___y_3829_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3840_ = v___y_3829_;
v_isShared_3841_ = v_isSharedCheck_3846_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___y_3829_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3846_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_fst_3842_; lean_object* v___x_3844_; 
v_fst_3842_ = lean_ctor_get(v_a_3838_, 0);
lean_inc(v_fst_3842_);
lean_dec(v_a_3838_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_fst_3842_);
v___x_3844_ = v___x_3840_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_fst_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_3848_, lean_object* v_k_3849_){
_start:
{
lean_object* v_ref_3851_; lean_object* v_mutex_3852_; lean_object* v___f_3853_; lean_object* v___f_3854_; lean_object* v___f_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___y_3860_; 
v_ref_3851_ = lean_ctor_get(v_mutex_3848_, 0);
lean_inc(v_ref_3851_);
v_mutex_3852_ = lean_ctor_get(v_mutex_3848_, 1);
lean_inc_n(v_mutex_3852_, 2);
lean_dec_ref(v_mutex_3848_);
v___f_3853_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3853_, 0, v_mutex_3852_);
v___f_3854_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3854_, 0, v_k_3849_);
lean_closure_set(v___f_3854_, 1, v_ref_3851_);
v___f_3855_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3855_, 0, v_mutex_3852_);
lean_closure_set(v___f_3855_, 1, v___f_3854_);
v___x_3856_ = lean_unsigned_to_nat(0u);
v___x_3857_ = 0;
v___x_3858_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_3855_, v___f_3853_, v___x_3856_, v___x_3857_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3862_; 
v_a_3862_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___x_3858_, 1);
if (lean_obj_tag(v_a_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
v_a_3863_ = lean_ctor_get(v_a_3862_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_a_3862_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v_a_3862_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v_a_3862_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
v___y_3860_ = v___x_3868_;
goto v___jp_3859_;
}
}
}
else
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3879_; 
v_a_3871_ = lean_ctor_get(v_a_3862_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v_a_3862_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3873_ = v_a_3862_;
v_isShared_3874_ = v_isSharedCheck_3879_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v_a_3862_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3879_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v_fst_3875_; lean_object* v___x_3877_; 
v_fst_3875_ = lean_ctor_get(v_a_3871_, 0);
lean_inc(v_fst_3875_);
lean_dec(v_a_3871_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 0, v_fst_3875_);
v___x_3877_ = v___x_3873_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_fst_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
v___y_3860_ = v___x_3877_;
goto v___jp_3859_;
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3889_; 
v_a_3880_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3882_ = v___x_3858_;
v_isShared_3883_ = v_isSharedCheck_3889_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3858_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3889_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___f_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___f_3884_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___x_3885_ = lean_task_map(v___f_3884_, v_a_3880_, v___x_3856_, v___x_3857_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 0, v___x_3885_);
v___x_3887_ = v___x_3882_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
v___jp_3859_:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___y_3860_);
return v___x_3861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_3890_, lean_object* v_k_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3890_, v_k_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_3894_, lean_object* v_00_u03b2_3895_, lean_object* v_mutex_3896_, lean_object* v_k_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3896_, v_k_3897_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_3900_, lean_object* v_00_u03b2_3901_, lean_object* v_mutex_3902_, lean_object* v_k_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_3900_, v_00_u03b2_3901_, v_mutex_3902_, v_k_3903_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_3910_, lean_object* v_capacity_3911_, lean_object* v_size_3912_, lean_object* v_buffer_3913_, lean_object* v_write_3914_, lean_object* v_read_3915_, lean_object* v_receivers_3916_, lean_object* v_nextId_3917_, uint8_t v_closed_3918_, lean_object* v_pos_3919_, lean_object* v___y_3920_, lean_object* v_x_3921_){
_start:
{
if (lean_obj_tag(v_x_3921_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v_pos_3919_);
lean_dec(v_nextId_3917_);
lean_dec(v_receivers_3916_);
lean_dec(v_read_3915_);
lean_dec(v_write_3914_);
lean_dec_ref(v_buffer_3913_);
lean_dec(v_size_3912_);
lean_dec(v_capacity_3911_);
lean_dec_ref(v_producers_3910_);
v_a_3923_ = lean_ctor_get(v_x_3921_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_x_3921_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3925_ = v_x_3921_;
v_isShared_3926_ = v_isSharedCheck_3931_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v_x_3921_);
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
lean_object* v_a_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_a_3932_ = lean_ctor_get(v_x_3921_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v_x_3921_, 1);
v___x_3933_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3933_, 0, v_producers_3910_);
lean_ctor_set(v___x_3933_, 1, v_a_3932_);
lean_ctor_set(v___x_3933_, 2, v_capacity_3911_);
lean_ctor_set(v___x_3933_, 3, v_size_3912_);
lean_ctor_set(v___x_3933_, 4, v_buffer_3913_);
lean_ctor_set(v___x_3933_, 5, v_write_3914_);
lean_ctor_set(v___x_3933_, 6, v_read_3915_);
lean_ctor_set(v___x_3933_, 7, v_receivers_3916_);
lean_ctor_set(v___x_3933_, 8, v_nextId_3917_);
lean_ctor_set(v___x_3933_, 9, v_pos_3919_);
lean_ctor_set_uint8(v___x_3933_, sizeof(void*)*10, v_closed_3918_);
v___x_3934_ = lean_st_ref_swap(v___y_3920_, v___x_3933_);
lean_dec(v___x_3934_);
v___x_3935_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_3936_, lean_object* v_capacity_3937_, lean_object* v_size_3938_, lean_object* v_buffer_3939_, lean_object* v_write_3940_, lean_object* v_read_3941_, lean_object* v_receivers_3942_, lean_object* v_nextId_3943_, lean_object* v_closed_3944_, lean_object* v_pos_3945_, lean_object* v___y_3946_, lean_object* v_x_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v_closed_boxed_3949_; lean_object* v_res_3950_; 
v_closed_boxed_3949_ = lean_unbox(v_closed_3944_);
v_res_3950_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_3936_, v_capacity_3937_, v_size_3938_, v_buffer_3939_, v_write_3940_, v_read_3941_, v_receivers_3942_, v_nextId_3943_, v_closed_boxed_3949_, v_pos_3945_, v___y_3946_, v_x_3947_);
lean_dec(v___y_3946_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_3951_){
_start:
{
if (lean_obj_tag(v_x_3951_) == 0)
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v_x_3951_);
return v___x_3953_;
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3963_; 
v_a_3954_ = lean_ctor_get(v_x_3951_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_x_3951_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3956_ = v_x_3951_;
v_isShared_3957_ = v_isSharedCheck_3963_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v_x_3951_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3963_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3958_ = l_List_reverse___redArg(v_a_3954_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v___x_3958_);
v___x_3960_ = v___x_3956_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3958_);
v___x_3960_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
return v___x_3961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_3964_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_3967_, lean_object* v___x_3968_, lean_object* v_x_3969_){
_start:
{
if (lean_obj_tag(v_x_3969_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v___x_3968_);
lean_dec(v_a_3967_);
v_a_3971_ = lean_ctor_get(v_x_3969_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v_x_3969_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3973_ = v_x_3969_;
v_isShared_3974_ = v_isSharedCheck_3979_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v_x_3969_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3979_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; 
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
return v___x_3977_;
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3996_; 
v_a_3980_ = lean_ctor_get(v_x_3969_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_x_3969_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3982_ = v_x_3969_;
v_isShared_3983_ = v_isSharedCheck_3996_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v_x_3969_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3996_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
uint8_t v___x_3984_; 
v___x_3984_ = l_List_isEmpty___redArg(v_a_3967_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
lean_dec(v___x_3968_);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v_a_3980_);
lean_ctor_set(v___x_3985_, 1, v_a_3967_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3985_);
v___x_3987_ = v___x_3982_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
return v___x_3988_;
}
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
lean_dec(v_a_3967_);
v___x_3990_ = l_List_reverse___redArg(v_a_3980_);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3968_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3991_);
v___x_3993_ = v___x_3982_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3991_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_3997_, lean_object* v___x_3998_, lean_object* v_x_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_3997_, v___x_3998_, v_x_3999_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_4002_){
_start:
{
uint8_t v___y_4005_; 
if (lean_obj_tag(v_x_4002_) == 0)
{
lean_object* v___x_4009_; 
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v_x_4002_);
return v___x_4009_;
}
else
{
lean_object* v_a_4010_; uint8_t v___x_4011_; 
v_a_4010_ = lean_ctor_get(v_x_4002_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v_x_4002_, 1);
v___x_4011_ = lean_unbox(v_a_4010_);
lean_dec(v_a_4010_);
if (v___x_4011_ == 0)
{
uint8_t v___x_4012_; 
v___x_4012_ = 1;
v___y_4005_ = v___x_4012_;
goto v___jp_4004_;
}
else
{
uint8_t v___x_4013_; 
v___x_4013_ = 0;
v___y_4005_ = v___x_4013_;
goto v___jp_4004_;
}
}
v___jp_4004_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = lean_box(v___y_4005_);
v___x_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
return v___x_4008_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4014_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_4017_, lean_object* v_x_4018_, lean_object* v_head_4019_, lean_object* v_x_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4017_, v_x_4018_, v_head_4019_, v_x_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_4029_, lean_object* v_x_4030_){
_start:
{
if (lean_obj_tag(v_x_4029_) == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v_x_4030_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
else
{
lean_object* v_head_4034_; lean_object* v_tail_4035_; lean_object* v_waiter_4036_; lean_object* v___f_4037_; lean_object* v_val_4039_; 
v_head_4034_ = lean_ctor_get(v_x_4029_, 0);
lean_inc(v_head_4034_);
v_tail_4035_ = lean_ctor_get(v_x_4029_, 1);
lean_inc(v_tail_4035_);
lean_dec_ref_known(v_x_4029_, 2);
v_waiter_4036_ = lean_ctor_get(v_head_4034_, 1);
lean_inc(v_waiter_4036_);
v___f_4037_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4037_, 0, v_tail_4035_);
lean_closure_set(v___f_4037_, 1, v_x_4030_);
lean_closure_set(v___f_4037_, 2, v_head_4034_);
if (lean_obj_tag(v_waiter_4036_) == 0)
{
lean_object* v___x_4043_; 
v___x_4043_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v_val_4039_ = v___x_4043_;
goto v___jp_4038_;
}
else
{
lean_object* v_val_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4058_; 
v_val_4044_ = lean_ctor_get(v_waiter_4036_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_waiter_4036_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4046_ = v_waiter_4036_;
v_isShared_4047_ = v_isSharedCheck_4058_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_val_4044_);
lean_dec(v_waiter_4036_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4058_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v_finished_4048_; lean_object* v___x_4049_; lean_object* v___f_4050_; lean_object* v___x_4052_; 
v_finished_4048_ = lean_ctor_get(v_val_4044_, 0);
lean_inc(v_finished_4048_);
lean_dec(v_val_4044_);
v___x_4049_ = lean_st_ref_get(v_finished_4048_);
lean_dec(v_finished_4048_);
v___f_4050_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 0, v___x_4049_);
v___x_4052_ = v___x_4046_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4049_);
v___x_4052_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; lean_object* v___x_4056_; 
v___x_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
v___x_4054_ = lean_unsigned_to_nat(0u);
v___x_4055_ = 0;
v___x_4056_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4054_, v___x_4055_, v___x_4053_, v___f_4050_);
v_val_4039_ = v___x_4056_;
goto v___jp_4038_;
}
}
}
v___jp_4038_:
{
lean_object* v___x_4040_; uint8_t v___x_4041_; lean_object* v___x_4042_; 
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = 0;
v___x_4042_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4040_, v___x_4041_, v_val_4039_, v___f_4037_);
return v___x_4042_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_4059_, lean_object* v_x_4060_, lean_object* v_head_4061_, lean_object* v_x_4062_){
_start:
{
if (lean_obj_tag(v_x_4062_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v_head_4061_);
lean_dec(v_x_4060_);
lean_dec(v_tail_4059_);
v_a_4064_ = lean_ctor_get(v_x_4062_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v_x_4062_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4066_ = v_x_4062_;
v_isShared_4067_ = v_isSharedCheck_4072_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v_x_4062_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4072_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; 
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
return v___x_4070_;
}
}
}
else
{
lean_object* v_a_4073_; uint8_t v___x_4074_; 
v_a_4073_ = lean_ctor_get(v_x_4062_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v_x_4062_, 1);
v___x_4074_ = lean_unbox(v_a_4073_);
lean_dec(v_a_4073_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; 
lean_dec_ref(v_head_4061_);
v___x_4075_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4059_, v_x_4060_);
return v___x_4075_;
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4076_, 0, v_head_4061_);
lean_ctor_set(v___x_4076_, 1, v_x_4060_);
v___x_4077_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4059_, v___x_4076_);
return v___x_4077_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_4078_, lean_object* v_x_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4078_, v_x_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_4082_, lean_object* v___x_4083_, lean_object* v___f_4084_, lean_object* v_x_4085_){
_start:
{
if (lean_obj_tag(v_x_4085_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4095_; 
lean_dec_ref(v___f_4084_);
lean_dec(v___x_4083_);
lean_dec(v_eList_4082_);
v_a_4087_ = lean_ctor_get(v_x_4085_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_x_4085_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4089_ = v_x_4085_;
v_isShared_4090_ = v_isSharedCheck_4095_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v_x_4085_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4095_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
return v___x_4093_;
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; lean_object* v___f_4101_; lean_object* v___x_4102_; 
v_a_4096_ = lean_ctor_get(v_x_4085_, 0);
lean_inc(v_a_4096_);
lean_dec_ref_known(v_x_4085_, 1);
lean_inc(v___x_4083_);
v___x_4097_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4082_, v___x_4083_);
v___x_4098_ = lean_unsigned_to_nat(0u);
v___x_4099_ = 0;
v___x_4100_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4098_, v___x_4099_, v___x_4097_, v___f_4084_);
v___f_4101_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4101_, 0, v_a_4096_);
lean_closure_set(v___f_4101_, 1, v___x_4083_);
v___x_4102_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4098_, v___x_4099_, v___x_4100_, v___f_4101_);
return v___x_4102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_4103_, lean_object* v___x_4104_, lean_object* v___f_4105_, lean_object* v_x_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v_eList_4103_, v___x_4104_, v___f_4105_, v_x_4106_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_eList_4113_; lean_object* v_dList_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___f_4117_; lean_object* v___x_4118_; uint8_t v___x_4119_; lean_object* v___x_4120_; lean_object* v___f_4121_; lean_object* v___x_4122_; 
v_eList_4113_ = lean_ctor_get(v_q_4110_, 0);
lean_inc(v_eList_4113_);
v_dList_4114_ = lean_ctor_get(v_q_4110_, 1);
lean_inc(v_dList_4114_);
lean_dec_ref(v_q_4110_);
v___x_4115_ = lean_box(0);
v___x_4116_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4114_, v___x_4115_);
v___f_4117_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4118_ = lean_unsigned_to_nat(0u);
v___x_4119_ = 0;
v___x_4120_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4118_, v___x_4119_, v___x_4116_, v___f_4117_);
v___f_4121_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4121_, 0, v_eList_4113_);
lean_closure_set(v___f_4121_, 1, v___x_4115_);
lean_closure_set(v___f_4121_, 2, v___f_4117_);
v___x_4122_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4118_, v___x_4119_, v___x_4120_, v___f_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4123_, v___y_4124_);
lean_dec(v___y_4124_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4127_, lean_object* v_x_4128_){
_start:
{
if (lean_obj_tag(v_x_4128_) == 0)
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4138_; 
v_a_4130_ = lean_ctor_get(v_x_4128_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_x_4128_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4132_ = v_x_4128_;
v_isShared_4133_ = v_isSharedCheck_4138_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v_x_4128_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4138_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
lean_object* v___x_4136_; 
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v_producers_4140_; lean_object* v_waiters_4141_; lean_object* v_capacity_4142_; lean_object* v_size_4143_; lean_object* v_buffer_4144_; lean_object* v_write_4145_; lean_object* v_read_4146_; lean_object* v_receivers_4147_; lean_object* v_nextId_4148_; uint8_t v_closed_4149_; lean_object* v_pos_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___f_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; lean_object* v___x_4156_; 
v_a_4139_ = lean_ctor_get(v_x_4128_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v_x_4128_, 1);
v_producers_4140_ = lean_ctor_get(v_a_4139_, 0);
lean_inc_ref(v_producers_4140_);
v_waiters_4141_ = lean_ctor_get(v_a_4139_, 1);
lean_inc_ref(v_waiters_4141_);
v_capacity_4142_ = lean_ctor_get(v_a_4139_, 2);
lean_inc(v_capacity_4142_);
v_size_4143_ = lean_ctor_get(v_a_4139_, 3);
lean_inc(v_size_4143_);
v_buffer_4144_ = lean_ctor_get(v_a_4139_, 4);
lean_inc_ref(v_buffer_4144_);
v_write_4145_ = lean_ctor_get(v_a_4139_, 5);
lean_inc(v_write_4145_);
v_read_4146_ = lean_ctor_get(v_a_4139_, 6);
lean_inc(v_read_4146_);
v_receivers_4147_ = lean_ctor_get(v_a_4139_, 7);
lean_inc(v_receivers_4147_);
v_nextId_4148_ = lean_ctor_get(v_a_4139_, 8);
lean_inc(v_nextId_4148_);
v_closed_4149_ = lean_ctor_get_uint8(v_a_4139_, sizeof(void*)*10);
v_pos_4150_ = lean_ctor_get(v_a_4139_, 9);
lean_inc(v_pos_4150_);
lean_dec(v_a_4139_);
v___x_4151_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4141_, v___y_4127_);
v___x_4152_ = lean_box(v_closed_4149_);
lean_inc(v___y_4127_);
v___f_4153_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4153_, 0, v_producers_4140_);
lean_closure_set(v___f_4153_, 1, v_capacity_4142_);
lean_closure_set(v___f_4153_, 2, v_size_4143_);
lean_closure_set(v___f_4153_, 3, v_buffer_4144_);
lean_closure_set(v___f_4153_, 4, v_write_4145_);
lean_closure_set(v___f_4153_, 5, v_read_4146_);
lean_closure_set(v___f_4153_, 6, v_receivers_4147_);
lean_closure_set(v___f_4153_, 7, v_nextId_4148_);
lean_closure_set(v___f_4153_, 8, v___x_4152_);
lean_closure_set(v___f_4153_, 9, v_pos_4150_);
lean_closure_set(v___f_4153_, 10, v___y_4127_);
v___x_4154_ = lean_unsigned_to_nat(0u);
v___x_4155_ = 0;
v___x_4156_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4154_, v___x_4155_, v___x_4151_, v___f_4153_);
return v___x_4156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4157_, lean_object* v_x_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4157_, v_x_4158_);
lean_dec(v___y_4157_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4161_){
_start:
{
lean_object* v___x_4163_; lean_object* v___f_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; uint8_t v___x_4168_; lean_object* v___x_4169_; 
v___x_4163_ = lean_st_ref_get(v___y_4161_);
lean_inc(v___y_4161_);
v___f_4164_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4164_, 0, v___y_4161_);
v___x_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
v___x_4167_ = lean_unsigned_to_nat(0u);
v___x_4168_ = 0;
v___x_4169_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4167_, v___x_4168_, v___x_4166_, v___f_4164_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4170_);
lean_dec(v___y_4170_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4173_, lean_object* v_waiter_4174_){
_start:
{
lean_object* v_val_4177_; lean_object* v___x_4179_; 
v___x_4179_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4173_, v_waiter_4174_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
lean_ctor_set_tag(v___x_4182_, 1);
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
v_val_4177_ = v___x_4185_;
goto v___jp_4176_;
}
}
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
v_a_4188_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v___x_4179_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4179_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
lean_ctor_set_tag(v___x_4190_, 0);
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
v_val_4177_ = v___x_4193_;
goto v___jp_4176_;
}
}
}
v___jp_4176_:
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v_val_4177_);
return v___x_4178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4196_, lean_object* v_waiter_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4196_, v_waiter_4197_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4200_){
_start:
{
if (lean_obj_tag(v_x_4200_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4210_; 
v_a_4202_ = lean_ctor_get(v_x_4200_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v_x_4200_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4204_ = v_x_4200_;
v_isShared_4205_ = v_isSharedCheck_4210_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v_x_4200_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4210_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
lean_object* v___x_4208_; 
v___x_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
return v___x_4208_;
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4220_; 
v_a_4211_ = lean_ctor_get(v_x_4200_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v_x_4200_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4213_ = v_x_4200_;
v_isShared_4214_ = v_isSharedCheck_4220_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v_x_4200_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4220_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_a_4211_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4215_);
v___x_4217_ = v___x_4213_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
lean_object* v___x_4218_; 
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
return v___x_4218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4221_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_val_4224_, lean_object* v_x_4225_){
_start:
{
if (lean_obj_tag(v_x_4225_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4235_; 
v_a_4227_ = lean_ctor_get(v_x_4225_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v_x_4225_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4229_ = v_x_4225_;
v_isShared_4230_ = v_isSharedCheck_4235_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v_x_4225_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4235_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
lean_object* v___x_4233_; 
v___x_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
return v___x_4233_;
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4247_; 
v_a_4236_ = lean_ctor_get(v_x_4225_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v_x_4225_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4238_ = v_x_4225_;
v_isShared_4239_ = v_isSharedCheck_4247_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v_x_4225_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4247_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v_pos_4240_; uint8_t v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4244_; 
v_pos_4240_ = lean_ctor_get(v_a_4236_, 1);
lean_inc(v_pos_4240_);
lean_dec(v_a_4236_);
v___x_4241_ = lean_nat_dec_eq(v_pos_4240_, v_val_4224_);
lean_dec(v_pos_4240_);
v___x_4242_ = lean_box(v___x_4241_);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v___x_4242_);
v___x_4244_ = v___x_4238_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
return v___x_4245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_val_4248_, lean_object* v_x_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_val_4248_, v_x_4249_);
lean_dec(v_val_4248_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v___x_4252_, uint8_t v_closed_4253_, lean_object* v___f_4254_, lean_object* v_x_4255_){
_start:
{
if (lean_obj_tag(v_x_4255_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4265_; 
lean_dec_ref(v___f_4254_);
lean_dec(v___x_4252_);
v_a_4257_ = lean_ctor_get(v_x_4255_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v_x_4255_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4259_ = v_x_4255_;
v_isShared_4260_ = v_isSharedCheck_4265_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v_x_4255_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4265_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4262_);
return v___x_4263_;
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4276_; 
v_a_4266_ = lean_ctor_get(v_x_4255_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_x_4255_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4268_ = v_x_4255_;
v_isShared_4269_ = v_isSharedCheck_4276_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v_x_4255_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4276_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4270_; lean_object* v___x_4272_; 
v___x_4270_ = lean_st_ref_get(v_a_4266_);
lean_dec(v_a_4266_);
if (v_isShared_4269_ == 0)
{
lean_ctor_set(v___x_4268_, 0, v___x_4270_);
v___x_4272_ = v___x_4268_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4272_);
v___x_4274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4252_, v_closed_4253_, v___x_4273_, v___f_4254_);
return v___x_4274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v___x_4277_, lean_object* v_closed_4278_, lean_object* v___f_4279_, lean_object* v_x_4280_, lean_object* v___y_4281_){
_start:
{
uint8_t v_closed_boxed_4282_; lean_object* v_res_4283_; 
v_closed_boxed_4282_ = lean_unbox(v_closed_4278_);
v_res_4283_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v___x_4277_, v_closed_boxed_4282_, v___f_4279_, v_x_4280_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v_id_4284_, lean_object* v___y_4285_, lean_object* v_x_4286_){
_start:
{
if (lean_obj_tag(v_x_4286_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4296_; 
v_a_4288_ = lean_ctor_get(v_x_4286_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v_x_4286_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4290_ = v_x_4286_;
v_isShared_4291_ = v_isSharedCheck_4296_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v_x_4286_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4296_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
return v___x_4294_;
}
}
}
else
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4336_; 
v_a_4297_ = lean_ctor_get(v_x_4286_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v_x_4286_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4299_ = v_x_4286_;
v_isShared_4300_ = v_isSharedCheck_4336_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v_x_4286_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4336_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
uint8_t v_closed_4301_; 
v_closed_4301_ = lean_ctor_get_uint8(v_a_4297_, sizeof(void*)*10);
if (v_closed_4301_ == 0)
{
lean_object* v_capacity_4302_; lean_object* v_size_4303_; lean_object* v_receivers_4304_; lean_object* v___x_4305_; 
v_capacity_4302_ = lean_ctor_get(v_a_4297_, 2);
lean_inc(v_capacity_4302_);
v_size_4303_ = lean_ctor_get(v_a_4297_, 3);
lean_inc(v_size_4303_);
v_receivers_4304_ = lean_ctor_get(v_a_4297_, 7);
lean_inc(v_receivers_4304_);
lean_dec(v_a_4297_);
v___x_4305_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4304_, v_id_4284_);
lean_dec(v_receivers_4304_);
if (lean_obj_tag(v___x_4305_) == 1)
{
lean_object* v_val_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4325_; 
v_val_4306_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4308_ = v___x_4305_;
v_isShared_4309_ = v_isSharedCheck_4325_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_val_4306_);
lean_dec(v___x_4305_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4325_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4310_; uint8_t v___x_4311_; 
v___x_4310_ = lean_unsigned_to_nat(0u);
v___x_4311_ = lean_nat_dec_eq(v_size_4303_, v___x_4310_);
lean_dec(v_size_4303_);
if (v___x_4311_ == 0)
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___f_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___x_4317_; 
lean_del_object(v___x_4308_);
lean_del_object(v___x_4299_);
v___x_4312_ = lean_nat_mod(v_val_4306_, v_capacity_4302_);
lean_dec(v_capacity_4302_);
v___x_4313_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4312_, v___y_4285_);
v___f_4314_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4314_, 0, v_val_4306_);
v___x_4315_ = lean_box(v_closed_4301_);
v___f_4316_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_4316_, 0, v___x_4310_);
lean_closure_set(v___f_4316_, 1, v___x_4315_);
lean_closure_set(v___f_4316_, 2, v___f_4314_);
v___x_4317_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4310_, v___x_4311_, v___x_4313_, v___f_4316_);
return v___x_4317_;
}
else
{
lean_object* v___x_4318_; lean_object* v___x_4320_; 
lean_dec(v_val_4306_);
lean_dec(v_capacity_4302_);
v___x_4318_ = lean_box(v_closed_4301_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4318_);
v___x_4320_ = v___x_4299_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4318_);
v___x_4320_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
lean_object* v___x_4322_; 
if (v_isShared_4309_ == 0)
{
lean_ctor_set_tag(v___x_4308_, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4320_);
v___x_4322_ = v___x_4308_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4320_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4328_; 
lean_dec(v___x_4305_);
lean_dec(v_size_4303_);
lean_dec(v_capacity_4302_);
v___x_4326_ = lean_box(v_closed_4301_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4326_);
v___x_4328_ = v___x_4299_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4326_);
v___x_4328_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4329_; 
v___x_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
return v___x_4329_;
}
}
}
else
{
lean_object* v___x_4331_; lean_object* v___x_4333_; 
lean_dec(v_a_4297_);
v___x_4331_ = lean_box(v_closed_4301_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4331_);
v___x_4333_ = v___x_4299_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4334_; 
v___x_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
return v___x_4334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v_id_4337_, lean_object* v___y_4338_, lean_object* v_x_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v_id_4337_, v___y_4338_, v_x_4339_);
lean_dec(v___y_4338_);
lean_dec(v_id_4337_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4342_, lean_object* v_x_4343_){
_start:
{
if (lean_obj_tag(v_x_4343_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4353_; 
lean_dec_ref(v_x_4342_);
v_a_4345_ = lean_ctor_get(v_x_4343_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_x_4343_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4347_ = v_x_4343_;
v_isShared_4348_ = v_isSharedCheck_4353_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v_x_4343_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4353_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4345_);
v___x_4350_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
return v___x_4351_;
}
}
}
else
{
lean_object* v___x_4354_; 
lean_dec_ref_known(v_x_4343_, 1);
v___x_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4354_, 0, v_x_4342_);
return v___x_4354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4355_, lean_object* v_x_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4355_, v_x_4356_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4361_, lean_object* v_receiverId_4362_, lean_object* v_receivers_4363_, lean_object* v_x_4364_){
_start:
{
if (lean_obj_tag(v_x_4364_) == 0)
{
lean_object* v___x_4366_; 
lean_dec(v_receivers_4363_);
lean_dec(v_receiverId_4362_);
v___x_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4366_, 0, v_x_4364_);
return v___x_4366_;
}
else
{
lean_object* v_a_4367_; 
v_a_4367_ = lean_ctor_get(v_x_4364_, 0);
if (lean_obj_tag(v_a_4367_) == 1)
{
lean_object* v___x_4368_; lean_object* v_producers_4369_; lean_object* v_waiters_4370_; lean_object* v_capacity_4371_; lean_object* v_size_4372_; lean_object* v_buffer_4373_; lean_object* v_write_4374_; lean_object* v_read_4375_; lean_object* v_nextId_4376_; uint8_t v_closed_4377_; lean_object* v_pos_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4392_; 
v___x_4368_ = lean_st_ref_take(v_a_4361_);
v_producers_4369_ = lean_ctor_get(v___x_4368_, 0);
v_waiters_4370_ = lean_ctor_get(v___x_4368_, 1);
v_capacity_4371_ = lean_ctor_get(v___x_4368_, 2);
v_size_4372_ = lean_ctor_get(v___x_4368_, 3);
v_buffer_4373_ = lean_ctor_get(v___x_4368_, 4);
v_write_4374_ = lean_ctor_get(v___x_4368_, 5);
v_read_4375_ = lean_ctor_get(v___x_4368_, 6);
v_nextId_4376_ = lean_ctor_get(v___x_4368_, 8);
v_closed_4377_ = lean_ctor_get_uint8(v___x_4368_, sizeof(void*)*10);
v_pos_4378_ = lean_ctor_get(v___x_4368_, 9);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4392_ == 0)
{
lean_object* v_unused_4393_; 
v_unused_4393_ = lean_ctor_get(v___x_4368_, 7);
lean_dec(v_unused_4393_);
v___x_4380_ = v___x_4368_;
v_isShared_4381_ = v_isSharedCheck_4392_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_pos_4378_);
lean_inc(v_nextId_4376_);
lean_inc(v_read_4375_);
lean_inc(v_write_4374_);
lean_inc(v_buffer_4373_);
lean_inc(v_size_4372_);
lean_inc(v_capacity_4371_);
lean_inc(v_waiters_4370_);
lean_inc(v_producers_4369_);
lean_dec(v___x_4368_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4392_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4382_; lean_object* v___x_4384_; 
v___x_4382_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4362_, v_receivers_4363_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 7, v___x_4382_);
v___x_4384_ = v___x_4380_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_producers_4369_);
lean_ctor_set(v_reuseFailAlloc_4391_, 1, v_waiters_4370_);
lean_ctor_set(v_reuseFailAlloc_4391_, 2, v_capacity_4371_);
lean_ctor_set(v_reuseFailAlloc_4391_, 3, v_size_4372_);
lean_ctor_set(v_reuseFailAlloc_4391_, 4, v_buffer_4373_);
lean_ctor_set(v_reuseFailAlloc_4391_, 5, v_write_4374_);
lean_ctor_set(v_reuseFailAlloc_4391_, 6, v_read_4375_);
lean_ctor_set(v_reuseFailAlloc_4391_, 7, v___x_4382_);
lean_ctor_set(v_reuseFailAlloc_4391_, 8, v_nextId_4376_);
lean_ctor_set(v_reuseFailAlloc_4391_, 9, v_pos_4378_);
lean_ctor_set_uint8(v_reuseFailAlloc_4391_, sizeof(void*)*10, v_closed_4377_);
v___x_4384_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
lean_object* v___x_4385_; lean_object* v___f_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; lean_object* v___x_4390_; 
v___x_4385_ = lean_st_ref_put(v_a_4361_, v___x_4384_);
v___f_4386_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4386_, 0, v_x_4364_);
v___x_4387_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4388_ = lean_unsigned_to_nat(0u);
v___x_4389_ = 0;
v___x_4390_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4388_, v___x_4389_, v___x_4387_, v___f_4386_);
return v___x_4390_;
}
}
}
else
{
lean_object* v___x_4394_; 
lean_dec_ref_known(v_x_4364_, 1);
lean_dec(v_receivers_4363_);
lean_dec(v_receiverId_4362_);
v___x_4394_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4394_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4395_, lean_object* v_receiverId_4396_, lean_object* v_receivers_4397_, lean_object* v_x_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4395_, v_receiverId_4396_, v_receivers_4397_, v_x_4398_);
lean_dec(v_a_4395_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4401_){
_start:
{
if (lean_obj_tag(v_x_4401_) == 0)
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4411_; 
v_a_4403_ = lean_ctor_get(v_x_4401_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v_x_4401_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4405_ = v_x_4401_;
v_isShared_4406_ = v_isSharedCheck_4411_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v_x_4401_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4411_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
lean_object* v___x_4409_; 
v___x_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
return v___x_4409_;
}
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4424_; 
v_a_4412_ = lean_ctor_get(v_x_4401_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_x_4401_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4414_ = v_x_4401_;
v_isShared_4415_ = v_isSharedCheck_4424_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v_x_4401_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4424_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v_size_4416_; lean_object* v___x_4417_; uint8_t v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4421_; 
v_size_4416_ = lean_ctor_get(v_a_4412_, 3);
lean_inc(v_size_4416_);
lean_dec(v_a_4412_);
v___x_4417_ = lean_unsigned_to_nat(0u);
v___x_4418_ = lean_nat_dec_eq(v_size_4416_, v___x_4417_);
lean_dec(v_size_4416_);
v___x_4419_ = lean_box(v___x_4418_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v___x_4419_);
v___x_4421_ = v___x_4414_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
return v___x_4422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4425_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4429_){
_start:
{
lean_object* v___x_4431_; lean_object* v___f_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; uint8_t v___x_4436_; lean_object* v___x_4437_; 
v___x_4431_ = lean_st_ref_get(v_a_4429_);
v___f_4432_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4431_);
v___x_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4433_);
v___x_4435_ = lean_unsigned_to_nat(0u);
v___x_4436_ = 0;
v___x_4437_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4435_, v___x_4436_, v___x_4434_, v___f_4432_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4438_);
lean_dec(v_a_4438_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4441_, lean_object* v_next_4442_){
_start:
{
lean_object* v___x_4444_; lean_object* v_fst_4446_; lean_object* v_snd_4447_; lean_object* v_value_4451_; lean_object* v_pos_4452_; lean_object* v_remaining_4453_; uint8_t v___x_4454_; 
v___x_4444_ = lean_st_ref_take(v_slot_4441_);
v_value_4451_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_value_4451_);
v_pos_4452_ = lean_ctor_get(v___x_4444_, 1);
lean_inc(v_pos_4452_);
v_remaining_4453_ = lean_ctor_get(v___x_4444_, 2);
lean_inc(v_remaining_4453_);
v___x_4454_ = lean_nat_dec_eq(v_next_4442_, v_pos_4452_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
lean_dec(v_remaining_4453_);
lean_dec(v_pos_4452_);
lean_dec(v_value_4451_);
v___x_4455_ = lean_box(0);
v___x_4456_ = lean_box(v___x_4454_);
v___x_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4455_);
lean_ctor_set(v___x_4457_, 1, v___x_4456_);
v_fst_4446_ = v___x_4457_;
v_snd_4447_ = v___x_4444_;
goto v___jp_4445_;
}
else
{
lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4476_; 
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; lean_object* v_unused_4478_; lean_object* v_unused_4479_; 
v_unused_4477_ = lean_ctor_get(v___x_4444_, 2);
lean_dec(v_unused_4477_);
v_unused_4478_ = lean_ctor_get(v___x_4444_, 1);
lean_dec(v_unused_4478_);
v_unused_4479_ = lean_ctor_get(v___x_4444_, 0);
lean_dec(v_unused_4479_);
v___x_4459_ = v___x_4444_;
v_isShared_4460_ = v_isSharedCheck_4476_;
goto v_resetjp_4458_;
}
else
{
lean_dec(v___x_4444_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4476_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4461_; uint8_t v___x_4462_; 
v___x_4461_ = lean_unsigned_to_nat(1u);
v___x_4462_ = lean_nat_dec_eq(v_remaining_4453_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4467_; 
v___x_4463_ = lean_box(v___x_4462_);
lean_inc(v_value_4451_);
v___x_4464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4464_, 0, v_value_4451_);
lean_ctor_set(v___x_4464_, 1, v___x_4463_);
v___x_4465_ = lean_nat_sub(v_remaining_4453_, v___x_4461_);
lean_dec(v_remaining_4453_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 2, v___x_4465_);
v___x_4467_ = v___x_4459_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_value_4451_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_pos_4452_);
lean_ctor_set(v_reuseFailAlloc_4468_, 2, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
v_fst_4446_ = v___x_4464_;
v_snd_4447_ = v___x_4467_;
goto v___jp_4445_;
}
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4474_; 
lean_dec(v_remaining_4453_);
v___x_4469_ = lean_box(v___x_4454_);
v___x_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4470_, 0, v_value_4451_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
v___x_4471_ = lean_box(0);
v___x_4472_ = lean_unsigned_to_nat(0u);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 2, v___x_4472_);
lean_ctor_set(v___x_4459_, 0, v___x_4471_);
v___x_4474_ = v___x_4459_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4475_, 1, v_pos_4452_);
lean_ctor_set(v_reuseFailAlloc_4475_, 2, v___x_4472_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
v_fst_4446_ = v___x_4470_;
v_snd_4447_ = v___x_4474_;
goto v___jp_4445_;
}
}
}
}
v___jp_4445_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4448_ = lean_st_ref_put(v_slot_4441_, v_snd_4447_);
v___x_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4449_, 0, v_fst_4446_);
v___x_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
return v___x_4450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4480_, lean_object* v_next_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4480_, v_next_4481_);
lean_dec(v_next_4481_);
lean_dec(v_slot_4480_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4484_, uint8_t v_a_4485_, lean_object* v___f_4486_, lean_object* v_x_4487_){
_start:
{
if (lean_obj_tag(v_x_4487_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4497_; 
lean_dec_ref(v___f_4486_);
v_a_4489_ = lean_ctor_get(v_x_4487_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v_x_4487_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4491_ = v_x_4487_;
v_isShared_4492_ = v_isSharedCheck_4497_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v_x_4487_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4497_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
lean_object* v___x_4495_; 
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4498_ = lean_ctor_get(v_x_4487_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v_x_4487_, 1);
v___x_4499_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4498_, v_next_4484_);
lean_dec(v_a_4498_);
v___x_4500_ = lean_unsigned_to_nat(0u);
v___x_4501_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4500_, v_a_4485_, v___x_4499_, v___f_4486_);
return v___x_4501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4502_, lean_object* v_a_4503_, lean_object* v___f_4504_, lean_object* v_x_4505_, lean_object* v___y_4506_){
_start:
{
uint8_t v_a_12228__boxed_4507_; lean_object* v_res_4508_; 
v_a_12228__boxed_4507_ = lean_unbox(v_a_4503_);
v_res_4508_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4502_, v_a_12228__boxed_4507_, v___f_4504_, v_x_4505_);
lean_dec(v_next_4502_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4509_, lean_object* v___f_4510_, lean_object* v_____r_4511_, lean_object* v_st_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4515_ = lean_st_ref_swap(v___y_4513_, v_st_4512_);
lean_dec(v___x_4515_);
v___x_4516_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4517_ = lean_unsigned_to_nat(0u);
v___x_4518_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4517_, v_a_4509_, v___x_4516_, v___f_4510_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4519_, lean_object* v___f_4520_, lean_object* v_____r_4521_, lean_object* v_st_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
uint8_t v_a_12270__boxed_4525_; lean_object* v_res_4526_; 
v_a_12270__boxed_4525_ = lean_unbox(v_a_4519_);
v_res_4526_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_12270__boxed_4525_, v___f_4520_, v_____r_4521_, v_st_4522_, v___y_4523_);
lean_dec(v___y_4523_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4527_, lean_object* v_waiters_4528_, lean_object* v_capacity_4529_, lean_object* v_size_4530_, lean_object* v_buffer_4531_, lean_object* v_write_4532_, lean_object* v_read_4533_, lean_object* v_receivers_4534_, lean_object* v_nextId_4535_, uint8_t v_closed_4536_, lean_object* v_pos_4537_, lean_object* v___f_4538_, lean_object* v_a_4539_, lean_object* v_x_4540_){
_start:
{
if (lean_obj_tag(v_x_4540_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v___f_4538_);
lean_dec(v_pos_4537_);
lean_dec(v_nextId_4535_);
lean_dec(v_receivers_4534_);
lean_dec(v_read_4533_);
lean_dec(v_write_4532_);
lean_dec_ref(v_buffer_4531_);
lean_dec(v_size_4530_);
lean_dec(v_capacity_4529_);
lean_dec_ref(v_waiters_4528_);
lean_dec_ref(v_snd_4527_);
v_a_4542_ = lean_ctor_get(v_x_4540_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_x_4540_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4544_ = v_x_4540_;
v_isShared_4545_ = v_isSharedCheck_4550_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v_x_4540_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4550_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
lean_object* v___x_4548_; 
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4547_);
return v___x_4548_;
}
}
}
else
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec_ref_known(v_x_4540_, 1);
v___x_4551_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4551_, 0, v_snd_4527_);
lean_ctor_set(v___x_4551_, 1, v_waiters_4528_);
lean_ctor_set(v___x_4551_, 2, v_capacity_4529_);
lean_ctor_set(v___x_4551_, 3, v_size_4530_);
lean_ctor_set(v___x_4551_, 4, v_buffer_4531_);
lean_ctor_set(v___x_4551_, 5, v_write_4532_);
lean_ctor_set(v___x_4551_, 6, v_read_4533_);
lean_ctor_set(v___x_4551_, 7, v_receivers_4534_);
lean_ctor_set(v___x_4551_, 8, v_nextId_4535_);
lean_ctor_set(v___x_4551_, 9, v_pos_4537_);
lean_ctor_set_uint8(v___x_4551_, sizeof(void*)*10, v_closed_4536_);
v___x_4552_ = lean_box(0);
lean_inc(v_a_4539_);
v___x_4553_ = lean_apply_4(v___f_4538_, v___x_4552_, v___x_4551_, v_a_4539_, lean_box(0));
return v___x_4553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4554_, lean_object* v_waiters_4555_, lean_object* v_capacity_4556_, lean_object* v_size_4557_, lean_object* v_buffer_4558_, lean_object* v_write_4559_, lean_object* v_read_4560_, lean_object* v_receivers_4561_, lean_object* v_nextId_4562_, lean_object* v_closed_4563_, lean_object* v_pos_4564_, lean_object* v___f_4565_, lean_object* v_a_4566_, lean_object* v_x_4567_, lean_object* v___y_4568_){
_start:
{
uint8_t v_closed_boxed_4569_; lean_object* v_res_4570_; 
v_closed_boxed_4569_ = lean_unbox(v_closed_4563_);
v_res_4570_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4554_, v_waiters_4555_, v_capacity_4556_, v_size_4557_, v_buffer_4558_, v_write_4559_, v_read_4560_, v_receivers_4561_, v_nextId_4562_, v_closed_boxed_4569_, v_pos_4564_, v___f_4565_, v_a_4566_, v_x_4567_);
lean_dec(v_a_4566_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4571_, lean_object* v_x_4572_){
_start:
{
if (lean_obj_tag(v_x_4572_) == 0)
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4582_; 
lean_dec(v_fst_4571_);
v_a_4574_ = lean_ctor_get(v_x_4572_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v_x_4572_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4576_ = v_x_4572_;
v_isShared_4577_ = v_isSharedCheck_4582_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v_x_4572_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4582_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
lean_object* v___x_4580_; 
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
return v___x_4580_;
}
}
}
else
{
lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4590_; 
v_isSharedCheck_4590_ = !lean_is_exclusive(v_x_4572_);
if (v_isSharedCheck_4590_ == 0)
{
lean_object* v_unused_4591_; 
v_unused_4591_ = lean_ctor_get(v_x_4572_, 0);
lean_dec(v_unused_4591_);
v___x_4584_ = v_x_4572_;
v_isShared_4585_ = v_isSharedCheck_4590_;
goto v_resetjp_4583_;
}
else
{
lean_dec(v_x_4572_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4590_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v_fst_4571_);
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_fst_4571_);
v___x_4587_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4588_; 
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
return v___x_4588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4592_, lean_object* v_x_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4592_, v_x_4593_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, uint8_t v___x_4599_, lean_object* v_x_4600_){
_start:
{
if (lean_obj_tag(v_x_4600_) == 0)
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4610_; 
lean_dec_ref(v_a_4597_);
v_a_4602_ = lean_ctor_get(v_x_4600_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v_x_4600_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4604_ = v_x_4600_;
v_isShared_4605_ = v_isSharedCheck_4610_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v_x_4600_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4610_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4602_);
v___x_4607_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
return v___x_4608_;
}
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4658_; 
v_a_4611_ = lean_ctor_get(v_x_4600_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_x_4600_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4613_ = v_x_4600_;
v_isShared_4614_ = v_isSharedCheck_4658_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v_x_4600_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4658_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v_fst_4615_; 
v_fst_4615_ = lean_ctor_get(v_a_4611_, 0);
lean_inc(v_fst_4615_);
if (lean_obj_tag(v_fst_4615_) == 1)
{
lean_object* v_snd_4616_; lean_object* v___f_4617_; lean_object* v___x_4618_; lean_object* v___f_4619_; uint8_t v___x_4620_; 
v_snd_4616_ = lean_ctor_get(v_a_4611_, 1);
lean_inc(v_snd_4616_);
lean_dec(v_a_4611_);
v___f_4617_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4617_, 0, v_fst_4615_);
v___x_4618_ = lean_box(v_a_4596_);
lean_inc_ref(v___f_4617_);
v___f_4619_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4619_, 0, v___x_4618_);
lean_closure_set(v___f_4619_, 1, v___f_4617_);
v___x_4620_ = lean_unbox(v_snd_4616_);
lean_dec(v_snd_4616_);
if (v___x_4620_ == 0)
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
lean_dec_ref(v___f_4619_);
lean_del_object(v___x_4613_);
v___x_4621_ = lean_box(0);
v___x_4622_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4596_, v___f_4617_, v___x_4621_, v_a_4597_, v_a_4598_);
return v___x_4622_;
}
else
{
lean_object* v___x_4623_; lean_object* v_producers_4624_; lean_object* v_waiters_4625_; lean_object* v_capacity_4626_; lean_object* v_size_4627_; lean_object* v_buffer_4628_; lean_object* v_write_4629_; lean_object* v_read_4630_; lean_object* v_receivers_4631_; lean_object* v_nextId_4632_; uint8_t v_closed_4633_; lean_object* v_pos_4634_; lean_object* v___x_4635_; 
v___x_4623_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4597_);
v_producers_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc_ref(v_producers_4624_);
v_waiters_4625_ = lean_ctor_get(v___x_4623_, 1);
lean_inc_ref(v_waiters_4625_);
v_capacity_4626_ = lean_ctor_get(v___x_4623_, 2);
lean_inc(v_capacity_4626_);
v_size_4627_ = lean_ctor_get(v___x_4623_, 3);
lean_inc(v_size_4627_);
v_buffer_4628_ = lean_ctor_get(v___x_4623_, 4);
lean_inc_ref(v_buffer_4628_);
v_write_4629_ = lean_ctor_get(v___x_4623_, 5);
lean_inc(v_write_4629_);
v_read_4630_ = lean_ctor_get(v___x_4623_, 6);
lean_inc(v_read_4630_);
v_receivers_4631_ = lean_ctor_get(v___x_4623_, 7);
lean_inc(v_receivers_4631_);
v_nextId_4632_ = lean_ctor_get(v___x_4623_, 8);
lean_inc(v_nextId_4632_);
v_closed_4633_ = lean_ctor_get_uint8(v___x_4623_, sizeof(void*)*10);
v_pos_4634_ = lean_ctor_get(v___x_4623_, 9);
lean_inc(v_pos_4634_);
v___x_4635_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4624_);
if (lean_obj_tag(v___x_4635_) == 1)
{
lean_object* v_val_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4654_; 
lean_dec_ref(v___x_4623_);
lean_dec_ref(v___f_4617_);
v_val_4636_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4638_ = v___x_4635_;
v_isShared_4639_ = v_isSharedCheck_4654_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_val_4636_);
lean_dec(v___x_4635_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4654_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v_fst_4640_; lean_object* v_snd_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___f_4645_; lean_object* v___x_4647_; 
v_fst_4640_ = lean_ctor_get(v_val_4636_, 0);
lean_inc(v_fst_4640_);
v_snd_4641_ = lean_ctor_get(v_val_4636_, 1);
lean_inc(v_snd_4641_);
lean_dec(v_val_4636_);
v___x_4642_ = lean_box(v___x_4599_);
v___x_4643_ = lean_io_promise_resolve(v___x_4642_, v_fst_4640_);
lean_dec(v_fst_4640_);
v___x_4644_ = lean_box(v_closed_4633_);
lean_inc(v_a_4598_);
v___f_4645_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4645_, 0, v_snd_4641_);
lean_closure_set(v___f_4645_, 1, v_waiters_4625_);
lean_closure_set(v___f_4645_, 2, v_capacity_4626_);
lean_closure_set(v___f_4645_, 3, v_size_4627_);
lean_closure_set(v___f_4645_, 4, v_buffer_4628_);
lean_closure_set(v___f_4645_, 5, v_write_4629_);
lean_closure_set(v___f_4645_, 6, v_read_4630_);
lean_closure_set(v___f_4645_, 7, v_receivers_4631_);
lean_closure_set(v___f_4645_, 8, v_nextId_4632_);
lean_closure_set(v___f_4645_, 9, v___x_4644_);
lean_closure_set(v___f_4645_, 10, v_pos_4634_);
lean_closure_set(v___f_4645_, 11, v___f_4619_);
lean_closure_set(v___f_4645_, 12, v_a_4598_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4643_);
v___x_4647_ = v___x_4613_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v___x_4643_);
v___x_4647_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
lean_object* v___x_4649_; 
if (v_isShared_4639_ == 0)
{
lean_ctor_set_tag(v___x_4638_, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4647_);
v___x_4649_ = v___x_4638_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4647_);
v___x_4649_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = lean_unsigned_to_nat(0u);
v___x_4651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4650_, v_a_4596_, v___x_4649_, v___f_4645_);
return v___x_4651_;
}
}
}
}
else
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
lean_dec(v___x_4635_);
lean_dec(v_pos_4634_);
lean_dec(v_nextId_4632_);
lean_dec(v_receivers_4631_);
lean_dec(v_read_4630_);
lean_dec(v_write_4629_);
lean_dec_ref(v_buffer_4628_);
lean_dec(v_size_4627_);
lean_dec(v_capacity_4626_);
lean_dec_ref(v_waiters_4625_);
lean_dec_ref(v___f_4619_);
lean_del_object(v___x_4613_);
v___x_4655_ = lean_box(0);
v___x_4656_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4596_, v___f_4617_, v___x_4655_, v___x_4623_, v_a_4598_);
return v___x_4656_;
}
}
}
else
{
lean_object* v___x_4657_; 
lean_dec(v_fst_4615_);
lean_del_object(v___x_4613_);
lean_dec(v_a_4611_);
lean_dec_ref(v_a_4597_);
v___x_4657_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v___x_4662_, lean_object* v_x_4663_, lean_object* v___y_4664_){
_start:
{
uint8_t v_a_12382__boxed_4665_; uint8_t v___x_12384__boxed_4666_; lean_object* v_res_4667_; 
v_a_12382__boxed_4665_ = lean_unbox(v_a_4659_);
v___x_12384__boxed_4666_ = lean_unbox(v___x_4662_);
v_res_4667_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12382__boxed_4665_, v_a_4660_, v_a_4661_, v___x_12384__boxed_4666_, v_x_4663_);
lean_dec(v_a_4661_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4668_, lean_object* v_next_4669_, lean_object* v_a_4670_, lean_object* v_x_4671_){
_start:
{
if (lean_obj_tag(v_x_4671_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4681_; 
lean_dec(v_next_4669_);
lean_dec_ref(v_a_4668_);
v_a_4673_ = lean_ctor_get(v_x_4671_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_x_4671_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4675_ = v_x_4671_;
v_isShared_4676_ = v_isSharedCheck_4681_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v_x_4671_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4681_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
lean_object* v___x_4679_; 
v___x_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
return v___x_4679_;
}
}
}
else
{
lean_object* v_a_4682_; uint8_t v___x_4683_; 
v_a_4682_ = lean_ctor_get(v_x_4671_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v_x_4671_, 1);
v___x_4683_ = lean_unbox(v_a_4682_);
if (v___x_4683_ == 0)
{
lean_object* v_capacity_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___f_4689_; lean_object* v___f_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; lean_object* v___x_4693_; 
v_capacity_4684_ = lean_ctor_get(v_a_4668_, 2);
v___x_4685_ = lean_nat_mod(v_next_4669_, v_capacity_4684_);
v___x_4686_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4685_, v_a_4670_);
v___x_4687_ = 1;
v___x_4688_ = lean_box(v___x_4687_);
lean_inc(v_a_4670_);
lean_inc_n(v_a_4682_, 2);
v___f_4689_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4689_, 0, v_a_4682_);
lean_closure_set(v___f_4689_, 1, v_a_4668_);
lean_closure_set(v___f_4689_, 2, v_a_4670_);
lean_closure_set(v___f_4689_, 3, v___x_4688_);
v___f_4690_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4690_, 0, v_next_4669_);
lean_closure_set(v___f_4690_, 1, v_a_4682_);
lean_closure_set(v___f_4690_, 2, v___f_4689_);
v___x_4691_ = lean_unsigned_to_nat(0u);
v___x_4692_ = lean_unbox(v_a_4682_);
lean_dec(v_a_4682_);
v___x_4693_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4691_, v___x_4692_, v___x_4686_, v___f_4690_);
return v___x_4693_;
}
else
{
lean_object* v___x_4694_; 
lean_dec(v_a_4682_);
lean_dec(v_next_4669_);
lean_dec_ref(v_a_4668_);
v___x_4694_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4695_, lean_object* v_next_4696_, lean_object* v_a_4697_, lean_object* v_x_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4695_, v_next_4696_, v_a_4697_, v_x_4698_);
lean_dec(v_a_4697_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4701_, lean_object* v_next_4702_, lean_object* v_x_4703_){
_start:
{
if (lean_obj_tag(v_x_4703_) == 0)
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4713_; 
lean_dec(v_next_4702_);
v_a_4705_ = lean_ctor_get(v_x_4703_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v_x_4703_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4707_ = v_x_4703_;
v_isShared_4708_ = v_isSharedCheck_4713_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v_x_4703_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4713_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4711_; 
v___x_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4711_, 0, v___x_4710_);
return v___x_4711_;
}
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4715_; lean_object* v___f_4716_; lean_object* v___x_4717_; uint8_t v___x_4718_; lean_object* v___x_4719_; 
v_a_4714_ = lean_ctor_get(v_x_4703_, 0);
lean_inc(v_a_4714_);
lean_dec_ref_known(v_x_4703_, 1);
v___x_4715_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4701_);
lean_inc(v_a_4701_);
v___f_4716_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4716_, 0, v_a_4714_);
lean_closure_set(v___f_4716_, 1, v_next_4702_);
lean_closure_set(v___f_4716_, 2, v_a_4701_);
v___x_4717_ = lean_unsigned_to_nat(0u);
v___x_4718_ = 0;
v___x_4719_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4717_, v___x_4718_, v___x_4715_, v___f_4716_);
return v___x_4719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4720_, lean_object* v_next_4721_, lean_object* v_x_4722_, lean_object* v___y_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4720_, v_next_4721_, v_x_4722_);
lean_dec(v_a_4720_);
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v___x_4728_; lean_object* v___f_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; uint8_t v___x_4733_; lean_object* v___x_4734_; 
v___x_4728_ = lean_st_ref_get(v_a_4726_);
lean_inc(v_a_4726_);
v___f_4729_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4729_, 0, v_a_4726_);
lean_closure_set(v___f_4729_, 1, v_next_4725_);
v___x_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4728_);
v___x_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
v___x_4732_ = lean_unsigned_to_nat(0u);
v___x_4733_ = 0;
v___x_4734_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4732_, v___x_4733_, v___x_4731_, v___f_4729_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4735_, lean_object* v_a_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4735_, v_a_4736_);
lean_dec(v_a_4736_);
return v_res_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4739_, lean_object* v_a_4740_, lean_object* v_x_4741_){
_start:
{
if (lean_obj_tag(v_x_4741_) == 0)
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v_receiverId_4739_);
v_a_4743_ = lean_ctor_get(v_x_4741_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v_x_4741_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4745_ = v_x_4741_;
v_isShared_4746_ = v_isSharedCheck_4751_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v_x_4741_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4751_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
lean_object* v___x_4749_; 
v___x_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4748_);
return v___x_4749_;
}
}
}
else
{
lean_object* v_a_4752_; lean_object* v_receivers_4753_; lean_object* v___x_4754_; 
v_a_4752_ = lean_ctor_get(v_x_4741_, 0);
lean_inc(v_a_4752_);
lean_dec_ref_known(v_x_4741_, 1);
v_receivers_4753_ = lean_ctor_get(v_a_4752_, 7);
lean_inc(v_receivers_4753_);
lean_dec(v_a_4752_);
v___x_4754_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4753_, v_receiverId_4739_);
if (lean_obj_tag(v___x_4754_) == 1)
{
lean_object* v_val_4755_; lean_object* v___x_4756_; lean_object* v___f_4757_; lean_object* v___x_4758_; uint8_t v___x_4759_; lean_object* v___x_4760_; 
v_val_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc(v_val_4755_);
lean_dec_ref_known(v___x_4754_, 1);
v___x_4756_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4755_, v_a_4740_);
lean_inc(v_a_4740_);
v___f_4757_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4757_, 0, v_a_4740_);
lean_closure_set(v___f_4757_, 1, v_receiverId_4739_);
lean_closure_set(v___f_4757_, 2, v_receivers_4753_);
v___x_4758_ = lean_unsigned_to_nat(0u);
v___x_4759_ = 0;
v___x_4760_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4758_, v___x_4759_, v___x_4756_, v___f_4757_);
return v___x_4760_;
}
else
{
lean_object* v___x_4761_; 
lean_dec(v___x_4754_);
lean_dec(v_receivers_4753_);
lean_dec(v_receiverId_4739_);
v___x_4761_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4762_, lean_object* v_a_4763_, lean_object* v_x_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4762_, v_a_4763_, v_x_4764_);
lean_dec(v_a_4763_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v___x_4770_; lean_object* v___f_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; uint8_t v___x_4775_; lean_object* v___x_4776_; 
v___x_4770_ = lean_st_ref_get(v_a_4768_);
lean_inc(v_a_4768_);
v___f_4771_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4771_, 0, v_receiverId_4767_);
lean_closure_set(v___f_4771_, 1, v_a_4768_);
v___x_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4770_);
v___x_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
v___x_4774_ = lean_unsigned_to_nat(0u);
v___x_4775_ = 0;
v___x_4776_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4774_, v___x_4775_, v___x_4773_, v___f_4771_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4777_, lean_object* v_a_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4777_, v_a_4778_);
lean_dec(v_a_4778_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4785_, lean_object* v___y_4786_, lean_object* v___f_4787_, lean_object* v_x_4788_){
_start:
{
if (lean_obj_tag(v_x_4788_) == 0)
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4798_; 
lean_dec_ref(v___f_4787_);
lean_dec(v_id_4785_);
v_a_4790_ = lean_ctor_get(v_x_4788_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v_x_4788_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4792_ = v_x_4788_;
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v_x_4788_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
lean_object* v___x_4796_; 
v___x_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4795_);
return v___x_4796_;
}
}
}
else
{
lean_object* v_a_4799_; uint8_t v___x_4800_; 
v_a_4799_ = lean_ctor_get(v_x_4788_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v_x_4788_, 1);
v___x_4800_ = lean_unbox(v_a_4799_);
lean_dec(v_a_4799_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; 
lean_dec_ref(v___f_4787_);
lean_dec(v_id_4785_);
v___x_4801_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1));
return v___x_4801_;
}
else
{
lean_object* v___x_4802_; lean_object* v___x_4803_; uint8_t v___x_4804_; lean_object* v___x_4805_; 
v___x_4802_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4785_, v___y_4786_);
v___x_4803_ = lean_unsigned_to_nat(0u);
v___x_4804_ = 0;
v___x_4805_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4803_, v___x_4804_, v___x_4802_, v___f_4787_);
return v___x_4805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4806_, lean_object* v___y_4807_, lean_object* v___f_4808_, lean_object* v_x_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4806_, v___y_4807_, v___f_4808_, v_x_4809_);
lean_dec(v___y_4807_);
return v_res_4811_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4812_, lean_object* v___f_4813_, lean_object* v___y_4814_){
_start:
{
lean_object* v___x_4816_; lean_object* v___f_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; lean_object* v___x_4822_; lean_object* v___f_4823_; lean_object* v___x_4824_; 
v___x_4816_ = lean_st_ref_get(v___y_4814_);
lean_inc_n(v___y_4814_, 2);
lean_inc(v_id_4812_);
v___f_4817_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_4817_, 0, v_id_4812_);
lean_closure_set(v___f_4817_, 1, v___y_4814_);
v___x_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4816_);
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
v___x_4820_ = lean_unsigned_to_nat(0u);
v___x_4821_ = 0;
v___x_4822_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4820_, v___x_4821_, v___x_4819_, v___f_4817_);
v___f_4823_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4823_, 0, v_id_4812_);
lean_closure_set(v___f_4823_, 1, v___y_4814_);
lean_closure_set(v___f_4823_, 2, v___f_4813_);
v___x_4824_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4820_, v___x_4821_, v___x_4822_, v___f_4823_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4825_, lean_object* v___f_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4825_, v___f_4826_, v___y_4827_);
lean_dec(v___y_4827_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4832_){
_start:
{
lean_object* v_state_4833_; lean_object* v_id_4834_; lean_object* v___f_4835_; lean_object* v___f_4836_; lean_object* v___f_4837_; lean_object* v___f_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v_state_4833_ = lean_ctor_get(v_ch_4832_, 0);
lean_inc_ref_n(v_state_4833_, 2);
v_id_4834_ = lean_ctor_get(v_ch_4832_, 1);
lean_inc(v_id_4834_);
v___f_4835_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4836_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4836_, 0, v_ch_4832_);
v___f_4837_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4838_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4838_, 0, v_id_4834_);
lean_closure_set(v___f_4838_, 1, v___f_4837_);
v___x_4839_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4839_, 0, lean_box(0));
lean_closure_set(v___x_4839_, 1, lean_box(0));
lean_closure_set(v___x_4839_, 2, v_state_4833_);
lean_closure_set(v___x_4839_, 3, v___f_4838_);
v___x_4840_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4840_, 0, lean_box(0));
lean_closure_set(v___x_4840_, 1, lean_box(0));
lean_closure_set(v___x_4840_, 2, v_state_4833_);
lean_closure_set(v___x_4840_, 3, v___f_4835_);
v___x_4841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4839_);
lean_ctor_set(v___x_4841_, 1, v___f_4836_);
lean_ctor_set(v___x_4841_, 2, v___x_4840_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4842_, lean_object* v_ch_4843_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4845_, lean_object* v_receiverId_4846_, lean_object* v_a_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4846_, v_a_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4850_, lean_object* v_receiverId_4851_, lean_object* v_a_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4850_, v_receiverId_4851_, v_a_4852_);
lean_dec(v_a_4852_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4855_, lean_object* v_q_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4856_, v___y_4857_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4860_, lean_object* v_q_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4860_, v_q_4861_, v___y_4862_);
lean_dec(v___y_4862_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4865_, lean_object* v_slot_4866_, lean_object* v_next_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4866_, v_next_4867_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4871_, lean_object* v_slot_4872_, lean_object* v_next_4873_, lean_object* v_a_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4871_, v_slot_4872_, v_next_4873_, v_a_4874_);
lean_dec(v_a_4874_);
lean_dec(v_next_4873_);
lean_dec(v_slot_4872_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4877_, lean_object* v_a_4878_){
_start:
{
lean_object* v___x_4880_; 
v___x_4880_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4878_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4881_, lean_object* v_a_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4881_, v_a_4882_);
lean_dec(v_a_4882_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4885_, lean_object* v_next_4886_, lean_object* v_a_4887_){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4886_, v_a_4887_);
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4890_, lean_object* v_next_4891_, lean_object* v_a_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4890_, v_next_4891_, v_a_4892_);
lean_dec(v_a_4892_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4895_, lean_object* v_x_4896_, lean_object* v_x_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v___x_4900_; 
v___x_4900_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4896_, v_x_4897_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4901_, lean_object* v_x_4902_, lean_object* v_x_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4901_, v_x_4902_, v_x_4903_, v___y_4904_);
lean_dec(v___y_4904_);
return v_res_4906_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4908_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4908_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4911_, lean_object* v_a_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_Std_Broadcast_new___redArg(v_capacity_4911_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4914_, lean_object* v_capacity_4915_, lean_object* v_h_4916_){
_start:
{
lean_object* v___x_4918_; 
v___x_4918_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4915_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4919_, lean_object* v_capacity_4920_, lean_object* v_h_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Std_Broadcast_new(v_00_u03b1_4919_, v_capacity_4920_, v_h_4921_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4924_, lean_object* v_v_4925_){
_start:
{
lean_object* v___x_4927_; 
v___x_4927_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4924_, v_v_4925_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4928_, lean_object* v_v_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Std_Broadcast_trySend___redArg(v_ch_4928_, v_v_4929_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4932_, lean_object* v_ch_4933_, lean_object* v_v_4934_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4933_, v_v_4934_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4937_, lean_object* v_ch_4938_, lean_object* v_v_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Std_Broadcast_trySend(v_00_u03b1_4937_, v_ch_4938_, v_v_4939_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4942_){
_start:
{
lean_object* v___x_4944_; 
v___x_4944_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4942_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4952_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4947_ = v___x_4944_;
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4944_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4950_; 
if (v_isShared_4948_ == 0)
{
v___x_4950_ = v___x_4947_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4945_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
}
}
}
else
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
v_a_4953_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4944_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4944_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___x_4958_; 
if (v_isShared_4956_ == 0)
{
v___x_4958_ = v___x_4955_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_4961_, lean_object* v_a_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_Std_Broadcast_subscribe___redArg(v_ch_4961_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_4964_, lean_object* v_ch_4965_){
_start:
{
lean_object* v___x_4967_; 
v___x_4967_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4965_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4967_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4967_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
v_a_4976_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4967_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4967_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_4984_, lean_object* v_ch_4985_, lean_object* v_a_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Std_Broadcast_subscribe(v_00_u03b1_4984_, v_ch_4985_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_4988_){
_start:
{
lean_object* v___x_4990_; 
v___x_4990_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_4988_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_4998_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4993_ = v___x_4990_;
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_dec(v___x_4990_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4996_; 
if (v_isShared_4994_ == 0)
{
v___x_4996_ = v___x_4993_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4991_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5016_; 
v_a_4999_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5001_ = v___x_4990_;
v_isShared_5002_ = v_isSharedCheck_5016_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4990_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5016_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
uint8_t v___x_5003_; 
v___x_5003_ = lean_unbox(v_a_4999_);
lean_dec(v_a_4999_);
switch(v___x_5003_)
{
case 0:
{
lean_object* v___x_5004_; lean_object* v___x_5006_; 
v___x_5004_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 0, v___x_5004_);
v___x_5006_ = v___x_5001_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v___x_5004_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
case 1:
{
lean_object* v___x_5008_; lean_object* v___x_5010_; 
v___x_5008_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 0, v___x_5008_);
v___x_5010_ = v___x_5001_;
goto v_reusejp_5009_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_5008_);
v___x_5010_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5009_;
}
v_reusejp_5009_:
{
return v___x_5010_;
}
}
default: 
{
lean_object* v___x_5012_; lean_object* v___x_5014_; 
v___x_5012_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 0, v___x_5012_);
v___x_5014_ = v___x_5001_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___x_5012_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5017_, lean_object* v_a_5018_){
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_Std_Broadcast_close___redArg(v_ch_5017_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5020_, lean_object* v_ch_5021_){
_start:
{
lean_object* v___x_5023_; 
v___x_5023_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5021_);
if (lean_obj_tag(v___x_5023_) == 0)
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
v_a_5024_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_5023_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5023_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
else
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5049_; 
v_a_5032_ = lean_ctor_get(v___x_5023_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5034_ = v___x_5023_;
v_isShared_5035_ = v_isSharedCheck_5049_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5023_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5049_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
uint8_t v___x_5036_; 
v___x_5036_ = lean_unbox(v_a_5032_);
lean_dec(v_a_5032_);
switch(v___x_5036_)
{
case 0:
{
lean_object* v___x_5037_; lean_object* v___x_5039_; 
v___x_5037_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v___x_5037_);
v___x_5039_ = v___x_5034_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
case 1:
{
lean_object* v___x_5041_; lean_object* v___x_5043_; 
v___x_5041_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v___x_5041_);
v___x_5043_ = v___x_5034_;
goto v_reusejp_5042_;
}
else
{
lean_object* v_reuseFailAlloc_5044_; 
v_reuseFailAlloc_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5044_, 0, v___x_5041_);
v___x_5043_ = v_reuseFailAlloc_5044_;
goto v_reusejp_5042_;
}
v_reusejp_5042_:
{
return v___x_5043_;
}
}
default: 
{
lean_object* v___x_5045_; lean_object* v___x_5047_; 
v___x_5045_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v___x_5045_);
v___x_5047_ = v___x_5034_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5045_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
return v___x_5047_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5050_, lean_object* v_ch_5051_, lean_object* v_a_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Std_Broadcast_close(v_00_u03b1_5050_, v_ch_5051_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5054_){
_start:
{
lean_object* v___y_5057_; 
if (lean_obj_tag(v_x_5054_) == 0)
{
lean_object* v_a_5061_; uint8_t v___x_5062_; 
v_a_5061_ = lean_ctor_get(v_x_5054_, 0);
lean_inc(v_a_5061_);
lean_dec_ref_known(v_x_5054_, 1);
v___x_5062_ = lean_unbox(v_a_5061_);
lean_dec(v_a_5061_);
switch(v___x_5062_)
{
case 0:
{
lean_object* v___x_5063_; 
v___x_5063_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5057_ = v___x_5063_;
goto v___jp_5056_;
}
case 1:
{
lean_object* v___x_5064_; 
v___x_5064_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5057_ = v___x_5064_;
goto v___jp_5056_;
}
default: 
{
lean_object* v___x_5065_; 
v___x_5065_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5057_ = v___x_5065_;
goto v___jp_5056_;
}
}
}
else
{
lean_object* v_a_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5074_; 
v_a_5066_ = lean_ctor_get(v_x_5054_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v_x_5054_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5068_ = v_x_5054_;
v_isShared_5069_ = v_isSharedCheck_5074_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_a_5066_);
lean_dec(v_x_5054_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5074_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5071_; 
if (v_isShared_5069_ == 0)
{
v___x_5071_ = v___x_5068_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5066_);
v___x_5071_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
lean_object* v___x_5072_; 
v___x_5072_ = lean_task_pure(v___x_5071_);
return v___x_5072_;
}
}
}
v___jp_5056_:
{
lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
lean_inc_ref(v___y_5057_);
v___x_5058_ = lean_mk_io_user_error(v___y_5057_);
v___x_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5058_);
v___x_5060_ = lean_task_pure(v___x_5059_);
return v___x_5060_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5075_, lean_object* v___y_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5075_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5079_, lean_object* v_v_5080_){
_start:
{
lean_object* v___x_5082_; lean_object* v___f_5083_; lean_object* v___x_5084_; uint8_t v___x_5085_; lean_object* v___x_5086_; 
v___x_5082_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5079_, v_v_5080_);
v___f_5083_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5084_ = lean_unsigned_to_nat(0u);
v___x_5085_ = 1;
v___x_5086_ = lean_io_bind_task(v___x_5082_, v___f_5083_, v___x_5084_, v___x_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5087_, lean_object* v_v_5088_, lean_object* v_a_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Std_Broadcast_send___redArg(v_ch_5087_, v_v_5088_);
return v_res_5090_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5091_, lean_object* v_ch_5092_, lean_object* v_v_5093_){
_start:
{
lean_object* v___x_5095_; lean_object* v___f_5096_; lean_object* v___x_5097_; uint8_t v___x_5098_; lean_object* v___x_5099_; 
v___x_5095_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5092_, v_v_5093_);
v___f_5096_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5097_ = lean_unsigned_to_nat(0u);
v___x_5098_ = 1;
v___x_5099_ = lean_io_bind_task(v___x_5095_, v___f_5096_, v___x_5097_, v___x_5098_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5100_, lean_object* v_ch_5101_, lean_object* v_v_5102_, lean_object* v_a_5103_){
_start:
{
lean_object* v_res_5104_; 
v_res_5104_ = l_Std_Broadcast_send(v_00_u03b1_5100_, v_ch_5101_, v_v_5102_);
return v_res_5104_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5105_){
_start:
{
lean_object* v___x_5107_; 
v___x_5107_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5105_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5108_);
return v_res_5110_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5111_, lean_object* v_ch_5112_){
_start:
{
lean_object* v___x_5114_; 
v___x_5114_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5112_);
return v___x_5114_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5115_, lean_object* v_ch_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5115_, v_ch_5116_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5119_){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5119_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5122_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5125_, lean_object* v_inst_5126_, lean_object* v_ch_5127_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5127_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5130_, lean_object* v_inst_5131_, lean_object* v_ch_5132_, lean_object* v_a_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5130_, v_inst_5131_, v_ch_5132_);
lean_dec(v_inst_5131_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5135_){
_start:
{
lean_object* v___x_5136_; 
v___x_5136_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5135_);
return v___x_5136_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5137_, lean_object* v_inst_5138_, lean_object* v_ch_5139_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5139_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5141_, lean_object* v_inst_5142_, lean_object* v_ch_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5141_, v_inst_5142_, v_ch_5143_);
lean_dec(v_inst_5142_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5145_){
_start:
{
lean_object* v___x_5147_; 
v___x_5147_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5145_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5148_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5151_, lean_object* v_ch_5152_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5152_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5155_, lean_object* v_ch_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v_res_5158_; 
v_res_5158_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5155_, v_ch_5156_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5159_, lean_object* v_ch_5160_, lean_object* v_prio_5161_){
_start:
{
lean_object* v___x_5163_; 
v___x_5163_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5159_, v_ch_5160_, v_prio_5161_);
return v___x_5163_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5164_, lean_object* v_ch_5165_, lean_object* v_prio_5166_, lean_object* v_a_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5164_, v_ch_5165_, v_prio_5166_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5169_, lean_object* v_f_5170_, lean_object* v_ch_5171_, lean_object* v_prio_5172_){
_start:
{
lean_object* v___x_5174_; 
v___x_5174_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5170_, v_ch_5171_, v_prio_5172_);
return v___x_5174_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5175_, lean_object* v_f_5176_, lean_object* v_ch_5177_, lean_object* v_prio_5178_, lean_object* v_a_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5175_, v_f_5176_, v_ch_5177_, v_prio_5178_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5186_, lean_object* v_inst_5187_){
_start:
{
lean_object* v___x_5188_; 
v___x_5188_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_5188_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5189_, lean_object* v_inst_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5189_, v_inst_5190_);
lean_dec(v_inst_5190_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_5192_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5193_, 0, v_a_5192_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_5194_, lean_object* v_x_5195_){
_start:
{
if (lean_obj_tag(v_x_5195_) == 0)
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5205_; 
lean_dec_ref(v___f_5194_);
v_a_5197_ = lean_ctor_get(v_x_5195_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v_x_5195_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5199_ = v_x_5195_;
v_isShared_5200_ = v_isSharedCheck_5205_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v_x_5195_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5205_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
lean_object* v___x_5203_; 
v___x_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5202_);
return v___x_5203_;
}
}
}
else
{
lean_object* v_a_5206_; 
v_a_5206_ = lean_ctor_get(v_x_5195_, 0);
lean_inc(v_a_5206_);
lean_dec_ref_known(v_x_5195_, 1);
if (lean_obj_tag(v_a_5206_) == 0)
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5215_; 
lean_dec_ref(v___f_5194_);
v_a_5207_ = lean_ctor_get(v_a_5206_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v_a_5206_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5209_ = v_a_5206_;
v_isShared_5210_ = v_isSharedCheck_5215_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v_a_5206_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5215_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5212_; 
if (v_isShared_5210_ == 0)
{
v___x_5212_ = v___x_5209_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5214_; 
v_reuseFailAlloc_5214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5207_);
v___x_5212_ = v_reuseFailAlloc_5214_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
lean_object* v___x_5213_; 
v___x_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5213_, 0, v___x_5212_);
return v___x_5213_;
}
}
}
else
{
lean_object* v_a_5216_; lean_object* v___x_5217_; uint8_t v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
v_a_5216_ = lean_ctor_get(v_a_5206_, 0);
lean_inc(v_a_5216_);
lean_dec_ref_known(v_a_5206_, 1);
v___x_5217_ = lean_unsigned_to_nat(0u);
v___x_5218_ = 0;
v___x_5219_ = lean_task_map(v___f_5194_, v_a_5216_, v___x_5217_, v___x_5218_);
v___x_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5219_);
return v___x_5220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_5221_, lean_object* v_x_5222_, lean_object* v___y_5223_){
_start:
{
lean_object* v_res_5224_; 
v_res_5224_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(v___f_5221_, v_x_5222_);
return v_res_5224_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_5225_, lean_object* v_receiver_5226_){
_start:
{
lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; uint8_t v___x_5233_; lean_object* v___x_5234_; 
v___x_5228_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5226_);
v___x_5229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5228_);
v___x_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5229_);
v___x_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5231_, 0, v___x_5230_);
v___x_5232_ = lean_unsigned_to_nat(0u);
v___x_5233_ = 0;
v___x_5234_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5232_, v___x_5233_, v___x_5231_, v___f_5225_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_5235_, lean_object* v_receiver_5236_, lean_object* v___y_5237_){
_start:
{
lean_object* v_res_5238_; 
v_res_5238_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(v___f_5235_, v_receiver_5236_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5244_, lean_object* v_inst_5245_){
_start:
{
lean_object* v___f_5246_; 
v___f_5246_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2));
return v___f_5246_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5247_, lean_object* v_inst_5248_){
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5247_, v_inst_5248_);
lean_dec(v_inst_5248_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__1(lean_object* v_a_5250_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5251_, 0, v_a_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_5256_, lean_object* v_x_5257_){
_start:
{
if (lean_obj_tag(v_x_5257_) == 0)
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5267_; 
lean_dec_ref(v___f_5256_);
v_a_5259_ = lean_ctor_get(v_x_5257_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v_x_5257_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5261_ = v_x_5257_;
v_isShared_5262_ = v_isSharedCheck_5267_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v_x_5257_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5267_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
lean_object* v___x_5265_; 
v___x_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5264_);
return v___x_5265_;
}
}
}
else
{
lean_object* v_a_5268_; lean_object* v___x_5269_; uint8_t v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; 
v_a_5268_ = lean_ctor_get(v_x_5257_, 0);
lean_inc(v_a_5268_);
lean_dec_ref_known(v_x_5257_, 1);
v___x_5269_ = lean_unsigned_to_nat(0u);
v___x_5270_ = 0;
v___x_5271_ = lean_task_map(v___f_5256_, v_a_5268_, v___x_5269_, v___x_5270_);
v___x_5272_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1));
v___x_5273_ = lean_task_map(v___x_5272_, v___x_5271_, v___x_5269_, v___x_5270_);
v___x_5274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5273_);
return v___x_5274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_5275_, lean_object* v_x_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(v___f_5275_, v_x_5276_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5279_, lean_object* v___f_5280_, lean_object* v_receiver_5281_, lean_object* v_x_5282_){
_start:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; uint8_t v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; lean_object* v___x_5291_; 
v___x_5284_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5281_, v_x_5282_);
v___x_5285_ = lean_unsigned_to_nat(0u);
v___x_5286_ = 1;
v___x_5287_ = lean_io_bind_task(v___x_5284_, v___f_5279_, v___x_5285_, v___x_5286_);
v___x_5288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5288_, 0, v___x_5287_);
v___x_5289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5288_);
v___x_5290_ = 0;
v___x_5291_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5285_, v___x_5290_, v___x_5289_, v___f_5280_);
return v___x_5291_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5292_, lean_object* v___f_5293_, lean_object* v_receiver_5294_, lean_object* v_x_5295_, lean_object* v___y_5296_){
_start:
{
lean_object* v_res_5297_; 
v_res_5297_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(v___f_5292_, v___f_5293_, v_receiver_5294_, v_x_5295_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(lean_object* v_x_5298_){
_start:
{
lean_object* v___x_5300_; 
v___x_5300_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5300_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v_x_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(v_x_5301_);
lean_dec_ref(v_x_5301_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_5304_, lean_object* v_socket_5305_, lean_object* v_x_5306_, lean_object* v___y_5307_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = lean_apply_3(v___f_5304_, v_socket_5305_, v___y_5307_, lean_box(0));
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_5310_, lean_object* v_socket_5311_, lean_object* v_x_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(v___f_5310_, v_socket_5311_, v_x_5312_, v___y_5313_);
return v_res_5315_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(lean_object* v___f_5316_, lean_object* v___x_5317_, lean_object* v_socket_5318_, lean_object* v_data_5319_){
_start:
{
lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; uint8_t v___x_5324_; 
v___x_5321_ = lean_unsigned_to_nat(0u);
v___x_5322_ = lean_array_get_size(v_data_5319_);
v___x_5323_ = lean_box(0);
v___x_5324_ = lean_nat_dec_lt(v___x_5321_, v___x_5322_);
if (v___x_5324_ == 0)
{
lean_object* v___x_5325_; 
lean_dec_ref(v_data_5319_);
lean_dec_ref(v_socket_5318_);
lean_dec_ref(v___x_5317_);
lean_dec_ref(v___f_5316_);
v___x_5325_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5325_;
}
else
{
lean_object* v___f_5326_; uint8_t v___x_5327_; 
v___f_5326_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5326_, 0, v___f_5316_);
lean_closure_set(v___f_5326_, 1, v_socket_5318_);
v___x_5327_ = lean_nat_dec_le(v___x_5322_, v___x_5322_);
if (v___x_5327_ == 0)
{
if (v___x_5324_ == 0)
{
lean_object* v___x_5328_; 
lean_dec_ref(v___f_5326_);
lean_dec_ref(v_data_5319_);
lean_dec_ref(v___x_5317_);
v___x_5328_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5328_;
}
else
{
size_t v___x_5329_; size_t v___x_5330_; lean_object* v___x_891__overap_5331_; lean_object* v___x_5332_; 
v___x_5329_ = ((size_t)0ULL);
v___x_5330_ = lean_usize_of_nat(v___x_5322_);
v___x_891__overap_5331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5317_, v___f_5326_, v_data_5319_, v___x_5329_, v___x_5330_, v___x_5323_);
v___x_5332_ = lean_apply_1(v___x_891__overap_5331_, lean_box(0));
return v___x_5332_;
}
}
else
{
size_t v___x_5333_; size_t v___x_5334_; lean_object* v___x_894__overap_5335_; lean_object* v___x_5336_; 
v___x_5333_ = ((size_t)0ULL);
v___x_5334_ = lean_usize_of_nat(v___x_5322_);
v___x_894__overap_5335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5317_, v___f_5326_, v_data_5319_, v___x_5333_, v___x_5334_, v___x_5323_);
v___x_5336_ = lean_apply_1(v___x_894__overap_5335_, lean_box(0));
return v___x_5336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed(lean_object* v___f_5337_, lean_object* v___x_5338_, lean_object* v_socket_5339_, lean_object* v_data_5340_, lean_object* v___y_5341_){
_start:
{
lean_object* v_res_5342_; 
v_res_5342_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(v___f_5337_, v___x_5338_, v_socket_5339_, v_data_5340_);
return v_res_5342_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_5350_; 
v___x_5350_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_5350_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___x_5351_; lean_object* v___f_5352_; lean_object* v___f_5353_; 
v___x_5351_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4);
v___f_5352_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___f_5353_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed), 5, 2);
lean_closure_set(v___f_5353_, 0, v___f_5352_);
lean_closure_set(v___f_5353_, 1, v___x_5351_);
return v___f_5353_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6(void){
_start:
{
lean_object* v___f_5354_; lean_object* v___f_5355_; lean_object* v___f_5356_; lean_object* v___x_5357_; 
v___f_5354_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3));
v___f_5355_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5);
v___f_5356_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___x_5357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5357_, 0, v___f_5356_);
lean_ctor_set(v___x_5357_, 1, v___f_5355_);
lean_ctor_set(v___x_5357_, 2, v___f_5354_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5358_, lean_object* v_inst_5359_){
_start:
{
lean_object* v___x_5360_; 
v___x_5360_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6);
return v___x_5360_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5361_, lean_object* v_inst_5362_){
_start:
{
lean_object* v_res_5363_; 
v_res_5363_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5361_, v_inst_5362_);
lean_dec(v_inst_5362_);
return v_res_5363_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5364_; 
v___x_5364_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5364_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5365_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5365_);
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5368_, lean_object* v_a_5369_){
_start:
{
lean_object* v_res_5370_; 
v_res_5370_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5368_);
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5371_, lean_object* v_capacity_5372_, lean_object* v_h_5373_){
_start:
{
lean_object* v___x_5375_; 
v___x_5375_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5372_);
return v___x_5375_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5376_, lean_object* v_capacity_5377_, lean_object* v_h_5378_, lean_object* v_a_5379_){
_start:
{
lean_object* v_res_5380_; 
v_res_5380_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5376_, v_capacity_5377_, v_h_5378_);
return v_res_5380_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5381_, lean_object* v_v_5382_){
_start:
{
lean_object* v___x_5384_; 
v___x_5384_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5381_, v_v_5382_);
return v___x_5384_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5385_, lean_object* v_v_5386_, lean_object* v_a_5387_){
_start:
{
lean_object* v_res_5388_; 
v_res_5388_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5385_, v_v_5386_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5389_, lean_object* v_ch_5390_, lean_object* v_v_5391_){
_start:
{
lean_object* v___x_5393_; 
v___x_5393_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5390_, v_v_5391_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5394_, lean_object* v_ch_5395_, lean_object* v_v_5396_, lean_object* v_a_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5394_, v_ch_5395_, v_v_5396_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5400_, lean_object* v_v_5401_){
_start:
{
lean_object* v___x_5403_; lean_object* v___f_5404_; lean_object* v___x_5405_; uint8_t v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5403_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5400_, v_v_5401_);
v___f_5404_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5405_ = lean_unsigned_to_nat(0u);
v___x_5406_ = 1;
v___x_5407_ = lean_io_bind_task(v___x_5403_, v___f_5404_, v___x_5405_, v___x_5406_);
v___x_5408_ = lean_io_wait(v___x_5407_);
v___x_5409_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5410_ = l_IO_ofExcept___redArg(v___x_5409_, v___x_5408_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5411_, lean_object* v_v_5412_, lean_object* v_a_5413_){
_start:
{
lean_object* v_res_5414_; 
v_res_5414_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5411_, v_v_5412_);
return v_res_5414_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5415_, lean_object* v_ch_5416_, lean_object* v_v_5417_){
_start:
{
lean_object* v___x_5419_; lean_object* v___f_5420_; lean_object* v___x_5421_; uint8_t v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5419_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5416_, v_v_5417_);
v___f_5420_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5421_ = lean_unsigned_to_nat(0u);
v___x_5422_ = 1;
v___x_5423_ = lean_io_bind_task(v___x_5419_, v___f_5420_, v___x_5421_, v___x_5422_);
v___x_5424_ = lean_io_wait(v___x_5423_);
v___x_5425_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5426_ = l_IO_ofExcept___redArg(v___x_5425_, v___x_5424_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5427_, lean_object* v_ch_5428_, lean_object* v_v_5429_, lean_object* v_a_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5427_, v_ch_5428_, v_v_5429_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5432_){
_start:
{
lean_object* v___x_5434_; 
v___x_5434_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5432_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5435_, lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5435_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5438_, lean_object* v_ch_5439_){
_start:
{
lean_object* v___x_5441_; 
v___x_5441_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5439_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5442_, lean_object* v_ch_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5442_, v_ch_5443_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5446_){
_start:
{
lean_object* v___x_5448_; lean_object* v___x_5449_; 
v___x_5448_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5446_);
v___x_5449_ = lean_io_wait(v___x_5448_);
return v___x_5449_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5450_, lean_object* v_a_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5450_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5453_, lean_object* v_inst_5454_, lean_object* v_ch_5455_){
_start:
{
lean_object* v___x_5457_; 
v___x_5457_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5458_, lean_object* v_inst_5459_, lean_object* v_ch_5460_, lean_object* v_a_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5458_, v_inst_5459_, v_ch_5460_);
lean_dec(v_inst_5459_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5463_, lean_object* v_b_5464_, lean_object* v_f_5465_, lean_object* v_toBind_5466_, lean_object* v___f_5467_, lean_object* v_a_5468_){
_start:
{
if (lean_obj_tag(v_a_5468_) == 0)
{
lean_object* v___x_5469_; 
lean_dec(v___f_5467_);
lean_dec(v_toBind_5466_);
lean_dec(v_f_5465_);
v___x_5469_ = lean_apply_2(v_toPure_5463_, lean_box(0), v_b_5464_);
return v___x_5469_;
}
else
{
lean_object* v_val_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; 
lean_dec(v_toPure_5463_);
v_val_5470_ = lean_ctor_get(v_a_5468_, 0);
lean_inc(v_val_5470_);
lean_dec_ref_known(v_a_5468_, 1);
v___x_5471_ = lean_apply_2(v_f_5465_, v_val_5470_, v_b_5464_);
v___x_5472_ = lean_apply_4(v_toBind_5466_, lean_box(0), lean_box(0), v___x_5471_, v___f_5467_);
return v___x_5472_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5473_, lean_object* v_inst_5474_, lean_object* v_inst_5475_, lean_object* v_ch_5476_, lean_object* v_f_5477_, lean_object* v_b_5478_){
_start:
{
lean_object* v_toApplicative_5479_; lean_object* v_toBind_5480_; lean_object* v_toPure_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___f_5484_; lean_object* v___f_5485_; lean_object* v___x_5486_; 
v_toApplicative_5479_ = lean_ctor_get(v_inst_5474_, 0);
v_toBind_5480_ = lean_ctor_get(v_inst_5474_, 1);
lean_inc_n(v_toBind_5480_, 2);
v_toPure_5481_ = lean_ctor_get(v_toApplicative_5479_, 1);
lean_inc_n(v_toPure_5481_, 2);
lean_inc_ref(v_ch_5476_);
lean_inc(v_inst_5473_);
v___x_5482_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5482_, 0, lean_box(0));
lean_closure_set(v___x_5482_, 1, v_inst_5473_);
lean_closure_set(v___x_5482_, 2, v_ch_5476_);
lean_inc(v_inst_5475_);
v___x_5483_ = lean_apply_2(v_inst_5475_, lean_box(0), v___x_5482_);
lean_inc(v_f_5477_);
v___f_5484_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5484_, 0, v_toPure_5481_);
lean_closure_set(v___f_5484_, 1, v_inst_5473_);
lean_closure_set(v___f_5484_, 2, v_inst_5474_);
lean_closure_set(v___f_5484_, 3, v_inst_5475_);
lean_closure_set(v___f_5484_, 4, v_ch_5476_);
lean_closure_set(v___f_5484_, 5, v_f_5477_);
v___f_5485_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5485_, 0, v_toPure_5481_);
lean_closure_set(v___f_5485_, 1, v_b_5478_);
lean_closure_set(v___f_5485_, 2, v_f_5477_);
lean_closure_set(v___f_5485_, 3, v_toBind_5480_);
lean_closure_set(v___f_5485_, 4, v___f_5484_);
v___x_5486_ = lean_apply_4(v_toBind_5480_, lean_box(0), lean_box(0), v___x_5483_, v___f_5485_);
return v___x_5486_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5487_, lean_object* v_inst_5488_, lean_object* v_inst_5489_, lean_object* v_inst_5490_, lean_object* v_ch_5491_, lean_object* v_f_5492_, lean_object* v_____do__lift_5493_){
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
v___x_5497_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5488_, v_inst_5489_, v_inst_5490_, v_ch_5491_, v_f_5492_, v_a_5496_);
return v___x_5497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5498_, lean_object* v_m_5499_, lean_object* v_00_u03b2_5500_, lean_object* v_inst_5501_, lean_object* v_inst_5502_, lean_object* v_inst_5503_, lean_object* v_ch_5504_, lean_object* v_f_5505_, lean_object* v_b_5506_){
_start:
{
lean_object* v___x_5507_; 
v___x_5507_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5501_, v_inst_5502_, v_inst_5503_, v_ch_5504_, v_f_5505_, v_b_5506_);
return v___x_5507_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5508_, lean_object* v_inst_5509_, lean_object* v_inst_5510_, lean_object* v_00_u03b2_5511_, lean_object* v_ch_5512_, lean_object* v_b_5513_, lean_object* v_f_5514_){
_start:
{
lean_object* v___x_5515_; 
v___x_5515_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5508_, v_inst_5509_, v_inst_5510_, v_ch_5512_, v_f_5514_, v_b_5513_);
return v___x_5515_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5516_, lean_object* v_inst_5517_, lean_object* v_inst_5518_){
_start:
{
lean_object* v___f_5519_; 
v___f_5519_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5519_, 0, v_inst_5516_);
lean_closure_set(v___f_5519_, 1, v_inst_5517_);
lean_closure_set(v___f_5519_, 2, v_inst_5518_);
return v___f_5519_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5520_, lean_object* v_m_5521_, lean_object* v_inst_5522_, lean_object* v_inst_5523_, lean_object* v_inst_5524_){
_start:
{
lean_object* v___f_5525_; 
v___f_5525_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5525_, 0, v_inst_5522_);
lean_closure_set(v___f_5525_, 1, v_inst_5523_);
lean_closure_set(v___f_5525_, 2, v_inst_5524_);
return v___f_5525_;
}
}
lean_object* runtime_initialize_Std_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Broadcast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_Broadcast(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1 = _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1();
lean_mark_persistent(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1);
l_Std_Broadcast_new___auto__1 = _init_l_Std_Broadcast_new___auto__1();
lean_mark_persistent(l_Std_Broadcast_new___auto__1);
l_Std_Broadcast_Sync_new___auto__3 = _init_l_Std_Broadcast_Sync_new___auto__3();
lean_mark_persistent(l_Std_Broadcast_Sync_new___auto__3);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data(uint8_t builtin);
lean_object* initialize_Init_Data_Queue(uint8_t builtin);
lean_object* initialize_Init_Data_Vector(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* initialize_Std_Async_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_Broadcast(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Broadcast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_Broadcast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_Broadcast(builtin);
}
#ifdef __cplusplus
}
#endif

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
uint8_t v_x_177__boxed_112_; lean_object* v_res_113_; 
v_x_177__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Std_Broadcast_instReprError_repr(v_x_177__boxed_112_, v_prec_111_);
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
uint8_t v_x_13__boxed_134_; uint8_t v_y_14__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_x_13__boxed_134_ = lean_unbox(v_x_132_);
v_y_14__boxed_135_ = lean_unbox(v_y_133_);
v_res_136_ = l_Std_Broadcast_instDecidableEqError(v_x_13__boxed_134_, v_y_14__boxed_135_);
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
v___x_712_ = lean_nat_add(v___y_709_, v___y_711_);
lean_dec(v___y_711_);
lean_dec(v___y_709_);
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
lean_ctor_set(v___x_692_, 3, v___y_710_);
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
lean_ctor_set(v_reuseFailAlloc_717_, 3, v___y_710_);
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
v___y_709_ = v___x_725_;
v___y_710_ = v___x_724_;
v___y_711_ = v_size_726_;
goto v___jp_708_;
}
else
{
lean_object* v___x_727_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___y_709_ = v___x_725_;
v___y_710_ = v___x_724_;
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
uint8_t v___x_1435__boxed_1357_; size_t v_sz_boxed_1358_; size_t v_i_boxed_1359_; lean_object* v_res_1360_; 
v___x_1435__boxed_1357_ = lean_unbox(v___x_1351_);
v_sz_boxed_1358_ = lean_unbox_usize(v_sz_1353_);
lean_dec(v_sz_1353_);
v_i_boxed_1359_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1435__boxed_1357_, v_as_1352_, v_sz_boxed_1358_, v_i_boxed_1359_, v_b_1355_);
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
uint8_t v___x_1531__boxed_1437_; size_t v_sz_boxed_1438_; size_t v_i_boxed_1439_; lean_object* v_res_1440_; 
v___x_1531__boxed_1437_ = lean_unbox(v___x_1430_);
v_sz_boxed_1438_ = lean_unbox_usize(v_sz_1432_);
lean_dec(v_sz_1432_);
v_i_boxed_1439_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_res_1440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1429_, v___x_1531__boxed_1437_, v_as_1431_, v_sz_boxed_1438_, v_i_boxed_1439_, v_b_1434_, v___y_1435_);
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
uint8_t v___x_1069__boxed_1631_; lean_object* v_res_1632_; 
v___x_1069__boxed_1631_ = lean_unbox(v___x_1628_);
v_res_1632_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1623_, v_inst_1624_, v_toBind_1625_, v_a_1626_, v_a_1627_, v___x_1069__boxed_1631_, v_inst_1629_, v_a_1630_);
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
lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1912_; 
v_fst_1874_ = lean_ctor_get(v_a_1871_, 0);
v_snd_1875_ = lean_ctor_get(v_a_1871_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_a_1871_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1877_ = v_a_1871_;
v_isShared_1878_ = v_isSharedCheck_1912_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_snd_1875_);
lean_inc(v_fst_1874_);
lean_dec(v_a_1871_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1912_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_size_1884_; lean_object* v_pos_1885_; uint8_t v___x_1886_; 
v_size_1884_ = lean_ctor_get(v_fst_1874_, 3);
v_pos_1885_ = lean_ctor_get(v_fst_1874_, 9);
v___x_1886_ = lean_nat_dec_lt(v_snd_1875_, v_pos_1885_);
if (v___x_1886_ == 0)
{
goto v___jp_1879_;
}
else
{
lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = lean_nat_dec_lt(v___x_1887_, v_size_1884_);
if (v___x_1888_ == 0)
{
goto v___jp_1879_;
}
else
{
lean_object* v___x_1889_; 
lean_del_object(v___x_1877_);
v___x_1889_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_1875_, v___y_1872_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1903_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1903_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1903_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
if (lean_obj_tag(v_a_1890_) == 1)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref_known(v_a_1890_, 1);
lean_del_object(v___x_1892_);
lean_dec(v_fst_1874_);
v___x_1894_ = lean_st_ref_get(v___y_1872_);
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = lean_nat_add(v_snd_1875_, v___x_1895_);
lean_dec(v_snd_1875_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1894_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v_a_1871_ = v___x_1897_;
goto _start;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_dec(v_a_1890_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_fst_1874_);
lean_ctor_set(v___x_1899_, 1, v_snd_1875_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1899_);
v___x_1901_ = v___x_1892_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_snd_1875_);
lean_dec(v_fst_1874_);
v_a_1904_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1889_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1889_);
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
v___jp_1879_:
{
lean_object* v___x_1881_; 
if (v_isShared_1878_ == 0)
{
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_fst_1874_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_snd_1875_);
v___x_1881_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_a_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_1913_, v___y_1914_);
lean_dec(v___y_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_1917_, lean_object* v_k_1918_){
_start:
{
if (lean_obj_tag(v_t_1917_) == 0)
{
lean_object* v_k_1919_; lean_object* v_v_1920_; lean_object* v_l_1921_; lean_object* v_r_1922_; uint8_t v___x_1923_; 
v_k_1919_ = lean_ctor_get(v_t_1917_, 1);
v_v_1920_ = lean_ctor_get(v_t_1917_, 2);
v_l_1921_ = lean_ctor_get(v_t_1917_, 3);
v_r_1922_ = lean_ctor_get(v_t_1917_, 4);
v___x_1923_ = lean_nat_dec_lt(v_k_1918_, v_k_1919_);
if (v___x_1923_ == 0)
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_nat_dec_eq(v_k_1918_, v_k_1919_);
if (v___x_1924_ == 0)
{
v_t_1917_ = v_r_1922_;
goto _start;
}
else
{
lean_object* v___x_1926_; 
lean_inc(v_v_1920_);
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_v_1920_);
return v___x_1926_;
}
}
else
{
v_t_1917_ = v_l_1921_;
goto _start;
}
}
else
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_box(0);
return v___x_1928_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_1929_, lean_object* v_k_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_1929_, v_k_1930_);
lean_dec(v_k_1930_);
lean_dec(v_t_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_1932_, lean_object* v_t_1933_){
_start:
{
if (lean_obj_tag(v_t_1933_) == 0)
{
lean_object* v_k_1934_; lean_object* v_v_1935_; lean_object* v_l_1936_; lean_object* v_r_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_2592_; 
v_k_1934_ = lean_ctor_get(v_t_1933_, 1);
v_v_1935_ = lean_ctor_get(v_t_1933_, 2);
v_l_1936_ = lean_ctor_get(v_t_1933_, 3);
v_r_1937_ = lean_ctor_get(v_t_1933_, 4);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_t_1933_);
if (v_isSharedCheck_2592_ == 0)
{
lean_object* v_unused_2593_; 
v_unused_2593_ = lean_ctor_get(v_t_1933_, 0);
lean_dec(v_unused_2593_);
v___x_1939_ = v_t_1933_;
v_isShared_1940_ = v_isSharedCheck_2592_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_r_1937_);
lean_inc(v_l_1936_);
lean_inc(v_v_1935_);
lean_inc(v_k_1934_);
lean_dec(v_t_1933_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_2592_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_nat_dec_lt(v_k_1932_, v_k_1934_);
if (v___x_1941_ == 0)
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_nat_dec_eq(v_k_1932_, v_k_1934_);
if (v___x_1942_ == 0)
{
lean_object* v_impl_1943_; lean_object* v___x_1944_; 
v_impl_1943_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1932_, v_r_1937_);
v___x_1944_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1943_) == 0)
{
if (lean_obj_tag(v_l_1936_) == 0)
{
lean_object* v_size_1945_; lean_object* v_size_1946_; lean_object* v_k_1947_; lean_object* v_v_1948_; lean_object* v_l_1949_; lean_object* v_r_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v_size_1945_ = lean_ctor_get(v_impl_1943_, 0);
lean_inc(v_size_1945_);
v_size_1946_ = lean_ctor_get(v_l_1936_, 0);
v_k_1947_ = lean_ctor_get(v_l_1936_, 1);
v_v_1948_ = lean_ctor_get(v_l_1936_, 2);
v_l_1949_ = lean_ctor_get(v_l_1936_, 3);
v_r_1950_ = lean_ctor_get(v_l_1936_, 4);
lean_inc(v_r_1950_);
v___x_1951_ = lean_unsigned_to_nat(3u);
v___x_1952_ = lean_nat_mul(v___x_1951_, v_size_1945_);
v___x_1953_ = lean_nat_dec_lt(v___x_1952_, v_size_1946_);
lean_dec(v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_dec(v_r_1950_);
v___x_1954_ = lean_nat_add(v___x_1944_, v_size_1946_);
v___x_1955_ = lean_nat_add(v___x_1954_, v_size_1945_);
lean_dec(v_size_1945_);
lean_dec(v___x_1954_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_impl_1943_);
lean_ctor_set(v___x_1939_, 0, v___x_1955_);
v___x_1957_ = v___x_1939_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_l_1936_);
lean_ctor_set(v_reuseFailAlloc_1958_, 4, v_impl_1943_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
else
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_2024_; 
lean_inc(v_l_1949_);
lean_inc(v_v_1948_);
lean_inc(v_k_1947_);
lean_inc(v_size_1946_);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_l_1936_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; lean_object* v_unused_2026_; lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; 
v_unused_2025_ = lean_ctor_get(v_l_1936_, 4);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_l_1936_, 3);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_l_1936_, 2);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_l_1936_, 1);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_l_1936_, 0);
lean_dec(v_unused_2029_);
v___x_1960_ = v_l_1936_;
v_isShared_1961_ = v_isSharedCheck_2024_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v_l_1936_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_2024_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_size_1962_; lean_object* v_size_1963_; lean_object* v_k_1964_; lean_object* v_v_1965_; lean_object* v_l_1966_; lean_object* v_r_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_size_1962_ = lean_ctor_get(v_l_1949_, 0);
v_size_1963_ = lean_ctor_get(v_r_1950_, 0);
v_k_1964_ = lean_ctor_get(v_r_1950_, 1);
v_v_1965_ = lean_ctor_get(v_r_1950_, 2);
v_l_1966_ = lean_ctor_get(v_r_1950_, 3);
v_r_1967_ = lean_ctor_get(v_r_1950_, 4);
v___x_1968_ = lean_unsigned_to_nat(2u);
v___x_1969_ = lean_nat_mul(v___x_1968_, v_size_1962_);
v___x_1970_ = lean_nat_dec_lt(v_size_1963_, v___x_1969_);
lean_dec(v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1999_; 
lean_inc(v_r_1967_);
lean_inc(v_l_1966_);
lean_inc(v_v_1965_);
lean_inc(v_k_1964_);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; lean_object* v_unused_2001_; lean_object* v_unused_2002_; lean_object* v_unused_2003_; lean_object* v_unused_2004_; 
v_unused_2000_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2000_);
v_unused_2001_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2001_);
v_unused_2002_ = lean_ctor_get(v_r_1950_, 2);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_r_1950_, 1);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_r_1950_, 0);
lean_dec(v_unused_2004_);
v___x_1972_ = v_r_1950_;
v_isShared_1973_ = v_isSharedCheck_1999_;
goto v_resetjp_1971_;
}
else
{
lean_dec(v_r_1950_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1999_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___x_1987_; lean_object* v___y_1989_; 
v___x_1974_ = lean_nat_add(v___x_1944_, v_size_1946_);
lean_dec(v_size_1946_);
v___x_1975_ = lean_nat_add(v___x_1974_, v_size_1945_);
lean_dec(v___x_1974_);
v___x_1987_ = lean_nat_add(v___x_1944_, v_size_1962_);
if (lean_obj_tag(v_l_1966_) == 0)
{
lean_object* v_size_1997_; 
v_size_1997_ = lean_ctor_get(v_l_1966_, 0);
lean_inc(v_size_1997_);
v___y_1989_ = v_size_1997_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_unsigned_to_nat(0u);
v___y_1989_ = v___x_1998_;
goto v___jp_1988_;
}
v___jp_1976_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = lean_nat_add(v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec(v___y_1978_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 4, v_impl_1943_);
lean_ctor_set(v___x_1972_, 3, v_r_1967_);
lean_ctor_set(v___x_1972_, 2, v_v_1935_);
lean_ctor_set(v___x_1972_, 1, v_k_1934_);
lean_ctor_set(v___x_1972_, 0, v___x_1980_);
v___x_1982_ = v___x_1972_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_r_1967_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_impl_1943_);
v___x_1982_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 4, v___x_1982_);
lean_ctor_set(v___x_1960_, 3, v___y_1977_);
lean_ctor_set(v___x_1960_, 2, v_v_1965_);
lean_ctor_set(v___x_1960_, 1, v_k_1964_);
lean_ctor_set(v___x_1960_, 0, v___x_1975_);
v___x_1984_ = v___x_1960_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_k_1964_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_v_1965_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v___y_1977_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
v___jp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1990_ = lean_nat_add(v___x_1987_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec(v___x_1987_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_l_1966_);
lean_ctor_set(v___x_1939_, 3, v_l_1949_);
lean_ctor_set(v___x_1939_, 2, v_v_1948_);
lean_ctor_set(v___x_1939_, 1, v_k_1947_);
lean_ctor_set(v___x_1939_, 0, v___x_1990_);
v___x_1992_ = v___x_1939_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_l_1949_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v_l_1966_);
v___x_1992_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_nat_add(v___x_1944_, v_size_1945_);
lean_dec(v_size_1945_);
if (lean_obj_tag(v_r_1967_) == 0)
{
lean_object* v_size_1994_; 
v_size_1994_ = lean_ctor_get(v_r_1967_, 0);
lean_inc(v_size_1994_);
v___y_1977_ = v___x_1992_;
v___y_1978_ = v___x_1993_;
v___y_1979_ = v_size_1994_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_unsigned_to_nat(0u);
v___y_1977_ = v___x_1992_;
v___y_1978_ = v___x_1993_;
v___y_1979_ = v___x_1995_;
goto v___jp_1976_;
}
}
}
}
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
lean_del_object(v___x_1939_);
v___x_2005_ = lean_nat_add(v___x_1944_, v_size_1946_);
lean_dec(v_size_1946_);
v___x_2006_ = lean_nat_add(v___x_2005_, v_size_1945_);
lean_dec(v___x_2005_);
v___x_2007_ = lean_nat_add(v___x_1944_, v_size_1945_);
lean_dec(v_size_1945_);
v___x_2008_ = lean_nat_add(v___x_2007_, v_size_1963_);
lean_dec(v___x_2007_);
lean_inc_ref(v_impl_1943_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 4, v_impl_1943_);
lean_ctor_set(v___x_1960_, 3, v_r_1950_);
lean_ctor_set(v___x_1960_, 2, v_v_1935_);
lean_ctor_set(v___x_1960_, 1, v_k_1934_);
lean_ctor_set(v___x_1960_, 0, v___x_2008_);
v___x_2010_ = v___x_1960_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_r_1950_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v_impl_1943_);
v___x_2010_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_isSharedCheck_2017_ = !lean_is_exclusive(v_impl_1943_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; lean_object* v_unused_2019_; lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; 
v_unused_2018_ = lean_ctor_get(v_impl_1943_, 4);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_impl_1943_, 3);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_impl_1943_, 2);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_impl_1943_, 1);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_impl_1943_, 0);
lean_dec(v_unused_2022_);
v___x_2012_ = v_impl_1943_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_dec(v_impl_1943_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 4, v___x_2010_);
lean_ctor_set(v___x_2012_, 3, v_l_1949_);
lean_ctor_set(v___x_2012_, 2, v_v_1948_);
lean_ctor_set(v___x_2012_, 1, v_k_1947_);
lean_ctor_set(v___x_2012_, 0, v___x_2006_);
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_l_1949_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v___x_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v_size_2030_ = lean_ctor_get(v_impl_1943_, 0);
lean_inc(v_size_2030_);
v___x_2031_ = lean_nat_add(v___x_1944_, v_size_2030_);
lean_dec(v_size_2030_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_impl_1943_);
lean_ctor_set(v___x_1939_, 0, v___x_2031_);
v___x_2033_ = v___x_1939_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_l_1936_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_impl_1943_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
else
{
if (lean_obj_tag(v_l_1936_) == 0)
{
lean_object* v_l_2035_; 
v_l_2035_ = lean_ctor_get(v_l_1936_, 3);
if (lean_obj_tag(v_l_2035_) == 0)
{
lean_object* v_r_2036_; 
lean_inc_ref(v_l_2035_);
v_r_2036_ = lean_ctor_get(v_l_1936_, 4);
lean_inc(v_r_2036_);
if (lean_obj_tag(v_r_2036_) == 0)
{
lean_object* v_size_2037_; lean_object* v_k_2038_; lean_object* v_v_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2052_; 
v_size_2037_ = lean_ctor_get(v_l_1936_, 0);
v_k_2038_ = lean_ctor_get(v_l_1936_, 1);
v_v_2039_ = lean_ctor_get(v_l_1936_, 2);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_l_1936_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; lean_object* v_unused_2054_; 
v_unused_2053_ = lean_ctor_get(v_l_1936_, 4);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_l_1936_, 3);
lean_dec(v_unused_2054_);
v___x_2041_ = v_l_1936_;
v_isShared_2042_ = v_isSharedCheck_2052_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_v_2039_);
lean_inc(v_k_2038_);
lean_inc(v_size_2037_);
lean_dec(v_l_1936_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2052_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v_size_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
v_size_2043_ = lean_ctor_get(v_r_2036_, 0);
v___x_2044_ = lean_nat_add(v___x_1944_, v_size_2037_);
lean_dec(v_size_2037_);
v___x_2045_ = lean_nat_add(v___x_1944_, v_size_2043_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 4, v_impl_1943_);
lean_ctor_set(v___x_2041_, 3, v_r_2036_);
lean_ctor_set(v___x_2041_, 2, v_v_1935_);
lean_ctor_set(v___x_2041_, 1, v_k_1934_);
lean_ctor_set(v___x_2041_, 0, v___x_2045_);
v___x_2047_ = v___x_2041_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_r_2036_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_impl_1943_);
v___x_2047_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2049_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v___x_2047_);
lean_ctor_set(v___x_1939_, 3, v_l_2035_);
lean_ctor_set(v___x_1939_, 2, v_v_2039_);
lean_ctor_set(v___x_1939_, 1, v_k_2038_);
lean_ctor_set(v___x_1939_, 0, v___x_2044_);
v___x_2049_ = v___x_1939_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_k_2038_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_v_2039_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_k_2055_; lean_object* v_v_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2067_; 
v_k_2055_ = lean_ctor_get(v_l_1936_, 1);
v_v_2056_ = lean_ctor_get(v_l_1936_, 2);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_l_1936_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; lean_object* v_unused_2069_; lean_object* v_unused_2070_; 
v_unused_2068_ = lean_ctor_get(v_l_1936_, 4);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_l_1936_, 3);
lean_dec(v_unused_2069_);
v_unused_2070_ = lean_ctor_get(v_l_1936_, 0);
lean_dec(v_unused_2070_);
v___x_2058_ = v_l_1936_;
v_isShared_2059_ = v_isSharedCheck_2067_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_v_2056_);
lean_inc(v_k_2055_);
lean_dec(v_l_1936_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2067_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_unsigned_to_nat(3u);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 3, v_r_2036_);
lean_ctor_set(v___x_2058_, 2, v_v_1935_);
lean_ctor_set(v___x_2058_, 1, v_k_1934_);
lean_ctor_set(v___x_2058_, 0, v___x_1944_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2066_, 3, v_r_2036_);
lean_ctor_set(v_reuseFailAlloc_2066_, 4, v_r_2036_);
v___x_2062_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2064_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v___x_2062_);
lean_ctor_set(v___x_1939_, 3, v_l_2035_);
lean_ctor_set(v___x_1939_, 2, v_v_2056_);
lean_ctor_set(v___x_1939_, 1, v_k_2055_);
lean_ctor_set(v___x_1939_, 0, v___x_2060_);
v___x_2064_ = v___x_1939_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_k_2055_);
lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_v_2056_);
lean_ctor_set(v_reuseFailAlloc_2065_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2065_, 4, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
else
{
lean_object* v_r_2071_; 
v_r_2071_ = lean_ctor_get(v_l_1936_, 4);
lean_inc(v_r_2071_);
if (lean_obj_tag(v_r_2071_) == 0)
{
lean_object* v_k_2072_; lean_object* v_v_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2096_; 
lean_inc(v_l_2035_);
v_k_2072_ = lean_ctor_get(v_l_1936_, 1);
v_v_2073_ = lean_ctor_get(v_l_1936_, 2);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_l_1936_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; lean_object* v_unused_2098_; lean_object* v_unused_2099_; 
v_unused_2097_ = lean_ctor_get(v_l_1936_, 4);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_l_1936_, 3);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_l_1936_, 0);
lean_dec(v_unused_2099_);
v___x_2075_ = v_l_1936_;
v_isShared_2076_ = v_isSharedCheck_2096_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_v_2073_);
lean_inc(v_k_2072_);
lean_dec(v_l_1936_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2096_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v_k_2077_; lean_object* v_v_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2092_; 
v_k_2077_ = lean_ctor_get(v_r_2071_, 1);
v_v_2078_ = lean_ctor_get(v_r_2071_, 2);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_r_2071_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; lean_object* v_unused_2094_; lean_object* v_unused_2095_; 
v_unused_2093_ = lean_ctor_get(v_r_2071_, 4);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_r_2071_, 3);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_r_2071_, 0);
lean_dec(v_unused_2095_);
v___x_2080_ = v_r_2071_;
v_isShared_2081_ = v_isSharedCheck_2092_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_v_2078_);
lean_inc(v_k_2077_);
lean_dec(v_r_2071_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2092_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2082_ = lean_unsigned_to_nat(3u);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 4, v_l_2035_);
lean_ctor_set(v___x_2080_, 3, v_l_2035_);
lean_ctor_set(v___x_2080_, 2, v_v_2073_);
lean_ctor_set(v___x_2080_, 1, v_k_2072_);
lean_ctor_set(v___x_2080_, 0, v___x_1944_);
v___x_2084_ = v___x_2080_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_k_2072_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_v_2073_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v_l_2035_);
v___x_2084_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 4, v_l_2035_);
lean_ctor_set(v___x_2075_, 2, v_v_1935_);
lean_ctor_set(v___x_2075_, 1, v_k_1934_);
lean_ctor_set(v___x_2075_, 0, v___x_1944_);
v___x_2086_ = v___x_2075_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_l_2035_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v_l_2035_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v___x_2086_);
lean_ctor_set(v___x_1939_, 3, v___x_2084_);
lean_ctor_set(v___x_1939_, 2, v_v_2078_);
lean_ctor_set(v___x_1939_, 1, v_k_2077_);
lean_ctor_set(v___x_1939_, 0, v___x_2082_);
v___x_2088_ = v___x_1939_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2089_, 3, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2089_, 4, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2100_ = lean_unsigned_to_nat(2u);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_r_2071_);
lean_ctor_set(v___x_1939_, 0, v___x_2100_);
v___x_2102_ = v___x_1939_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_l_1936_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_r_2071_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v___x_2105_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_l_1936_);
lean_ctor_set(v___x_1939_, 0, v___x_1944_);
v___x_2105_ = v___x_1939_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_l_1936_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v_l_1936_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_del_object(v___x_1939_);
lean_dec(v_v_1935_);
lean_dec(v_k_1934_);
if (lean_obj_tag(v_l_1936_) == 0)
{
if (lean_obj_tag(v_r_1937_) == 0)
{
lean_object* v_size_2107_; lean_object* v_k_2108_; lean_object* v_v_2109_; lean_object* v_l_2110_; lean_object* v_r_2111_; lean_object* v_size_2112_; lean_object* v_k_2113_; lean_object* v_v_2114_; lean_object* v_l_2115_; lean_object* v_r_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v_size_2107_ = lean_ctor_get(v_l_1936_, 0);
v_k_2108_ = lean_ctor_get(v_l_1936_, 1);
v_v_2109_ = lean_ctor_get(v_l_1936_, 2);
v_l_2110_ = lean_ctor_get(v_l_1936_, 3);
v_r_2111_ = lean_ctor_get(v_l_1936_, 4);
lean_inc(v_r_2111_);
v_size_2112_ = lean_ctor_get(v_r_1937_, 0);
v_k_2113_ = lean_ctor_get(v_r_1937_, 1);
v_v_2114_ = lean_ctor_get(v_r_1937_, 2);
v_l_2115_ = lean_ctor_get(v_r_1937_, 3);
lean_inc(v_l_2115_);
v_r_2116_ = lean_ctor_get(v_r_1937_, 4);
v___x_2117_ = lean_unsigned_to_nat(1u);
v___x_2118_ = lean_nat_dec_lt(v_size_2107_, v_size_2112_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2254_; 
lean_inc(v_l_2110_);
lean_inc(v_v_2109_);
lean_inc(v_k_2108_);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_l_1936_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; lean_object* v_unused_2256_; lean_object* v_unused_2257_; lean_object* v_unused_2258_; lean_object* v_unused_2259_; 
v_unused_2255_ = lean_ctor_get(v_l_1936_, 4);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_l_1936_, 3);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_l_1936_, 2);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_l_1936_, 1);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_l_1936_, 0);
lean_dec(v_unused_2259_);
v___x_2120_ = v_l_1936_;
v_isShared_2121_ = v_isSharedCheck_2254_;
goto v_resetjp_2119_;
}
else
{
lean_dec(v_l_1936_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2254_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v_tree_2123_; 
v___x_2122_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2108_, v_v_2109_, v_l_2110_, v_r_2111_);
v_tree_2123_ = lean_ctor_get(v___x_2122_, 2);
lean_inc(v_tree_2123_);
if (lean_obj_tag(v_tree_2123_) == 0)
{
lean_object* v_k_2124_; lean_object* v_v_2125_; lean_object* v_size_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v_k_2124_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_k_2124_);
v_v_2125_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_v_2125_);
lean_dec_ref(v___x_2122_);
v_size_2126_ = lean_ctor_get(v_tree_2123_, 0);
v___x_2127_ = lean_unsigned_to_nat(3u);
v___x_2128_ = lean_nat_mul(v___x_2127_, v_size_2126_);
v___x_2129_ = lean_nat_dec_lt(v___x_2128_, v_size_2112_);
lean_dec(v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_dec(v_l_2115_);
v___x_2130_ = lean_nat_add(v___x_2117_, v_size_2126_);
v___x_2131_ = lean_nat_add(v___x_2130_, v_size_2112_);
lean_dec(v___x_2130_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v_r_1937_);
lean_ctor_set(v___x_2120_, 3, v_tree_2123_);
lean_ctor_set(v___x_2120_, 2, v_v_2125_);
lean_ctor_set(v___x_2120_, 1, v_k_2124_);
lean_ctor_set(v___x_2120_, 0, v___x_2131_);
v___x_2133_ = v___x_2120_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_k_2124_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_v_2125_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_tree_2123_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_r_1937_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
else
{
lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2189_; 
lean_inc(v_r_2116_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
lean_inc(v_size_2112_);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; lean_object* v_unused_2191_; lean_object* v_unused_2192_; lean_object* v_unused_2193_; lean_object* v_unused_2194_; 
v_unused_2190_ = lean_ctor_get(v_r_1937_, 4);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_r_1937_, 3);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_r_1937_, 2);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_r_1937_, 1);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_r_1937_, 0);
lean_dec(v_unused_2194_);
v___x_2136_ = v_r_1937_;
v_isShared_2137_ = v_isSharedCheck_2189_;
goto v_resetjp_2135_;
}
else
{
lean_dec(v_r_1937_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2189_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_size_2138_; lean_object* v_k_2139_; lean_object* v_v_2140_; lean_object* v_l_2141_; lean_object* v_r_2142_; lean_object* v_size_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_size_2138_ = lean_ctor_get(v_l_2115_, 0);
v_k_2139_ = lean_ctor_get(v_l_2115_, 1);
v_v_2140_ = lean_ctor_get(v_l_2115_, 2);
v_l_2141_ = lean_ctor_get(v_l_2115_, 3);
v_r_2142_ = lean_ctor_get(v_l_2115_, 4);
v_size_2143_ = lean_ctor_get(v_r_2116_, 0);
v___x_2144_ = lean_unsigned_to_nat(2u);
v___x_2145_ = lean_nat_mul(v___x_2144_, v_size_2143_);
v___x_2146_ = lean_nat_dec_lt(v_size_2138_, v___x_2145_);
lean_dec(v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2174_; 
lean_inc(v_r_2142_);
lean_inc(v_l_2141_);
lean_inc(v_v_2140_);
lean_inc(v_k_2139_);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_l_2115_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; lean_object* v_unused_2178_; lean_object* v_unused_2179_; 
v_unused_2175_ = lean_ctor_get(v_l_2115_, 4);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_l_2115_, 3);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_l_2115_, 2);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_l_2115_, 1);
lean_dec(v_unused_2178_);
v_unused_2179_ = lean_ctor_get(v_l_2115_, 0);
lean_dec(v_unused_2179_);
v___x_2148_ = v_l_2115_;
v_isShared_2149_ = v_isSharedCheck_2174_;
goto v_resetjp_2147_;
}
else
{
lean_dec(v_l_2115_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2174_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2164_; 
v___x_2150_ = lean_nat_add(v___x_2117_, v_size_2126_);
v___x_2151_ = lean_nat_add(v___x_2150_, v_size_2112_);
lean_dec(v_size_2112_);
if (lean_obj_tag(v_l_2141_) == 0)
{
lean_object* v_size_2172_; 
v_size_2172_ = lean_ctor_get(v_l_2141_, 0);
lean_inc(v_size_2172_);
v___y_2164_ = v_size_2172_;
goto v___jp_2163_;
}
else
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_unsigned_to_nat(0u);
v___y_2164_ = v___x_2173_;
goto v___jp_2163_;
}
v___jp_2152_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_nat_add(v___y_2153_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec(v___y_2153_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 4, v_r_2116_);
lean_ctor_set(v___x_2148_, 3, v_r_2142_);
lean_ctor_set(v___x_2148_, 2, v_v_2114_);
lean_ctor_set(v___x_2148_, 1, v_k_2113_);
lean_ctor_set(v___x_2148_, 0, v___x_2156_);
v___x_2158_ = v___x_2148_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_r_2142_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_r_2116_);
v___x_2158_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 4, v___x_2158_);
lean_ctor_set(v___x_2136_, 3, v___y_2154_);
lean_ctor_set(v___x_2136_, 2, v_v_2140_);
lean_ctor_set(v___x_2136_, 1, v_k_2139_);
lean_ctor_set(v___x_2136_, 0, v___x_2151_);
v___x_2160_ = v___x_2136_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v___y_2154_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
v___jp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_nat_add(v___x_2150_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec(v___x_2150_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v_l_2141_);
lean_ctor_set(v___x_2120_, 3, v_tree_2123_);
lean_ctor_set(v___x_2120_, 2, v_v_2125_);
lean_ctor_set(v___x_2120_, 1, v_k_2124_);
lean_ctor_set(v___x_2120_, 0, v___x_2165_);
v___x_2167_ = v___x_2120_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_2124_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_2125_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_tree_2123_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v_l_2141_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_nat_add(v___x_2117_, v_size_2143_);
if (lean_obj_tag(v_r_2142_) == 0)
{
lean_object* v_size_2169_; 
v_size_2169_ = lean_ctor_get(v_r_2142_, 0);
lean_inc(v_size_2169_);
v___y_2153_ = v___x_2168_;
v___y_2154_ = v___x_2167_;
v___y_2155_ = v_size_2169_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2170_; 
v___x_2170_ = lean_unsigned_to_nat(0u);
v___y_2153_ = v___x_2168_;
v___y_2154_ = v___x_2167_;
v___y_2155_ = v___x_2170_;
goto v___jp_2152_;
}
}
}
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2180_ = lean_nat_add(v___x_2117_, v_size_2126_);
v___x_2181_ = lean_nat_add(v___x_2180_, v_size_2112_);
lean_dec(v_size_2112_);
v___x_2182_ = lean_nat_add(v___x_2180_, v_size_2138_);
lean_dec(v___x_2180_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 4, v_l_2115_);
lean_ctor_set(v___x_2136_, 3, v_tree_2123_);
lean_ctor_set(v___x_2136_, 2, v_v_2125_);
lean_ctor_set(v___x_2136_, 1, v_k_2124_);
lean_ctor_set(v___x_2136_, 0, v___x_2182_);
v___x_2184_ = v___x_2136_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_k_2124_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_v_2125_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_tree_2123_);
lean_ctor_set(v_reuseFailAlloc_2188_, 4, v_l_2115_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v_r_2116_);
lean_ctor_set(v___x_2120_, 3, v___x_2184_);
lean_ctor_set(v___x_2120_, 2, v_v_2114_);
lean_ctor_set(v___x_2120_, 1, v_k_2113_);
lean_ctor_set(v___x_2120_, 0, v___x_2181_);
v___x_2186_ = v___x_2120_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v_r_2116_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
else
{
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2248_; 
lean_inc(v_r_2116_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
lean_inc(v_size_2112_);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; lean_object* v_unused_2250_; lean_object* v_unused_2251_; lean_object* v_unused_2252_; lean_object* v_unused_2253_; 
v_unused_2249_ = lean_ctor_get(v_r_1937_, 4);
lean_dec(v_unused_2249_);
v_unused_2250_ = lean_ctor_get(v_r_1937_, 3);
lean_dec(v_unused_2250_);
v_unused_2251_ = lean_ctor_get(v_r_1937_, 2);
lean_dec(v_unused_2251_);
v_unused_2252_ = lean_ctor_get(v_r_1937_, 1);
lean_dec(v_unused_2252_);
v_unused_2253_ = lean_ctor_get(v_r_1937_, 0);
lean_dec(v_unused_2253_);
v___x_2196_ = v_r_1937_;
v_isShared_2197_ = v_isSharedCheck_2248_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v_r_1937_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2248_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
if (lean_obj_tag(v_l_2115_) == 0)
{
if (lean_obj_tag(v_r_2116_) == 0)
{
lean_object* v_k_2198_; lean_object* v_v_2199_; lean_object* v_size_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v_k_2198_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_k_2198_);
v_v_2199_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_v_2199_);
lean_dec_ref(v___x_2122_);
v_size_2200_ = lean_ctor_get(v_l_2115_, 0);
v___x_2201_ = lean_nat_add(v___x_2117_, v_size_2112_);
lean_dec(v_size_2112_);
v___x_2202_ = lean_nat_add(v___x_2117_, v_size_2200_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 4, v_l_2115_);
lean_ctor_set(v___x_2196_, 3, v_tree_2123_);
lean_ctor_set(v___x_2196_, 2, v_v_2199_);
lean_ctor_set(v___x_2196_, 1, v_k_2198_);
lean_ctor_set(v___x_2196_, 0, v___x_2202_);
v___x_2204_ = v___x_2196_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2198_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2199_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_tree_2123_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_l_2115_);
v___x_2204_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v_r_2116_);
lean_ctor_set(v___x_2120_, 3, v___x_2204_);
lean_ctor_set(v___x_2120_, 2, v_v_2114_);
lean_ctor_set(v___x_2120_, 1, v_k_2113_);
lean_ctor_set(v___x_2120_, 0, v___x_2201_);
v___x_2206_ = v___x_2120_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2207_, 4, v_r_2116_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_object* v_k_2209_; lean_object* v_v_2210_; lean_object* v_k_2211_; lean_object* v_v_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_size_2112_);
v_k_2209_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_k_2209_);
v_v_2210_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_v_2210_);
lean_dec_ref(v___x_2122_);
v_k_2211_ = lean_ctor_get(v_l_2115_, 1);
v_v_2212_ = lean_ctor_get(v_l_2115_, 2);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_l_2115_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2227_ = lean_ctor_get(v_l_2115_, 4);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v_l_2115_, 3);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_l_2115_, 0);
lean_dec(v_unused_2229_);
v___x_2214_ = v_l_2115_;
v_isShared_2215_ = v_isSharedCheck_2226_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_v_2212_);
lean_inc(v_k_2211_);
lean_dec(v_l_2115_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2226_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = lean_unsigned_to_nat(3u);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 4, v_r_2116_);
lean_ctor_set(v___x_2214_, 3, v_r_2116_);
lean_ctor_set(v___x_2214_, 2, v_v_2210_);
lean_ctor_set(v___x_2214_, 1, v_k_2209_);
lean_ctor_set(v___x_2214_, 0, v___x_2117_);
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_k_2209_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_v_2210_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_r_2116_);
v___x_2218_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 3, v_r_2116_);
lean_ctor_set(v___x_2196_, 0, v___x_2117_);
v___x_2220_ = v___x_2196_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_r_2116_);
v___x_2220_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2222_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v___x_2220_);
lean_ctor_set(v___x_2120_, 3, v___x_2218_);
lean_ctor_set(v___x_2120_, 2, v_v_2212_);
lean_ctor_set(v___x_2120_, 1, v_k_2211_);
lean_ctor_set(v___x_2120_, 0, v___x_2216_);
v___x_2222_ = v___x_2120_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2211_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2212_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2116_) == 0)
{
lean_object* v_k_2230_; lean_object* v_v_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_dec(v_size_2112_);
v_k_2230_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_k_2230_);
v_v_2231_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_v_2231_);
lean_dec_ref(v___x_2122_);
v___x_2232_ = lean_unsigned_to_nat(3u);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 4, v_l_2115_);
lean_ctor_set(v___x_2196_, 2, v_v_2231_);
lean_ctor_set(v___x_2196_, 1, v_k_2230_);
lean_ctor_set(v___x_2196_, 0, v___x_2117_);
v___x_2234_ = v___x_2196_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_k_2230_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_v_2231_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_l_2115_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_l_2115_);
v___x_2234_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2236_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v_r_2116_);
lean_ctor_set(v___x_2120_, 3, v___x_2234_);
lean_ctor_set(v___x_2120_, 2, v_v_2114_);
lean_ctor_set(v___x_2120_, 1, v_k_2113_);
lean_ctor_set(v___x_2120_, 0, v___x_2232_);
v___x_2236_ = v___x_2120_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_r_2116_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
lean_object* v_k_2239_; lean_object* v_v_2240_; lean_object* v___x_2242_; 
v_k_2239_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_k_2239_);
v_v_2240_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_v_2240_);
lean_dec_ref(v___x_2122_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 3, v_r_2116_);
v___x_2242_ = v___x_2196_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_size_2112_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2247_, 4, v_r_2116_);
v___x_2242_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = lean_unsigned_to_nat(2u);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 4, v___x_2242_);
lean_ctor_set(v___x_2120_, 3, v_r_2116_);
lean_ctor_set(v___x_2120_, 2, v_v_2240_);
lean_ctor_set(v___x_2120_, 1, v_k_2239_);
lean_ctor_set(v___x_2120_, 0, v___x_2243_);
v___x_2245_ = v___x_2120_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v___x_2242_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
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
lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2412_; 
lean_inc(v_r_2116_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; lean_object* v_unused_2414_; lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; 
v_unused_2413_ = lean_ctor_get(v_r_1937_, 4);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_r_1937_, 3);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_r_1937_, 2);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_r_1937_, 1);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_r_1937_, 0);
lean_dec(v_unused_2417_);
v___x_2261_ = v_r_1937_;
v_isShared_2262_ = v_isSharedCheck_2412_;
goto v_resetjp_2260_;
}
else
{
lean_dec(v_r_1937_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2412_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v_tree_2264_; 
v___x_2263_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2113_, v_v_2114_, v_l_2115_, v_r_2116_);
v_tree_2264_ = lean_ctor_get(v___x_2263_, 2);
lean_inc(v_tree_2264_);
if (lean_obj_tag(v_tree_2264_) == 0)
{
lean_object* v_k_2265_; lean_object* v_v_2266_; lean_object* v_size_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v_k_2265_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_k_2265_);
v_v_2266_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_v_2266_);
lean_dec_ref(v___x_2263_);
v_size_2267_ = lean_ctor_get(v_tree_2264_, 0);
v___x_2268_ = lean_unsigned_to_nat(3u);
v___x_2269_ = lean_nat_mul(v___x_2268_, v_size_2267_);
v___x_2270_ = lean_nat_dec_lt(v___x_2269_, v_size_2107_);
lean_dec(v___x_2269_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec(v_r_2111_);
v___x_2271_ = lean_nat_add(v___x_2117_, v_size_2107_);
v___x_2272_ = lean_nat_add(v___x_2271_, v_size_2267_);
lean_dec(v___x_2271_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_tree_2264_);
lean_ctor_set(v___x_2261_, 3, v_l_1936_);
lean_ctor_set(v___x_2261_, 2, v_v_2266_);
lean_ctor_set(v___x_2261_, 1, v_k_2265_);
lean_ctor_set(v___x_2261_, 0, v___x_2272_);
v___x_2274_ = v___x_2261_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_k_2265_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_v_2266_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_l_1936_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v_tree_2264_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
else
{
lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2341_; 
lean_inc(v_l_2110_);
lean_inc(v_v_2109_);
lean_inc(v_k_2108_);
lean_inc(v_size_2107_);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_l_1936_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; lean_object* v_unused_2343_; lean_object* v_unused_2344_; lean_object* v_unused_2345_; lean_object* v_unused_2346_; 
v_unused_2342_ = lean_ctor_get(v_l_1936_, 4);
lean_dec(v_unused_2342_);
v_unused_2343_ = lean_ctor_get(v_l_1936_, 3);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_l_1936_, 2);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_l_1936_, 1);
lean_dec(v_unused_2345_);
v_unused_2346_ = lean_ctor_get(v_l_1936_, 0);
lean_dec(v_unused_2346_);
v___x_2277_ = v_l_1936_;
v_isShared_2278_ = v_isSharedCheck_2341_;
goto v_resetjp_2276_;
}
else
{
lean_dec(v_l_1936_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2341_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v_size_2279_; lean_object* v_size_2280_; lean_object* v_k_2281_; lean_object* v_v_2282_; lean_object* v_l_2283_; lean_object* v_r_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v_size_2279_ = lean_ctor_get(v_l_2110_, 0);
v_size_2280_ = lean_ctor_get(v_r_2111_, 0);
v_k_2281_ = lean_ctor_get(v_r_2111_, 1);
v_v_2282_ = lean_ctor_get(v_r_2111_, 2);
v_l_2283_ = lean_ctor_get(v_r_2111_, 3);
v_r_2284_ = lean_ctor_get(v_r_2111_, 4);
v___x_2285_ = lean_unsigned_to_nat(2u);
v___x_2286_ = lean_nat_mul(v___x_2285_, v_size_2279_);
v___x_2287_ = lean_nat_dec_lt(v_size_2280_, v___x_2286_);
lean_dec(v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2325_; 
lean_inc(v_r_2284_);
lean_inc(v_l_2283_);
lean_inc(v_v_2282_);
lean_inc(v_k_2281_);
lean_del_object(v___x_2277_);
v_isSharedCheck_2325_ = !lean_is_exclusive(v_r_2111_);
if (v_isSharedCheck_2325_ == 0)
{
lean_object* v_unused_2326_; lean_object* v_unused_2327_; lean_object* v_unused_2328_; lean_object* v_unused_2329_; lean_object* v_unused_2330_; 
v_unused_2326_ = lean_ctor_get(v_r_2111_, 4);
lean_dec(v_unused_2326_);
v_unused_2327_ = lean_ctor_get(v_r_2111_, 3);
lean_dec(v_unused_2327_);
v_unused_2328_ = lean_ctor_get(v_r_2111_, 2);
lean_dec(v_unused_2328_);
v_unused_2329_ = lean_ctor_get(v_r_2111_, 1);
lean_dec(v_unused_2329_);
v_unused_2330_ = lean_ctor_get(v_r_2111_, 0);
lean_dec(v_unused_2330_);
v___x_2289_ = v_r_2111_;
v_isShared_2290_ = v_isSharedCheck_2325_;
goto v_resetjp_2288_;
}
else
{
lean_dec(v_r_2111_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2325_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___x_2313_; lean_object* v___y_2315_; 
v___x_2291_ = lean_nat_add(v___x_2117_, v_size_2107_);
lean_dec(v_size_2107_);
v___x_2292_ = lean_nat_add(v___x_2291_, v_size_2267_);
lean_dec(v___x_2291_);
v___x_2313_ = lean_nat_add(v___x_2117_, v_size_2279_);
if (lean_obj_tag(v_l_2283_) == 0)
{
lean_object* v_size_2323_; 
v_size_2323_ = lean_ctor_get(v_l_2283_, 0);
lean_inc(v_size_2323_);
v___y_2315_ = v_size_2323_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_unsigned_to_nat(0u);
v___y_2315_ = v___x_2324_;
goto v___jp_2314_;
}
v___jp_2293_:
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = lean_nat_add(v___y_2294_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec(v___y_2294_);
lean_inc_ref(v_tree_2264_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 4, v_tree_2264_);
lean_ctor_set(v___x_2289_, 3, v_r_2284_);
lean_ctor_set(v___x_2289_, 2, v_v_2266_);
lean_ctor_set(v___x_2289_, 1, v_k_2265_);
lean_ctor_set(v___x_2289_, 0, v___x_2297_);
v___x_2299_ = v___x_2289_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_k_2265_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_v_2266_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_r_2284_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v_tree_2264_);
v___x_2299_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_isSharedCheck_2306_ = !lean_is_exclusive(v_tree_2264_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; lean_object* v_unused_2308_; lean_object* v_unused_2309_; lean_object* v_unused_2310_; lean_object* v_unused_2311_; 
v_unused_2307_ = lean_ctor_get(v_tree_2264_, 4);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_tree_2264_, 3);
lean_dec(v_unused_2308_);
v_unused_2309_ = lean_ctor_get(v_tree_2264_, 2);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_tree_2264_, 1);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_tree_2264_, 0);
lean_dec(v_unused_2311_);
v___x_2301_ = v_tree_2264_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_dec(v_tree_2264_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 4, v___x_2299_);
lean_ctor_set(v___x_2301_, 3, v___y_2295_);
lean_ctor_set(v___x_2301_, 2, v_v_2282_);
lean_ctor_set(v___x_2301_, 1, v_k_2281_);
lean_ctor_set(v___x_2301_, 0, v___x_2292_);
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_k_2281_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_v_2282_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v___y_2295_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v___x_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
v___jp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = lean_nat_add(v___x_2313_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec(v___x_2313_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_l_2283_);
lean_ctor_set(v___x_2261_, 3, v_l_2110_);
lean_ctor_set(v___x_2261_, 2, v_v_2109_);
lean_ctor_set(v___x_2261_, 1, v_k_2108_);
lean_ctor_set(v___x_2261_, 0, v___x_2316_);
v___x_2318_ = v___x_2261_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_k_2108_);
lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_v_2109_);
lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_l_2110_);
lean_ctor_set(v_reuseFailAlloc_2322_, 4, v_l_2283_);
v___x_2318_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_nat_add(v___x_2117_, v_size_2267_);
if (lean_obj_tag(v_r_2284_) == 0)
{
lean_object* v_size_2320_; 
v_size_2320_ = lean_ctor_get(v_r_2284_, 0);
lean_inc(v_size_2320_);
v___y_2294_ = v___x_2319_;
v___y_2295_ = v___x_2318_;
v___y_2296_ = v_size_2320_;
goto v___jp_2293_;
}
else
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_unsigned_to_nat(0u);
v___y_2294_ = v___x_2319_;
v___y_2295_ = v___x_2318_;
v___y_2296_ = v___x_2321_;
goto v___jp_2293_;
}
}
}
}
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2331_ = lean_nat_add(v___x_2117_, v_size_2107_);
lean_dec(v_size_2107_);
v___x_2332_ = lean_nat_add(v___x_2331_, v_size_2267_);
lean_dec(v___x_2331_);
v___x_2333_ = lean_nat_add(v___x_2117_, v_size_2267_);
v___x_2334_ = lean_nat_add(v___x_2333_, v_size_2280_);
lean_dec(v___x_2333_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_tree_2264_);
lean_ctor_set(v___x_2261_, 3, v_r_2111_);
lean_ctor_set(v___x_2261_, 2, v_v_2266_);
lean_ctor_set(v___x_2261_, 1, v_k_2265_);
lean_ctor_set(v___x_2261_, 0, v___x_2334_);
v___x_2336_ = v___x_2261_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_k_2265_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_v_2266_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_r_2111_);
lean_ctor_set(v_reuseFailAlloc_2340_, 4, v_tree_2264_);
v___x_2336_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 4, v___x_2336_);
lean_ctor_set(v___x_2277_, 0, v___x_2332_);
v___x_2338_ = v___x_2277_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_k_2108_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_v_2109_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_l_2110_);
lean_ctor_set(v_reuseFailAlloc_2339_, 4, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2110_) == 0)
{
lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2370_; 
lean_inc_ref(v_l_2110_);
lean_inc(v_v_2109_);
lean_inc(v_k_2108_);
lean_inc(v_size_2107_);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_l_1936_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; lean_object* v_unused_2372_; lean_object* v_unused_2373_; lean_object* v_unused_2374_; lean_object* v_unused_2375_; 
v_unused_2371_ = lean_ctor_get(v_l_1936_, 4);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_l_1936_, 3);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_l_1936_, 2);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_l_1936_, 1);
lean_dec(v_unused_2374_);
v_unused_2375_ = lean_ctor_get(v_l_1936_, 0);
lean_dec(v_unused_2375_);
v___x_2348_ = v_l_1936_;
v_isShared_2349_ = v_isSharedCheck_2370_;
goto v_resetjp_2347_;
}
else
{
lean_dec(v_l_1936_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2370_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
if (lean_obj_tag(v_r_2111_) == 0)
{
lean_object* v_k_2350_; lean_object* v_v_2351_; lean_object* v_size_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v_k_2350_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_k_2350_);
v_v_2351_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_v_2351_);
lean_dec_ref(v___x_2263_);
v_size_2352_ = lean_ctor_get(v_r_2111_, 0);
v___x_2353_ = lean_nat_add(v___x_2117_, v_size_2107_);
lean_dec(v_size_2107_);
v___x_2354_ = lean_nat_add(v___x_2117_, v_size_2352_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_tree_2264_);
lean_ctor_set(v___x_2261_, 3, v_r_2111_);
lean_ctor_set(v___x_2261_, 2, v_v_2351_);
lean_ctor_set(v___x_2261_, 1, v_k_2350_);
lean_ctor_set(v___x_2261_, 0, v___x_2354_);
v___x_2356_ = v___x_2261_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_k_2350_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_v_2351_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_r_2111_);
lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_tree_2264_);
v___x_2356_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2358_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 4, v___x_2356_);
lean_ctor_set(v___x_2348_, 0, v___x_2353_);
v___x_2358_ = v___x_2348_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_2108_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_2109_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_l_2110_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
lean_object* v_k_2361_; lean_object* v_v_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
lean_dec(v_size_2107_);
v_k_2361_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_k_2361_);
v_v_2362_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_v_2362_);
lean_dec_ref(v___x_2263_);
v___x_2363_ = lean_unsigned_to_nat(3u);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_r_2111_);
lean_ctor_set(v___x_2261_, 3, v_r_2111_);
lean_ctor_set(v___x_2261_, 2, v_v_2362_);
lean_ctor_set(v___x_2261_, 1, v_k_2361_);
lean_ctor_set(v___x_2261_, 0, v___x_2117_);
v___x_2365_ = v___x_2261_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_k_2361_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_v_2362_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v_r_2111_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v_r_2111_);
v___x_2365_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 4, v___x_2365_);
lean_ctor_set(v___x_2348_, 0, v___x_2363_);
v___x_2367_ = v___x_2348_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_k_2108_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_v_2109_);
lean_ctor_set(v_reuseFailAlloc_2368_, 3, v_l_2110_);
lean_ctor_set(v_reuseFailAlloc_2368_, 4, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2111_) == 0)
{
lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2400_; 
lean_inc(v_l_2110_);
lean_inc(v_v_2109_);
lean_inc(v_k_2108_);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_l_1936_);
if (v_isSharedCheck_2400_ == 0)
{
lean_object* v_unused_2401_; lean_object* v_unused_2402_; lean_object* v_unused_2403_; lean_object* v_unused_2404_; lean_object* v_unused_2405_; 
v_unused_2401_ = lean_ctor_get(v_l_1936_, 4);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_l_1936_, 3);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_l_1936_, 2);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_l_1936_, 1);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_l_1936_, 0);
lean_dec(v_unused_2405_);
v___x_2377_ = v_l_1936_;
v_isShared_2378_ = v_isSharedCheck_2400_;
goto v_resetjp_2376_;
}
else
{
lean_dec(v_l_1936_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2400_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v_k_2379_; lean_object* v_v_2380_; lean_object* v_k_2381_; lean_object* v_v_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2396_; 
v_k_2379_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_k_2379_);
v_v_2380_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_v_2380_);
lean_dec_ref(v___x_2263_);
v_k_2381_ = lean_ctor_get(v_r_2111_, 1);
v_v_2382_ = lean_ctor_get(v_r_2111_, 2);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_r_2111_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; lean_object* v_unused_2398_; lean_object* v_unused_2399_; 
v_unused_2397_ = lean_ctor_get(v_r_2111_, 4);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_r_2111_, 3);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_r_2111_, 0);
lean_dec(v_unused_2399_);
v___x_2384_ = v_r_2111_;
v_isShared_2385_ = v_isSharedCheck_2396_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_v_2382_);
lean_inc(v_k_2381_);
lean_dec(v_r_2111_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2396_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2386_ = lean_unsigned_to_nat(3u);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 4, v_l_2110_);
lean_ctor_set(v___x_2384_, 3, v_l_2110_);
lean_ctor_set(v___x_2384_, 2, v_v_2109_);
lean_ctor_set(v___x_2384_, 1, v_k_2108_);
lean_ctor_set(v___x_2384_, 0, v___x_2117_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_k_2108_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_v_2109_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_l_2110_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_l_2110_);
v___x_2388_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_l_2110_);
lean_ctor_set(v___x_2261_, 3, v_l_2110_);
lean_ctor_set(v___x_2261_, 2, v_v_2380_);
lean_ctor_set(v___x_2261_, 1, v_k_2379_);
lean_ctor_set(v___x_2261_, 0, v___x_2117_);
v___x_2390_ = v___x_2261_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_k_2379_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_v_2380_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_l_2110_);
lean_ctor_set(v_reuseFailAlloc_2394_, 4, v_l_2110_);
v___x_2390_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2392_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 4, v___x_2390_);
lean_ctor_set(v___x_2377_, 3, v___x_2388_);
lean_ctor_set(v___x_2377_, 2, v_v_2382_);
lean_ctor_set(v___x_2377_, 1, v_k_2381_);
lean_ctor_set(v___x_2377_, 0, v___x_2386_);
v___x_2392_ = v___x_2377_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_k_2381_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_v_2382_);
lean_ctor_set(v_reuseFailAlloc_2393_, 3, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2393_, 4, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
}
else
{
lean_object* v_k_2406_; lean_object* v_v_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v_k_2406_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_k_2406_);
v_v_2407_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_v_2407_);
lean_dec_ref(v___x_2263_);
v___x_2408_ = lean_unsigned_to_nat(2u);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_r_2111_);
lean_ctor_set(v___x_2261_, 3, v_l_1936_);
lean_ctor_set(v___x_2261_, 2, v_v_2407_);
lean_ctor_set(v___x_2261_, 1, v_k_2406_);
lean_ctor_set(v___x_2261_, 0, v___x_2408_);
v___x_2410_ = v___x_2261_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_k_2406_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_v_2407_);
lean_ctor_set(v_reuseFailAlloc_2411_, 3, v_l_1936_);
lean_ctor_set(v_reuseFailAlloc_2411_, 4, v_r_2111_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
}
else
{
return v_l_1936_;
}
}
else
{
return v_r_1937_;
}
}
}
else
{
lean_object* v_impl_2418_; lean_object* v___x_2419_; 
v_impl_2418_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1932_, v_l_1936_);
v___x_2419_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2418_) == 0)
{
if (lean_obj_tag(v_r_1937_) == 0)
{
lean_object* v_size_2420_; lean_object* v_size_2421_; lean_object* v_k_2422_; lean_object* v_v_2423_; lean_object* v_l_2424_; lean_object* v_r_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v_size_2420_ = lean_ctor_get(v_impl_2418_, 0);
lean_inc(v_size_2420_);
v_size_2421_ = lean_ctor_get(v_r_1937_, 0);
v_k_2422_ = lean_ctor_get(v_r_1937_, 1);
v_v_2423_ = lean_ctor_get(v_r_1937_, 2);
v_l_2424_ = lean_ctor_get(v_r_1937_, 3);
lean_inc(v_l_2424_);
v_r_2425_ = lean_ctor_get(v_r_1937_, 4);
v___x_2426_ = lean_unsigned_to_nat(3u);
v___x_2427_ = lean_nat_mul(v___x_2426_, v_size_2420_);
v___x_2428_ = lean_nat_dec_lt(v___x_2427_, v_size_2421_);
lean_dec(v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
lean_dec(v_l_2424_);
v___x_2429_ = lean_nat_add(v___x_2419_, v_size_2420_);
lean_dec(v_size_2420_);
v___x_2430_ = lean_nat_add(v___x_2429_, v_size_2421_);
lean_dec(v___x_2429_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 3, v_impl_2418_);
lean_ctor_set(v___x_1939_, 0, v___x_2430_);
v___x_2432_ = v___x_1939_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2433_, 3, v_impl_2418_);
lean_ctor_set(v_reuseFailAlloc_2433_, 4, v_r_1937_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
else
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2497_; 
lean_inc(v_r_2425_);
lean_inc(v_v_2423_);
lean_inc(v_k_2422_);
lean_inc(v_size_2421_);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; lean_object* v_unused_2499_; lean_object* v_unused_2500_; lean_object* v_unused_2501_; lean_object* v_unused_2502_; 
v_unused_2498_ = lean_ctor_get(v_r_1937_, 4);
lean_dec(v_unused_2498_);
v_unused_2499_ = lean_ctor_get(v_r_1937_, 3);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_r_1937_, 2);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_r_1937_, 1);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_r_1937_, 0);
lean_dec(v_unused_2502_);
v___x_2435_ = v_r_1937_;
v_isShared_2436_ = v_isSharedCheck_2497_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v_r_1937_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2497_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v_size_2437_; lean_object* v_k_2438_; lean_object* v_v_2439_; lean_object* v_l_2440_; lean_object* v_r_2441_; lean_object* v_size_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v_size_2437_ = lean_ctor_get(v_l_2424_, 0);
v_k_2438_ = lean_ctor_get(v_l_2424_, 1);
v_v_2439_ = lean_ctor_get(v_l_2424_, 2);
v_l_2440_ = lean_ctor_get(v_l_2424_, 3);
v_r_2441_ = lean_ctor_get(v_l_2424_, 4);
v_size_2442_ = lean_ctor_get(v_r_2425_, 0);
v___x_2443_ = lean_unsigned_to_nat(2u);
v___x_2444_ = lean_nat_mul(v___x_2443_, v_size_2442_);
v___x_2445_ = lean_nat_dec_lt(v_size_2437_, v___x_2444_);
lean_dec(v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2473_; 
lean_inc(v_r_2441_);
lean_inc(v_l_2440_);
lean_inc(v_v_2439_);
lean_inc(v_k_2438_);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_l_2424_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; lean_object* v_unused_2475_; lean_object* v_unused_2476_; lean_object* v_unused_2477_; lean_object* v_unused_2478_; 
v_unused_2474_ = lean_ctor_get(v_l_2424_, 4);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_l_2424_, 3);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_l_2424_, 2);
lean_dec(v_unused_2476_);
v_unused_2477_ = lean_ctor_get(v_l_2424_, 1);
lean_dec(v_unused_2477_);
v_unused_2478_ = lean_ctor_get(v_l_2424_, 0);
lean_dec(v_unused_2478_);
v___x_2447_ = v_l_2424_;
v_isShared_2448_ = v_isSharedCheck_2473_;
goto v_resetjp_2446_;
}
else
{
lean_dec(v_l_2424_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2473_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2463_; 
v___x_2449_ = lean_nat_add(v___x_2419_, v_size_2420_);
lean_dec(v_size_2420_);
v___x_2450_ = lean_nat_add(v___x_2449_, v_size_2421_);
lean_dec(v_size_2421_);
if (lean_obj_tag(v_l_2440_) == 0)
{
lean_object* v_size_2471_; 
v_size_2471_ = lean_ctor_get(v_l_2440_, 0);
lean_inc(v_size_2471_);
v___y_2463_ = v_size_2471_;
goto v___jp_2462_;
}
else
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_unsigned_to_nat(0u);
v___y_2463_ = v___x_2472_;
goto v___jp_2462_;
}
v___jp_2451_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = lean_nat_add(v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec(v___y_2453_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 4, v_r_2425_);
lean_ctor_set(v___x_2447_, 3, v_r_2441_);
lean_ctor_set(v___x_2447_, 2, v_v_2423_);
lean_ctor_set(v___x_2447_, 1, v_k_2422_);
lean_ctor_set(v___x_2447_, 0, v___x_2455_);
v___x_2457_ = v___x_2447_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_r_2441_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_r_2425_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v___x_2457_);
lean_ctor_set(v___x_2435_, 3, v___y_2452_);
lean_ctor_set(v___x_2435_, 2, v_v_2439_);
lean_ctor_set(v___x_2435_, 1, v_k_2438_);
lean_ctor_set(v___x_2435_, 0, v___x_2450_);
v___x_2459_ = v___x_2435_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_k_2438_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_v_2439_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v___y_2452_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
v___jp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = lean_nat_add(v___x_2449_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec(v___x_2449_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_l_2440_);
lean_ctor_set(v___x_1939_, 3, v_impl_2418_);
lean_ctor_set(v___x_1939_, 0, v___x_2464_);
v___x_2466_ = v___x_1939_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_impl_2418_);
lean_ctor_set(v_reuseFailAlloc_2470_, 4, v_l_2440_);
v___x_2466_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; 
v___x_2467_ = lean_nat_add(v___x_2419_, v_size_2442_);
if (lean_obj_tag(v_r_2441_) == 0)
{
lean_object* v_size_2468_; 
v_size_2468_ = lean_ctor_get(v_r_2441_, 0);
lean_inc(v_size_2468_);
v___y_2452_ = v___x_2466_;
v___y_2453_ = v___x_2467_;
v___y_2454_ = v_size_2468_;
goto v___jp_2451_;
}
else
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_unsigned_to_nat(0u);
v___y_2452_ = v___x_2466_;
v___y_2453_ = v___x_2467_;
v___y_2454_ = v___x_2469_;
goto v___jp_2451_;
}
}
}
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
lean_del_object(v___x_1939_);
v___x_2479_ = lean_nat_add(v___x_2419_, v_size_2420_);
lean_dec(v_size_2420_);
v___x_2480_ = lean_nat_add(v___x_2479_, v_size_2421_);
lean_dec(v_size_2421_);
v___x_2481_ = lean_nat_add(v___x_2479_, v_size_2437_);
lean_dec(v___x_2479_);
lean_inc_ref(v_impl_2418_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v_l_2424_);
lean_ctor_set(v___x_2435_, 3, v_impl_2418_);
lean_ctor_set(v___x_2435_, 2, v_v_1935_);
lean_ctor_set(v___x_2435_, 1, v_k_1934_);
lean_ctor_set(v___x_2435_, 0, v___x_2481_);
v___x_2483_ = v___x_2435_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_impl_2418_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_l_2424_);
v___x_2483_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
v_isSharedCheck_2490_ = !lean_is_exclusive(v_impl_2418_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; lean_object* v_unused_2494_; lean_object* v_unused_2495_; 
v_unused_2491_ = lean_ctor_get(v_impl_2418_, 4);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_impl_2418_, 3);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_impl_2418_, 2);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_impl_2418_, 1);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_impl_2418_, 0);
lean_dec(v_unused_2495_);
v___x_2485_ = v_impl_2418_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_dec(v_impl_2418_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 4, v_r_2425_);
lean_ctor_set(v___x_2485_, 3, v___x_2483_);
lean_ctor_set(v___x_2485_, 2, v_v_2423_);
lean_ctor_set(v___x_2485_, 1, v_k_2422_);
lean_ctor_set(v___x_2485_, 0, v___x_2480_);
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_k_2422_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_v_2423_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_r_2425_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v_size_2503_ = lean_ctor_get(v_impl_2418_, 0);
lean_inc(v_size_2503_);
v___x_2504_ = lean_nat_add(v___x_2419_, v_size_2503_);
lean_dec(v_size_2503_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 3, v_impl_2418_);
lean_ctor_set(v___x_1939_, 0, v___x_2504_);
v___x_2506_ = v___x_1939_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2507_, 3, v_impl_2418_);
lean_ctor_set(v_reuseFailAlloc_2507_, 4, v_r_1937_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
else
{
if (lean_obj_tag(v_r_1937_) == 0)
{
lean_object* v_l_2508_; 
v_l_2508_ = lean_ctor_get(v_r_1937_, 3);
lean_inc(v_l_2508_);
if (lean_obj_tag(v_l_2508_) == 0)
{
lean_object* v_r_2509_; 
v_r_2509_ = lean_ctor_get(v_r_1937_, 4);
lean_inc(v_r_2509_);
if (lean_obj_tag(v_r_2509_) == 0)
{
lean_object* v_size_2510_; lean_object* v_k_2511_; lean_object* v_v_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2525_; 
v_size_2510_ = lean_ctor_get(v_r_1937_, 0);
v_k_2511_ = lean_ctor_get(v_r_1937_, 1);
v_v_2512_ = lean_ctor_get(v_r_1937_, 2);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; lean_object* v_unused_2527_; 
v_unused_2526_ = lean_ctor_get(v_r_1937_, 4);
lean_dec(v_unused_2526_);
v_unused_2527_ = lean_ctor_get(v_r_1937_, 3);
lean_dec(v_unused_2527_);
v___x_2514_ = v_r_1937_;
v_isShared_2515_ = v_isSharedCheck_2525_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_v_2512_);
lean_inc(v_k_2511_);
lean_inc(v_size_2510_);
lean_dec(v_r_1937_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2525_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v_size_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v_size_2516_ = lean_ctor_get(v_l_2508_, 0);
v___x_2517_ = lean_nat_add(v___x_2419_, v_size_2510_);
lean_dec(v_size_2510_);
v___x_2518_ = lean_nat_add(v___x_2419_, v_size_2516_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v_l_2508_);
lean_ctor_set(v___x_2514_, 3, v_impl_2418_);
lean_ctor_set(v___x_2514_, 2, v_v_1935_);
lean_ctor_set(v___x_2514_, 1, v_k_1934_);
lean_ctor_set(v___x_2514_, 0, v___x_2518_);
v___x_2520_ = v___x_2514_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2518_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2524_, 3, v_impl_2418_);
lean_ctor_set(v_reuseFailAlloc_2524_, 4, v_l_2508_);
v___x_2520_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_r_2509_);
lean_ctor_set(v___x_1939_, 3, v___x_2520_);
lean_ctor_set(v___x_1939_, 2, v_v_2512_);
lean_ctor_set(v___x_1939_, 1, v_k_2511_);
lean_ctor_set(v___x_1939_, 0, v___x_2517_);
v___x_2522_ = v___x_1939_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_k_2511_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_v_2512_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_r_2509_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_object* v_k_2528_; lean_object* v_v_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2552_; 
v_k_2528_ = lean_ctor_get(v_r_1937_, 1);
v_v_2529_ = lean_ctor_get(v_r_1937_, 2);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; lean_object* v_unused_2554_; lean_object* v_unused_2555_; 
v_unused_2553_ = lean_ctor_get(v_r_1937_, 4);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_r_1937_, 3);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_r_1937_, 0);
lean_dec(v_unused_2555_);
v___x_2531_ = v_r_1937_;
v_isShared_2532_ = v_isSharedCheck_2552_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_v_2529_);
lean_inc(v_k_2528_);
lean_dec(v_r_1937_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2552_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_k_2533_; lean_object* v_v_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2548_; 
v_k_2533_ = lean_ctor_get(v_l_2508_, 1);
v_v_2534_ = lean_ctor_get(v_l_2508_, 2);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_l_2508_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; lean_object* v_unused_2550_; lean_object* v_unused_2551_; 
v_unused_2549_ = lean_ctor_get(v_l_2508_, 4);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_l_2508_, 3);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v_l_2508_, 0);
lean_dec(v_unused_2551_);
v___x_2536_ = v_l_2508_;
v_isShared_2537_ = v_isSharedCheck_2548_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_v_2534_);
lean_inc(v_k_2533_);
lean_dec(v_l_2508_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2548_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = lean_unsigned_to_nat(3u);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 4, v_r_2509_);
lean_ctor_set(v___x_2536_, 3, v_r_2509_);
lean_ctor_set(v___x_2536_, 2, v_v_1935_);
lean_ctor_set(v___x_2536_, 1, v_k_1934_);
lean_ctor_set(v___x_2536_, 0, v___x_2419_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v_r_2509_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v_r_2509_);
v___x_2540_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2542_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 3, v_r_2509_);
lean_ctor_set(v___x_2531_, 0, v___x_2419_);
v___x_2542_ = v___x_2531_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_k_2528_);
lean_ctor_set(v_reuseFailAlloc_2546_, 2, v_v_2529_);
lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_r_2509_);
lean_ctor_set(v_reuseFailAlloc_2546_, 4, v_r_2509_);
v___x_2542_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v___x_2542_);
lean_ctor_set(v___x_1939_, 3, v___x_2540_);
lean_ctor_set(v___x_1939_, 2, v_v_2534_);
lean_ctor_set(v___x_1939_, 1, v_k_2533_);
lean_ctor_set(v___x_1939_, 0, v___x_2538_);
v___x_2544_ = v___x_1939_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_k_2533_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_v_2534_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2556_; 
v_r_2556_ = lean_ctor_get(v_r_1937_, 4);
lean_inc(v_r_2556_);
if (lean_obj_tag(v_r_2556_) == 0)
{
lean_object* v_k_2557_; lean_object* v_v_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2569_; 
v_k_2557_ = lean_ctor_get(v_r_1937_, 1);
v_v_2558_ = lean_ctor_get(v_r_1937_, 2);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; lean_object* v_unused_2571_; lean_object* v_unused_2572_; 
v_unused_2570_ = lean_ctor_get(v_r_1937_, 4);
lean_dec(v_unused_2570_);
v_unused_2571_ = lean_ctor_get(v_r_1937_, 3);
lean_dec(v_unused_2571_);
v_unused_2572_ = lean_ctor_get(v_r_1937_, 0);
lean_dec(v_unused_2572_);
v___x_2560_ = v_r_1937_;
v_isShared_2561_ = v_isSharedCheck_2569_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_v_2558_);
lean_inc(v_k_2557_);
lean_dec(v_r_1937_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2569_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2564_; 
v___x_2562_ = lean_unsigned_to_nat(3u);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 4, v_l_2508_);
lean_ctor_set(v___x_2560_, 2, v_v_1935_);
lean_ctor_set(v___x_2560_, 1, v_k_1934_);
lean_ctor_set(v___x_2560_, 0, v___x_2419_);
v___x_2564_ = v___x_2560_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v_l_2508_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v_l_2508_);
v___x_2564_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2566_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v_r_2556_);
lean_ctor_set(v___x_1939_, 3, v___x_2564_);
lean_ctor_set(v___x_1939_, 2, v_v_2558_);
lean_ctor_set(v___x_1939_, 1, v_k_2557_);
lean_ctor_set(v___x_1939_, 0, v___x_2562_);
v___x_2566_ = v___x_1939_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_k_2557_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_v_2558_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_r_2556_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
else
{
lean_object* v_size_2573_; lean_object* v_k_2574_; lean_object* v_v_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2586_; 
v_size_2573_ = lean_ctor_get(v_r_1937_, 0);
v_k_2574_ = lean_ctor_get(v_r_1937_, 1);
v_v_2575_ = lean_ctor_get(v_r_1937_, 2);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_r_1937_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; lean_object* v_unused_2588_; 
v_unused_2587_ = lean_ctor_get(v_r_1937_, 4);
lean_dec(v_unused_2587_);
v_unused_2588_ = lean_ctor_get(v_r_1937_, 3);
lean_dec(v_unused_2588_);
v___x_2577_ = v_r_1937_;
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_v_2575_);
lean_inc(v_k_2574_);
lean_inc(v_size_2573_);
lean_dec(v_r_1937_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 3, v_r_2556_);
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_size_2573_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_k_2574_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_v_2575_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_r_2556_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_r_2556_);
v___x_2580_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_unsigned_to_nat(2u);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v___x_2580_);
lean_ctor_set(v___x_1939_, 3, v_r_2556_);
lean_ctor_set(v___x_1939_, 0, v___x_2581_);
v___x_2583_ = v___x_1939_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_r_2556_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v___x_2580_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
else
{
lean_object* v___x_2590_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 3, v_r_1937_);
lean_ctor_set(v___x_1939_, 0, v___x_2419_);
v___x_2590_ = v___x_1939_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_k_1934_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_v_1935_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_r_1937_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_r_1937_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
}
else
{
return v_t_1933_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2594_, lean_object* v_t_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2594_, v_t_2595_);
lean_dec(v_k_2594_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object* v_id_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; lean_object* v_receivers_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_st_ref_get(v___y_2603_);
v_receivers_2606_ = lean_ctor_get(v___x_2605_, 7);
lean_inc(v_receivers_2606_);
v___x_2607_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2606_, v_id_2602_);
lean_dec(v_receivers_2606_);
if (lean_obj_tag(v___x_2607_) == 1)
{
lean_object* v_val_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_val_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_val_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2605_);
lean_ctor_set(v___x_2609_, 1, v_val_2608_);
v___x_2610_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2609_, v___y_2603_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2640_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2640_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2640_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v_fst_2615_; lean_object* v_producers_2616_; lean_object* v_waiters_2617_; lean_object* v_capacity_2618_; lean_object* v_size_2619_; lean_object* v_buffer_2620_; lean_object* v_write_2621_; lean_object* v_read_2622_; lean_object* v_receivers_2623_; lean_object* v_nextId_2624_; uint8_t v_closed_2625_; lean_object* v_pos_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2639_; 
v_fst_2615_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_fst_2615_);
lean_dec(v_a_2611_);
v_producers_2616_ = lean_ctor_get(v_fst_2615_, 0);
v_waiters_2617_ = lean_ctor_get(v_fst_2615_, 1);
v_capacity_2618_ = lean_ctor_get(v_fst_2615_, 2);
v_size_2619_ = lean_ctor_get(v_fst_2615_, 3);
v_buffer_2620_ = lean_ctor_get(v_fst_2615_, 4);
v_write_2621_ = lean_ctor_get(v_fst_2615_, 5);
v_read_2622_ = lean_ctor_get(v_fst_2615_, 6);
v_receivers_2623_ = lean_ctor_get(v_fst_2615_, 7);
v_nextId_2624_ = lean_ctor_get(v_fst_2615_, 8);
v_closed_2625_ = lean_ctor_get_uint8(v_fst_2615_, sizeof(void*)*10);
v_pos_2626_ = lean_ctor_get(v_fst_2615_, 9);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_fst_2615_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2628_ = v_fst_2615_;
v_isShared_2629_ = v_isSharedCheck_2639_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_pos_2626_);
lean_inc(v_nextId_2624_);
lean_inc(v_receivers_2623_);
lean_inc(v_read_2622_);
lean_inc(v_write_2621_);
lean_inc(v_buffer_2620_);
lean_inc(v_size_2619_);
lean_inc(v_capacity_2618_);
lean_inc(v_waiters_2617_);
lean_inc(v_producers_2616_);
lean_dec(v_fst_2615_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2639_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; lean_object* v___x_2632_; 
v___x_2630_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_id_2602_, v_receivers_2623_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 7, v___x_2630_);
v___x_2632_ = v___x_2628_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_producers_2616_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_waiters_2617_);
lean_ctor_set(v_reuseFailAlloc_2638_, 2, v_capacity_2618_);
lean_ctor_set(v_reuseFailAlloc_2638_, 3, v_size_2619_);
lean_ctor_set(v_reuseFailAlloc_2638_, 4, v_buffer_2620_);
lean_ctor_set(v_reuseFailAlloc_2638_, 5, v_write_2621_);
lean_ctor_set(v_reuseFailAlloc_2638_, 6, v_read_2622_);
lean_ctor_set(v_reuseFailAlloc_2638_, 7, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2638_, 8, v_nextId_2624_);
lean_ctor_set(v_reuseFailAlloc_2638_, 9, v_pos_2626_);
lean_ctor_set_uint8(v_reuseFailAlloc_2638_, sizeof(void*)*10, v_closed_2625_);
v___x_2632_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2633_ = lean_st_ref_swap(v___y_2603_, v___x_2632_);
lean_dec(v___x_2633_);
v___x_2634_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0));
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2634_);
v___x_2636_ = v___x_2613_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2610_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2610_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec(v___x_2607_);
lean_dec(v___x_2605_);
v___x_2649_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1));
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object* v_id_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec(v_id_2651_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object* v_bd_2655_){
_start:
{
lean_object* v_state_2657_; lean_object* v_id_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; 
v_state_2657_ = lean_ctor_get(v_bd_2655_, 0);
lean_inc_ref(v_state_2657_);
v_id_2658_ = lean_ctor_get(v_bd_2655_, 1);
lean_inc(v_id_2658_);
lean_dec_ref(v_bd_2655_);
v___f_2659_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2659_, 0, v_id_2658_);
v___x_2660_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_2657_, v___f_2659_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2685_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2663_ = v___x_2660_;
v_isShared_2664_ = v_isSharedCheck_2685_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2660_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2685_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___y_2666_; 
if (lean_obj_tag(v_a_2661_) == 0)
{
lean_object* v_a_2671_; uint8_t v___x_2672_; 
v_a_2671_ = lean_ctor_get(v_a_2661_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v_a_2661_, 1);
v___x_2672_ = lean_unbox(v_a_2671_);
lean_dec(v_a_2671_);
switch(v___x_2672_)
{
case 0:
{
lean_object* v___x_2673_; 
v___x_2673_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_2666_ = v___x_2673_;
goto v___jp_2665_;
}
case 1:
{
lean_object* v___x_2674_; 
v___x_2674_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_2666_ = v___x_2674_;
goto v___jp_2665_;
}
default: 
{
lean_object* v___x_2675_; 
v___x_2675_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_2666_ = v___x_2675_;
goto v___jp_2665_;
}
}
}
else
{
lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2683_; 
lean_del_object(v___x_2663_);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_a_2661_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v_a_2661_, 0);
lean_dec(v_unused_2684_);
v___x_2677_ = v_a_2661_;
v_isShared_2678_ = v_isSharedCheck_2683_;
goto v_resetjp_2676_;
}
else
{
lean_dec(v_a_2661_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2683_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2679_ = lean_box(0);
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2679_);
v___x_2681_ = v___x_2677_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
v___jp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_inc_ref(v___y_2666_);
v___x_2667_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___y_2666_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 1);
lean_ctor_set(v___x_2663_, 0, v___x_2667_);
v___x_2669_ = v___x_2663_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_a_2686_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2660_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2660_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object* v_bd_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object* v_00_u03b1_2697_, lean_object* v_bd_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_bd_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(v_00_u03b1_2701_, v_bd_2702_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object* v_00_u03b1_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2709_, lean_object* v_a_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(v_00_u03b1_2709_, v_a_2710_);
lean_dec(v_a_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object* v_00_u03b1_2713_, lean_object* v_place_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2714_, v_a_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2718_, lean_object* v_place_2719_, lean_object* v_a_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(v_00_u03b1_2718_, v_place_2719_, v_a_2720_);
lean_dec(v_a_2720_);
lean_dec(v_place_2719_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object* v_00_u03b1_2723_, lean_object* v_slot_2724_, lean_object* v_next_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2724_, v_next_2725_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2729_, lean_object* v_slot_2730_, lean_object* v_next_2731_, lean_object* v_a_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(v_00_u03b1_2729_, v_slot_2730_, v_next_2731_, v_a_2732_);
lean_dec(v_a_2732_);
lean_dec(v_next_2731_);
lean_dec(v_slot_2730_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object* v_00_u03b1_2735_, lean_object* v_next_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2736_, v_a_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object* v_00_u03b1_2740_, lean_object* v_next_2741_, lean_object* v_a_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(v_00_u03b1_2740_, v_next_2741_, v_a_2742_);
lean_dec(v_a_2742_);
lean_dec(v_next_2741_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object* v_00_u03b4_2745_, lean_object* v_t_2746_, lean_object* v_k_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2746_, v_k_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object* v_00_u03b4_2749_, lean_object* v_t_2750_, lean_object* v_k_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(v_00_u03b4_2749_, v_t_2750_, v_k_2751_);
lean_dec(v_k_2751_);
lean_dec(v_t_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2753_, lean_object* v_inst_2754_, lean_object* v_a_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_2755_, v___y_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_inst_2760_, lean_object* v_a_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2759_, v_inst_2760_, v_a_2761_, v___y_2762_);
lean_dec(v___y_2762_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2765_, lean_object* v_k_2766_, lean_object* v_t_2767_, lean_object* v_h_2768_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2766_, v_t_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2770_, lean_object* v_k_2771_, lean_object* v_t_2772_, lean_object* v_h_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2770_, v_k_2771_, v_t_2772_, v_h_2773_);
lean_dec(v_k_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2775_, lean_object* v_y_2776_){
_start:
{
uint8_t v___x_2777_; 
v___x_2777_ = lean_nat_dec_lt(v_x_2775_, v_y_2776_);
if (v___x_2777_ == 0)
{
uint8_t v___x_2778_; 
v___x_2778_ = lean_nat_dec_eq(v_x_2775_, v_y_2776_);
if (v___x_2778_ == 0)
{
uint8_t v___x_2779_; 
v___x_2779_ = 2;
return v___x_2779_;
}
else
{
uint8_t v___x_2780_; 
v___x_2780_ = 1;
return v___x_2780_;
}
}
else
{
uint8_t v___x_2781_; 
v___x_2781_ = 0;
return v___x_2781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2782_, lean_object* v_y_2783_){
_start:
{
uint8_t v_res_2784_; lean_object* v_r_2785_; 
v_res_2784_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2782_, v_y_2783_);
lean_dec(v_y_2783_);
lean_dec(v_x_2782_);
v_r_2785_ = lean_box(v_res_2784_);
return v_r_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_unsigned_to_nat(1u);
v___x_2788_ = lean_nat_add(v_x_2786_, v___x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2789_);
lean_dec(v_x_2789_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2791_, lean_object* v_receiverId_2792_, lean_object* v___f_2793_, lean_object* v_receivers_2794_, lean_object* v_s_2795_){
_start:
{
lean_object* v_producers_2796_; lean_object* v_waiters_2797_; lean_object* v_capacity_2798_; lean_object* v_size_2799_; lean_object* v_buffer_2800_; lean_object* v_write_2801_; lean_object* v_read_2802_; lean_object* v_nextId_2803_; uint8_t v_closed_2804_; lean_object* v_pos_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2815_; 
v_producers_2796_ = lean_ctor_get(v_s_2795_, 0);
v_waiters_2797_ = lean_ctor_get(v_s_2795_, 1);
v_capacity_2798_ = lean_ctor_get(v_s_2795_, 2);
v_size_2799_ = lean_ctor_get(v_s_2795_, 3);
v_buffer_2800_ = lean_ctor_get(v_s_2795_, 4);
v_write_2801_ = lean_ctor_get(v_s_2795_, 5);
v_read_2802_ = lean_ctor_get(v_s_2795_, 6);
v_nextId_2803_ = lean_ctor_get(v_s_2795_, 8);
v_closed_2804_ = lean_ctor_get_uint8(v_s_2795_, sizeof(void*)*10);
v_pos_2805_ = lean_ctor_get(v_s_2795_, 9);
v_isSharedCheck_2815_ = !lean_is_exclusive(v_s_2795_);
if (v_isSharedCheck_2815_ == 0)
{
lean_object* v_unused_2816_; 
v_unused_2816_ = lean_ctor_get(v_s_2795_, 7);
lean_dec(v_unused_2816_);
v___x_2807_ = v_s_2795_;
v_isShared_2808_ = v_isSharedCheck_2815_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_pos_2805_);
lean_inc(v_nextId_2803_);
lean_inc(v_read_2802_);
lean_inc(v_write_2801_);
lean_inc(v_buffer_2800_);
lean_inc(v_size_2799_);
lean_inc(v_capacity_2798_);
lean_inc(v_waiters_2797_);
lean_inc(v_producers_2796_);
lean_dec(v_s_2795_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2815_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2809_ = lean_box(0);
v___x_2810_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2791_, v_receiverId_2792_, v___f_2793_, v_receivers_2794_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 7, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_producers_2796_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_waiters_2797_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_capacity_2798_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v_size_2799_);
lean_ctor_set(v_reuseFailAlloc_2814_, 4, v_buffer_2800_);
lean_ctor_set(v_reuseFailAlloc_2814_, 5, v_write_2801_);
lean_ctor_set(v_reuseFailAlloc_2814_, 6, v_read_2802_);
lean_ctor_set(v_reuseFailAlloc_2814_, 7, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2814_, 8, v_nextId_2803_);
lean_ctor_set(v_reuseFailAlloc_2814_, 9, v_pos_2805_);
lean_ctor_set_uint8(v_reuseFailAlloc_2814_, sizeof(void*)*10, v_closed_2804_);
v___x_2812_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2809_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
return v___x_2813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_toPure_2820_; lean_object* v___x_2821_; 
v_toPure_2820_ = lean_ctor_get(v_toApplicative_2817_, 1);
lean_inc(v_toPure_2820_);
lean_dec_ref(v_toApplicative_2817_);
v___x_2821_ = lean_apply_2(v_toPure_2820_, lean_box(0), v_a_2818_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2822_, lean_object* v_a_2823_, lean_object* v___f_2824_, lean_object* v_inst_2825_, lean_object* v_toBind_2826_, lean_object* v_a_2827_){
_start:
{
if (lean_obj_tag(v_a_2827_) == 1)
{
lean_object* v___f_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___f_2828_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2828_, 0, v_toApplicative_2822_);
lean_closure_set(v___f_2828_, 1, v_a_2827_);
lean_inc(v_a_2823_);
v___x_2829_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2829_, 0, lean_box(0));
lean_closure_set(v___x_2829_, 1, lean_box(0));
lean_closure_set(v___x_2829_, 2, lean_box(0));
lean_closure_set(v___x_2829_, 3, v_a_2823_);
lean_closure_set(v___x_2829_, 4, v___f_2824_);
v___x_2830_ = lean_apply_2(v_inst_2825_, lean_box(0), v___x_2829_);
v___x_2831_ = lean_apply_4(v_toBind_2826_, lean_box(0), lean_box(0), v___x_2830_, v___f_2828_);
return v___x_2831_;
}
else
{
lean_object* v_toPure_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec(v_a_2827_);
lean_dec(v_toBind_2826_);
lean_dec(v_inst_2825_);
lean_dec_ref(v___f_2824_);
v_toPure_2832_ = lean_ctor_get(v_toApplicative_2822_, 1);
lean_inc(v_toPure_2832_);
lean_dec_ref(v_toApplicative_2822_);
v___x_2833_ = lean_box(0);
v___x_2834_ = lean_apply_2(v_toPure_2832_, lean_box(0), v___x_2833_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_2835_, lean_object* v_a_2836_, lean_object* v___f_2837_, lean_object* v_inst_2838_, lean_object* v_toBind_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(v_toApplicative_2835_, v_a_2836_, v___f_2837_, v_inst_2838_, v_toBind_2839_, v_a_2840_);
lean_dec(v_a_2836_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2842_, lean_object* v_receiverId_2843_, lean_object* v___f_2844_, lean_object* v___f_2845_, lean_object* v_toApplicative_2846_, lean_object* v_a_2847_, lean_object* v_inst_2848_, lean_object* v_toBind_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_receivers_2853_; lean_object* v___x_2854_; 
v_receivers_2853_ = lean_ctor_get(v_a_2852_, 7);
lean_inc_n(v_receivers_2853_, 2);
lean_dec_ref(v_a_2852_);
lean_inc(v_receiverId_2843_);
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2842_, v_receivers_2853_, v_receiverId_2843_);
if (lean_obj_tag(v___x_2854_) == 1)
{
lean_object* v_val_2855_; lean_object* v___f_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_val_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___f_2856_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2856_, 0, v___f_2844_);
lean_closure_set(v___f_2856_, 1, v_receiverId_2843_);
lean_closure_set(v___f_2856_, 2, v___f_2845_);
lean_closure_set(v___f_2856_, 3, v_receivers_2853_);
lean_inc(v_toBind_2849_);
lean_inc(v_inst_2848_);
lean_inc(v_a_2847_);
v___f_2857_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2857_, 0, v_toApplicative_2846_);
lean_closure_set(v___f_2857_, 1, v_a_2847_);
lean_closure_set(v___f_2857_, 2, v___f_2856_);
lean_closure_set(v___f_2857_, 3, v_inst_2848_);
lean_closure_set(v___f_2857_, 4, v_toBind_2849_);
v___x_2858_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2850_, v_inst_2848_, v_inst_2851_, v_val_2855_, v_a_2847_);
v___x_2859_ = lean_apply_4(v_toBind_2849_, lean_box(0), lean_box(0), v___x_2858_, v___f_2857_);
return v___x_2859_;
}
else
{
lean_object* v_toPure_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_dec(v___x_2854_);
lean_dec(v_receivers_2853_);
lean_dec(v_inst_2851_);
lean_dec_ref(v_inst_2850_);
lean_dec(v_toBind_2849_);
lean_dec(v_inst_2848_);
lean_dec_ref(v___f_2845_);
lean_dec_ref(v___f_2844_);
lean_dec(v_receiverId_2843_);
v_toPure_2860_ = lean_ctor_get(v_toApplicative_2846_, 1);
lean_inc(v_toPure_2860_);
lean_dec_ref(v_toApplicative_2846_);
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_apply_2(v_toPure_2860_, lean_box(0), v___x_2861_);
return v___x_2862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object* v___f_2863_, lean_object* v_receiverId_2864_, lean_object* v___f_2865_, lean_object* v___f_2866_, lean_object* v_toApplicative_2867_, lean_object* v_a_2868_, lean_object* v_inst_2869_, lean_object* v_toBind_2870_, lean_object* v_inst_2871_, lean_object* v_inst_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(v___f_2863_, v_receiverId_2864_, v___f_2865_, v___f_2866_, v_toApplicative_2867_, v_a_2868_, v_inst_2869_, v_toBind_2870_, v_inst_2871_, v_inst_2872_, v_a_2873_);
lean_dec(v_a_2868_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_receiverId_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_toApplicative_2882_; lean_object* v_toBind_2883_; lean_object* v___f_2884_; lean_object* v___f_2885_; lean_object* v___f_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_toApplicative_2882_ = lean_ctor_get(v_inst_2877_, 0);
lean_inc_ref(v_toApplicative_2882_);
v_toBind_2883_ = lean_ctor_get(v_inst_2877_, 1);
lean_inc_n(v_toBind_2883_, 2);
v___f_2884_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_2885_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_inst_2878_);
lean_inc_n(v_a_2881_, 2);
v___f_2886_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_2886_, 0, v___f_2884_);
lean_closure_set(v___f_2886_, 1, v_receiverId_2880_);
lean_closure_set(v___f_2886_, 2, v___f_2884_);
lean_closure_set(v___f_2886_, 3, v___f_2885_);
lean_closure_set(v___f_2886_, 4, v_toApplicative_2882_);
lean_closure_set(v___f_2886_, 5, v_a_2881_);
lean_closure_set(v___f_2886_, 6, v_inst_2878_);
lean_closure_set(v___f_2886_, 7, v_toBind_2883_);
lean_closure_set(v___f_2886_, 8, v_inst_2877_);
lean_closure_set(v___f_2886_, 9, v_inst_2879_);
v___x_2887_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2887_, 0, lean_box(0));
lean_closure_set(v___x_2887_, 1, lean_box(0));
lean_closure_set(v___x_2887_, 2, v_a_2881_);
v___x_2888_ = lean_apply_2(v_inst_2878_, lean_box(0), v___x_2887_);
v___x_2889_ = lean_apply_4(v_toBind_2883_, lean_box(0), lean_box(0), v___x_2888_, v___f_2886_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_receiverId_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2890_, v_inst_2891_, v_inst_2892_, v_receiverId_2893_, v_a_2894_);
lean_dec(v_a_2894_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_2896_, lean_object* v_00_u03b1_2897_, lean_object* v_inst_2898_, lean_object* v_inst_2899_, lean_object* v_inst_2900_, lean_object* v_receiverId_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2898_, v_inst_2899_, v_inst_2900_, v_receiverId_2901_, v_a_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object* v_m_2904_, lean_object* v_00_u03b1_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_receiverId_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(v_m_2904_, v_00_u03b1_2905_, v_inst_2906_, v_inst_2907_, v_inst_2908_, v_receiverId_2909_, v_a_2910_);
lean_dec(v_a_2910_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_2912_, lean_object* v_t_2913_){
_start:
{
if (lean_obj_tag(v_t_2913_) == 0)
{
lean_object* v_size_2914_; lean_object* v_k_2915_; lean_object* v_v_2916_; lean_object* v_l_2917_; lean_object* v_r_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2937_; 
v_size_2914_ = lean_ctor_get(v_t_2913_, 0);
v_k_2915_ = lean_ctor_get(v_t_2913_, 1);
v_v_2916_ = lean_ctor_get(v_t_2913_, 2);
v_l_2917_ = lean_ctor_get(v_t_2913_, 3);
v_r_2918_ = lean_ctor_get(v_t_2913_, 4);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_t_2913_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2920_ = v_t_2913_;
v_isShared_2921_ = v_isSharedCheck_2937_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_r_2918_);
lean_inc(v_l_2917_);
lean_inc(v_v_2916_);
lean_inc(v_k_2915_);
lean_inc(v_size_2914_);
lean_dec(v_t_2913_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2937_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_nat_dec_lt(v_k_2912_, v_k_2915_);
if (v___x_2922_ == 0)
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_nat_dec_eq(v_k_2912_, v_k_2915_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2924_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2912_, v_r_2918_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 4, v___x_2924_);
v___x_2926_ = v___x_2920_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_size_2914_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_k_2915_);
lean_ctor_set(v_reuseFailAlloc_2927_, 2, v_v_2916_);
lean_ctor_set(v_reuseFailAlloc_2927_, 3, v_l_2917_);
lean_ctor_set(v_reuseFailAlloc_2927_, 4, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
lean_dec(v_k_2915_);
v___x_2928_ = lean_unsigned_to_nat(1u);
v___x_2929_ = lean_nat_add(v_v_2916_, v___x_2928_);
lean_dec(v_v_2916_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 2, v___x_2929_);
lean_ctor_set(v___x_2920_, 1, v_k_2912_);
v___x_2931_ = v___x_2920_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_size_2914_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_k_2912_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v___x_2929_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_l_2917_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v_r_2918_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2933_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2912_, v_l_2917_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 3, v___x_2933_);
v___x_2935_ = v___x_2920_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_size_2914_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_k_2915_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_v_2916_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2936_, 4, v_r_2918_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_dec(v_k_2912_);
return v_t_2913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_2938_, lean_object* v_next_2939_){
_start:
{
lean_object* v___x_2941_; lean_object* v_fst_2943_; lean_object* v_snd_2944_; lean_object* v_value_2946_; lean_object* v_pos_2947_; lean_object* v_remaining_2948_; uint8_t v___x_2949_; 
v___x_2941_ = lean_st_ref_take(v_slot_2938_);
v_value_2946_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_value_2946_);
v_pos_2947_ = lean_ctor_get(v___x_2941_, 1);
lean_inc(v_pos_2947_);
v_remaining_2948_ = lean_ctor_get(v___x_2941_, 2);
lean_inc(v_remaining_2948_);
v___x_2949_ = lean_nat_dec_eq(v_next_2939_, v_pos_2947_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
lean_dec(v_remaining_2948_);
lean_dec(v_pos_2947_);
lean_dec(v_value_2946_);
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_box(v___x_2949_);
v___x_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v_fst_2943_ = v___x_2952_;
v_snd_2944_ = v___x_2941_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2971_; 
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; lean_object* v_unused_2973_; lean_object* v_unused_2974_; 
v_unused_2972_ = lean_ctor_get(v___x_2941_, 2);
lean_dec(v_unused_2972_);
v_unused_2973_ = lean_ctor_get(v___x_2941_, 1);
lean_dec(v_unused_2973_);
v_unused_2974_ = lean_ctor_get(v___x_2941_, 0);
lean_dec(v_unused_2974_);
v___x_2954_ = v___x_2941_;
v_isShared_2955_ = v_isSharedCheck_2971_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v___x_2941_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2971_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2956_ = lean_unsigned_to_nat(1u);
v___x_2957_ = lean_nat_dec_eq(v_remaining_2948_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2958_ = lean_box(v___x_2957_);
lean_inc(v_value_2946_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_value_2946_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_nat_sub(v_remaining_2948_, v___x_2956_);
lean_dec(v_remaining_2948_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 2, v___x_2960_);
v___x_2962_ = v___x_2954_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_value_2946_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_pos_2947_);
lean_ctor_set(v_reuseFailAlloc_2963_, 2, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
v_fst_2943_ = v___x_2959_;
v_snd_2944_ = v___x_2962_;
goto v___jp_2942_;
}
}
else
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2969_; 
lean_dec(v_remaining_2948_);
v___x_2964_ = lean_box(v___x_2949_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_value_2946_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v___x_2966_ = lean_box(0);
v___x_2967_ = lean_unsigned_to_nat(0u);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 2, v___x_2967_);
lean_ctor_set(v___x_2954_, 0, v___x_2966_);
v___x_2969_ = v___x_2954_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_pos_2947_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
v_fst_2943_ = v___x_2965_;
v_snd_2944_ = v___x_2969_;
goto v___jp_2942_;
}
}
}
}
v___jp_2942_:
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_st_ref_put(v_slot_2938_, v_snd_2944_);
return v_fst_2943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_2975_, lean_object* v_next_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_2975_, v_next_2976_);
lean_dec(v_next_2976_);
lean_dec(v_slot_2975_);
return v_res_2978_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2981_; lean_object* v_size_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2981_ = lean_st_ref_get(v_a_2979_);
v_size_2982_ = lean_ctor_get(v___x_2981_, 3);
lean_inc(v_size_2982_);
lean_dec(v___x_2981_);
v___x_2983_ = lean_unsigned_to_nat(0u);
v___x_2984_ = lean_nat_dec_eq(v_size_2982_, v___x_2983_);
lean_dec(v_size_2982_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v_res_2987_; lean_object* v_r_2988_; 
v_res_2987_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_2985_);
lean_dec(v_a_2985_);
v_r_2988_ = lean_box(v_res_2987_);
return v_r_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2992_; lean_object* v_capacity_2993_; lean_object* v_buffer_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2992_ = lean_st_ref_get(v_a_2990_);
v_capacity_2993_ = lean_ctor_get(v___x_2992_, 2);
lean_inc(v_capacity_2993_);
v_buffer_2994_ = lean_ctor_get(v___x_2992_, 4);
lean_inc_ref(v_buffer_2994_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_nat_mod(v_place_2989_, v_capacity_2993_);
lean_dec(v_capacity_2993_);
v___x_2996_ = lean_array_fget(v_buffer_2994_, v___x_2995_);
lean_dec(v___x_2995_);
lean_dec_ref(v_buffer_2994_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_2997_, lean_object* v_a_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_2997_, v_a_2998_);
lean_dec(v_a_2998_);
lean_dec(v_place_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = lean_st_ref_get(v_a_3002_);
v___x_3005_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3002_);
if (v___x_3005_ == 0)
{
lean_object* v_capacity_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v_fst_3010_; lean_object* v_snd_3011_; lean_object* v_st_3013_; lean_object* v___y_3014_; 
v_capacity_3006_ = lean_ctor_get(v___x_3004_, 2);
lean_inc(v_capacity_3006_);
v___x_3007_ = lean_nat_mod(v_next_3001_, v_capacity_3006_);
lean_dec(v_capacity_3006_);
v___x_3008_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_3007_, v_a_3002_);
lean_dec(v___x_3007_);
v___x_3009_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_3008_, v_next_3001_);
lean_dec(v___x_3008_);
v_fst_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_fst_3010_);
v_snd_3011_ = lean_ctor_get(v___x_3009_, 1);
lean_inc(v_snd_3011_);
lean_dec_ref(v___x_3009_);
if (lean_obj_tag(v_fst_3010_) == 1)
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_unbox(v_snd_3011_);
if (v___x_3016_ == 0)
{
lean_dec(v_snd_3011_);
v_st_3013_ = v___x_3004_;
v___y_3014_ = v_a_3002_;
goto v___jp_3012_;
}
else
{
lean_object* v___x_3017_; lean_object* v_producers_3018_; lean_object* v_waiters_3019_; lean_object* v_capacity_3020_; lean_object* v_size_3021_; lean_object* v_buffer_3022_; lean_object* v_write_3023_; lean_object* v_read_3024_; lean_object* v_receivers_3025_; lean_object* v_nextId_3026_; uint8_t v_closed_3027_; lean_object* v_pos_3028_; lean_object* v___x_3029_; 
v___x_3017_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_3004_);
v_producers_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_ref(v_producers_3018_);
v_waiters_3019_ = lean_ctor_get(v___x_3017_, 1);
lean_inc_ref(v_waiters_3019_);
v_capacity_3020_ = lean_ctor_get(v___x_3017_, 2);
lean_inc(v_capacity_3020_);
v_size_3021_ = lean_ctor_get(v___x_3017_, 3);
lean_inc(v_size_3021_);
v_buffer_3022_ = lean_ctor_get(v___x_3017_, 4);
lean_inc_ref(v_buffer_3022_);
v_write_3023_ = lean_ctor_get(v___x_3017_, 5);
lean_inc(v_write_3023_);
v_read_3024_ = lean_ctor_get(v___x_3017_, 6);
lean_inc(v_read_3024_);
v_receivers_3025_ = lean_ctor_get(v___x_3017_, 7);
lean_inc(v_receivers_3025_);
v_nextId_3026_ = lean_ctor_get(v___x_3017_, 8);
lean_inc(v_nextId_3026_);
v_closed_3027_ = lean_ctor_get_uint8(v___x_3017_, sizeof(void*)*10);
v_pos_3028_ = lean_ctor_get(v___x_3017_, 9);
lean_inc(v_pos_3028_);
v___x_3029_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3018_);
if (lean_obj_tag(v___x_3029_) == 1)
{
lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3040_; 
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3040_ == 0)
{
lean_object* v_unused_3041_; lean_object* v_unused_3042_; lean_object* v_unused_3043_; lean_object* v_unused_3044_; lean_object* v_unused_3045_; lean_object* v_unused_3046_; lean_object* v_unused_3047_; lean_object* v_unused_3048_; lean_object* v_unused_3049_; lean_object* v_unused_3050_; 
v_unused_3041_ = lean_ctor_get(v___x_3017_, 9);
lean_dec(v_unused_3041_);
v_unused_3042_ = lean_ctor_get(v___x_3017_, 8);
lean_dec(v_unused_3042_);
v_unused_3043_ = lean_ctor_get(v___x_3017_, 7);
lean_dec(v_unused_3043_);
v_unused_3044_ = lean_ctor_get(v___x_3017_, 6);
lean_dec(v_unused_3044_);
v_unused_3045_ = lean_ctor_get(v___x_3017_, 5);
lean_dec(v_unused_3045_);
v_unused_3046_ = lean_ctor_get(v___x_3017_, 4);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v___x_3017_, 3);
lean_dec(v_unused_3047_);
v_unused_3048_ = lean_ctor_get(v___x_3017_, 2);
lean_dec(v_unused_3048_);
v_unused_3049_ = lean_ctor_get(v___x_3017_, 1);
lean_dec(v_unused_3049_);
v_unused_3050_ = lean_ctor_get(v___x_3017_, 0);
lean_dec(v_unused_3050_);
v___x_3031_ = v___x_3017_;
v_isShared_3032_ = v_isSharedCheck_3040_;
goto v_resetjp_3030_;
}
else
{
lean_dec(v___x_3017_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3040_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_val_3033_; lean_object* v_fst_3034_; lean_object* v_snd_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
v_val_3033_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_val_3033_);
lean_dec_ref_known(v___x_3029_, 1);
v_fst_3034_ = lean_ctor_get(v_val_3033_, 0);
lean_inc(v_fst_3034_);
v_snd_3035_ = lean_ctor_get(v_val_3033_, 1);
lean_inc(v_snd_3035_);
lean_dec(v_val_3033_);
v___x_3036_ = lean_io_promise_resolve(v_snd_3011_, v_fst_3034_);
lean_dec(v_fst_3034_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v_snd_3035_);
v___x_3038_ = v___x_3031_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_snd_3035_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_waiters_3019_);
lean_ctor_set(v_reuseFailAlloc_3039_, 2, v_capacity_3020_);
lean_ctor_set(v_reuseFailAlloc_3039_, 3, v_size_3021_);
lean_ctor_set(v_reuseFailAlloc_3039_, 4, v_buffer_3022_);
lean_ctor_set(v_reuseFailAlloc_3039_, 5, v_write_3023_);
lean_ctor_set(v_reuseFailAlloc_3039_, 6, v_read_3024_);
lean_ctor_set(v_reuseFailAlloc_3039_, 7, v_receivers_3025_);
lean_ctor_set(v_reuseFailAlloc_3039_, 8, v_nextId_3026_);
lean_ctor_set(v_reuseFailAlloc_3039_, 9, v_pos_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3039_, sizeof(void*)*10, v_closed_3027_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
v_st_3013_ = v___x_3038_;
v___y_3014_ = v_a_3002_;
goto v___jp_3012_;
}
}
}
else
{
lean_dec(v___x_3029_);
lean_dec(v_pos_3028_);
lean_dec(v_nextId_3026_);
lean_dec(v_receivers_3025_);
lean_dec(v_read_3024_);
lean_dec(v_write_3023_);
lean_dec_ref(v_buffer_3022_);
lean_dec(v_size_3021_);
lean_dec(v_capacity_3020_);
lean_dec_ref(v_waiters_3019_);
lean_dec(v_snd_3011_);
v_st_3013_ = v___x_3017_;
v___y_3014_ = v_a_3002_;
goto v___jp_3012_;
}
}
}
else
{
lean_object* v___x_3051_; 
lean_dec(v_snd_3011_);
lean_dec(v_fst_3010_);
lean_dec(v___x_3004_);
v___x_3051_ = lean_box(0);
return v___x_3051_;
}
v___jp_3012_:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_st_ref_swap(v___y_3014_, v_st_3013_);
lean_dec(v___x_3015_);
return v_fst_3010_;
}
}
else
{
lean_object* v___x_3052_; 
lean_dec(v___x_3004_);
v___x_3052_ = lean_box(0);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_3053_, lean_object* v_a_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3053_, v_a_3054_);
lean_dec(v_a_3054_);
lean_dec(v_next_3053_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3060_; lean_object* v_receivers_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_st_ref_get(v_a_3058_);
v_receivers_3061_ = lean_ctor_get(v___x_3060_, 7);
lean_inc(v_receivers_3061_);
lean_dec(v___x_3060_);
v___x_3062_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3061_, v_receiverId_3057_);
if (lean_obj_tag(v___x_3062_) == 1)
{
lean_object* v_val_3063_; lean_object* v___x_3064_; 
v_val_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_val_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___x_3064_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_3063_, v_a_3058_);
lean_dec(v_val_3063_);
if (lean_obj_tag(v___x_3064_) == 1)
{
lean_object* v___x_3065_; lean_object* v_producers_3066_; lean_object* v_waiters_3067_; lean_object* v_capacity_3068_; lean_object* v_size_3069_; lean_object* v_buffer_3070_; lean_object* v_write_3071_; lean_object* v_read_3072_; lean_object* v_nextId_3073_; uint8_t v_closed_3074_; lean_object* v_pos_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3084_; 
v___x_3065_ = lean_st_ref_take(v_a_3058_);
v_producers_3066_ = lean_ctor_get(v___x_3065_, 0);
v_waiters_3067_ = lean_ctor_get(v___x_3065_, 1);
v_capacity_3068_ = lean_ctor_get(v___x_3065_, 2);
v_size_3069_ = lean_ctor_get(v___x_3065_, 3);
v_buffer_3070_ = lean_ctor_get(v___x_3065_, 4);
v_write_3071_ = lean_ctor_get(v___x_3065_, 5);
v_read_3072_ = lean_ctor_get(v___x_3065_, 6);
v_nextId_3073_ = lean_ctor_get(v___x_3065_, 8);
v_closed_3074_ = lean_ctor_get_uint8(v___x_3065_, sizeof(void*)*10);
v_pos_3075_ = lean_ctor_get(v___x_3065_, 9);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; 
v_unused_3085_ = lean_ctor_get(v___x_3065_, 7);
lean_dec(v_unused_3085_);
v___x_3077_ = v___x_3065_;
v_isShared_3078_ = v_isSharedCheck_3084_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_pos_3075_);
lean_inc(v_nextId_3073_);
lean_inc(v_read_3072_);
lean_inc(v_write_3071_);
lean_inc(v_buffer_3070_);
lean_inc(v_size_3069_);
lean_inc(v_capacity_3068_);
lean_inc(v_waiters_3067_);
lean_inc(v_producers_3066_);
lean_dec(v___x_3065_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3084_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3079_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3057_, v_receivers_3061_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 7, v___x_3079_);
v___x_3081_ = v___x_3077_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_producers_3066_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_waiters_3067_);
lean_ctor_set(v_reuseFailAlloc_3083_, 2, v_capacity_3068_);
lean_ctor_set(v_reuseFailAlloc_3083_, 3, v_size_3069_);
lean_ctor_set(v_reuseFailAlloc_3083_, 4, v_buffer_3070_);
lean_ctor_set(v_reuseFailAlloc_3083_, 5, v_write_3071_);
lean_ctor_set(v_reuseFailAlloc_3083_, 6, v_read_3072_);
lean_ctor_set(v_reuseFailAlloc_3083_, 7, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3083_, 8, v_nextId_3073_);
lean_ctor_set(v_reuseFailAlloc_3083_, 9, v_pos_3075_);
lean_ctor_set_uint8(v_reuseFailAlloc_3083_, sizeof(void*)*10, v_closed_3074_);
v___x_3081_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_st_ref_put(v_a_3058_, v___x_3081_);
return v___x_3064_;
}
}
}
else
{
lean_object* v___x_3086_; 
lean_dec(v___x_3064_);
lean_dec(v_receivers_3061_);
lean_dec(v_receiverId_3057_);
v___x_3086_ = lean_box(0);
return v___x_3086_;
}
}
else
{
lean_object* v___x_3087_; 
lean_dec(v___x_3062_);
lean_dec(v_receivers_3061_);
lean_dec(v_receiverId_3057_);
v___x_3087_ = lean_box(0);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3088_, lean_object* v_a_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3088_, v_a_3089_);
lean_dec(v_a_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3092_, v___y_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3096_, v___y_3097_);
lean_dec(v___y_3097_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3100_){
_start:
{
lean_object* v_state_3102_; lean_object* v_id_3103_; lean_object* v___f_3104_; lean_object* v___x_3105_; 
v_state_3102_ = lean_ctor_get(v_ch_3100_, 0);
lean_inc_ref(v_state_3102_);
v_id_3103_ = lean_ctor_get(v_ch_3100_, 1);
lean_inc(v_id_3103_);
lean_dec_ref(v_ch_3100_);
v___f_3104_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3104_, 0, v_id_3103_);
v___x_3105_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3102_, v___f_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3106_, lean_object* v_a_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3106_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3109_, lean_object* v_ch_3110_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3110_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3113_, lean_object* v_ch_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3113_, v_ch_3114_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3117_, lean_object* v_receiverId_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3118_, v_a_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3122_, lean_object* v_receiverId_3123_, lean_object* v_a_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3122_, v_receiverId_3123_, v_a_3124_);
lean_dec(v_a_3124_);
return v_res_3126_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3127_, lean_object* v_a_3128_){
_start:
{
uint8_t v___x_3130_; 
v___x_3130_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3131_, lean_object* v_a_3132_, lean_object* v___y_3133_){
_start:
{
uint8_t v_res_3134_; lean_object* v_r_3135_; 
v_res_3134_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3131_, v_a_3132_);
lean_dec(v_a_3132_);
v_r_3135_ = lean_box(v_res_3134_);
return v_r_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3136_, lean_object* v_place_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3137_, v_a_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3141_, lean_object* v_place_3142_, lean_object* v_a_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3141_, v_place_3142_, v_a_3143_);
lean_dec(v_a_3143_);
lean_dec(v_place_3142_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3146_, lean_object* v_slot_3147_, lean_object* v_next_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v___x_3151_; 
v___x_3151_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3147_, v_next_3148_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3152_, lean_object* v_slot_3153_, lean_object* v_next_3154_, lean_object* v_a_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3152_, v_slot_3153_, v_next_3154_, v_a_3155_);
lean_dec(v_a_3155_);
lean_dec(v_next_3154_);
lean_dec(v_slot_3153_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3158_, lean_object* v_next_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v___x_3162_; 
v___x_3162_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3159_, v_a_3160_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3163_, lean_object* v_next_3164_, lean_object* v_a_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3163_, v_next_3164_, v_a_3165_);
lean_dec(v_a_3165_);
lean_dec(v_next_3164_);
return v_res_3167_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3168_, lean_object* v_t_3169_){
_start:
{
if (lean_obj_tag(v_t_3169_) == 0)
{
lean_object* v_k_3170_; lean_object* v_l_3171_; lean_object* v_r_3172_; uint8_t v___x_3173_; 
v_k_3170_ = lean_ctor_get(v_t_3169_, 1);
v_l_3171_ = lean_ctor_get(v_t_3169_, 3);
v_r_3172_ = lean_ctor_get(v_t_3169_, 4);
v___x_3173_ = lean_nat_dec_lt(v_k_3168_, v_k_3170_);
if (v___x_3173_ == 0)
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_nat_dec_eq(v_k_3168_, v_k_3170_);
if (v___x_3174_ == 0)
{
v_t_3169_ = v_r_3172_;
goto _start;
}
else
{
return v___x_3174_;
}
}
else
{
v_t_3169_ = v_l_3171_;
goto _start;
}
}
else
{
uint8_t v___x_3177_; 
v___x_3177_ = 0;
return v___x_3177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3178_, lean_object* v_t_3179_){
_start:
{
uint8_t v_res_3180_; lean_object* v_r_3181_; 
v_res_3180_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3178_, v_t_3179_);
lean_dec(v_t_3179_);
lean_dec(v_k_3178_);
v_r_3181_ = lean_box(v_res_3180_);
return v_r_3181_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_task_pure(v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3184_, lean_object* v___f_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v___x_3188_; lean_object* v_receivers_3189_; uint8_t v___x_3190_; 
v___x_3188_ = lean_st_ref_get(v___y_3186_);
v_receivers_3189_ = lean_ctor_get(v___x_3188_, 7);
lean_inc(v_receivers_3189_);
lean_dec(v___x_3188_);
v___x_3190_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3184_, v_receivers_3189_);
lean_dec(v_receivers_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_dec_ref(v___f_3185_);
lean_dec(v_id_3184_);
v___x_3191_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3191_;
}
else
{
lean_object* v___x_3192_; 
v___x_3192_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3184_, v___y_3186_);
if (lean_obj_tag(v___x_3192_) == 1)
{
lean_object* v___x_3193_; 
lean_dec_ref(v___f_3185_);
v___x_3193_ = lean_task_pure(v___x_3192_);
return v___x_3193_;
}
else
{
lean_object* v___x_3194_; uint8_t v_closed_3195_; 
lean_dec(v___x_3192_);
v___x_3194_ = lean_st_ref_get(v___y_3186_);
v_closed_3195_ = lean_ctor_get_uint8(v___x_3194_, sizeof(void*)*10);
lean_dec(v___x_3194_);
if (v_closed_3195_ == 0)
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_producers_3198_; lean_object* v_waiters_3199_; lean_object* v_capacity_3200_; lean_object* v_size_3201_; lean_object* v_buffer_3202_; lean_object* v_write_3203_; lean_object* v_read_3204_; lean_object* v_receivers_3205_; lean_object* v_nextId_3206_; uint8_t v_closed_3207_; lean_object* v_pos_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3222_; 
v___x_3196_ = lean_io_promise_new();
v___x_3197_ = lean_st_ref_take(v___y_3186_);
v_producers_3198_ = lean_ctor_get(v___x_3197_, 0);
v_waiters_3199_ = lean_ctor_get(v___x_3197_, 1);
v_capacity_3200_ = lean_ctor_get(v___x_3197_, 2);
v_size_3201_ = lean_ctor_get(v___x_3197_, 3);
v_buffer_3202_ = lean_ctor_get(v___x_3197_, 4);
v_write_3203_ = lean_ctor_get(v___x_3197_, 5);
v_read_3204_ = lean_ctor_get(v___x_3197_, 6);
v_receivers_3205_ = lean_ctor_get(v___x_3197_, 7);
v_nextId_3206_ = lean_ctor_get(v___x_3197_, 8);
v_closed_3207_ = lean_ctor_get_uint8(v___x_3197_, sizeof(void*)*10);
v_pos_3208_ = lean_ctor_get(v___x_3197_, 9);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3210_ = v___x_3197_;
v_isShared_3211_ = v_isSharedCheck_3222_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_pos_3208_);
lean_inc(v_nextId_3206_);
lean_inc(v_receivers_3205_);
lean_inc(v_read_3204_);
lean_inc(v_write_3203_);
lean_inc(v_buffer_3202_);
lean_inc(v_size_3201_);
lean_inc(v_capacity_3200_);
lean_inc(v_waiters_3199_);
lean_inc(v_producers_3198_);
lean_dec(v___x_3197_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3222_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3212_ = lean_box(0);
lean_inc(v___x_3196_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3196_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l_Std_Queue_enqueue___redArg(v___x_3213_, v_waiters_3199_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v___x_3214_);
v___x_3216_ = v___x_3210_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_producers_3198_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_capacity_3200_);
lean_ctor_set(v_reuseFailAlloc_3221_, 3, v_size_3201_);
lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_buffer_3202_);
lean_ctor_set(v_reuseFailAlloc_3221_, 5, v_write_3203_);
lean_ctor_set(v_reuseFailAlloc_3221_, 6, v_read_3204_);
lean_ctor_set(v_reuseFailAlloc_3221_, 7, v_receivers_3205_);
lean_ctor_set(v_reuseFailAlloc_3221_, 8, v_nextId_3206_);
lean_ctor_set(v_reuseFailAlloc_3221_, 9, v_pos_3208_);
lean_ctor_set_uint8(v_reuseFailAlloc_3221_, sizeof(void*)*10, v_closed_3207_);
v___x_3216_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3217_ = lean_st_ref_put(v___y_3186_, v___x_3216_);
v___x_3218_ = lean_io_promise_result_opt(v___x_3196_);
lean_dec(v___x_3196_);
v___x_3219_ = lean_unsigned_to_nat(0u);
v___x_3220_ = lean_io_bind_task(v___x_3218_, v___f_3185_, v___x_3219_, v_closed_3195_);
return v___x_3220_;
}
}
}
else
{
lean_object* v___x_3223_; 
lean_dec_ref(v___f_3185_);
v___x_3223_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3224_, lean_object* v___f_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3224_, v___f_3225_, v___y_3226_);
lean_dec(v___y_3226_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3229_, lean_object* v_res_3230_){
_start:
{
if (lean_obj_tag(v_res_3230_) == 0)
{
lean_dec_ref(v_ch_3229_);
goto v___jp_3232_;
}
else
{
lean_object* v_val_3234_; uint8_t v___x_3235_; 
v_val_3234_ = lean_ctor_get(v_res_3230_, 0);
v___x_3235_ = lean_unbox(v_val_3234_);
if (v___x_3235_ == 0)
{
lean_dec_ref(v_ch_3229_);
goto v___jp_3232_;
}
else
{
lean_object* v___x_3236_; 
v___x_3236_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3229_);
return v___x_3236_;
}
}
v___jp_3232_:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3237_, lean_object* v_res_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3237_, v_res_3238_);
lean_dec(v_res_3238_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3241_){
_start:
{
lean_object* v_state_3243_; lean_object* v_id_3244_; lean_object* v___f_3245_; lean_object* v___f_3246_; lean_object* v___x_3247_; 
v_state_3243_ = lean_ctor_get(v_ch_3241_, 0);
lean_inc_ref(v_state_3243_);
v_id_3244_ = lean_ctor_get(v_ch_3241_, 1);
lean_inc(v_id_3244_);
v___f_3245_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3245_, 0, v_ch_3241_);
v___f_3246_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3246_, 0, v_id_3244_);
lean_closure_set(v___f_3246_, 1, v___f_3245_);
v___x_3247_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3243_, v___f_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3248_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3251_, lean_object* v_ch_3252_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3252_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3255_, lean_object* v_ch_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3255_, v_ch_3256_);
return v_res_3258_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3259_, lean_object* v_k_3260_, lean_object* v_t_3261_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3260_, v_t_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3263_, lean_object* v_k_3264_, lean_object* v_t_3265_){
_start:
{
uint8_t v_res_3266_; lean_object* v_r_3267_; 
v_res_3266_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3263_, v_k_3264_, v_t_3265_);
lean_dec(v_t_3265_);
lean_dec(v_k_3264_);
v_r_3267_ = lean_box(v_res_3266_);
return v_r_3267_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_task_pure(v___x_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3270_, lean_object* v_ch_3271_, lean_object* v_prio_3272_, lean_object* v_x_3273_){
_start:
{
if (lean_obj_tag(v_x_3273_) == 0)
{
lean_object* v___x_3275_; 
lean_dec(v_prio_3272_);
lean_dec_ref(v_ch_3271_);
lean_dec_ref(v_f_3270_);
v___x_3275_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3275_;
}
else
{
lean_object* v_val_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_val_3276_ = lean_ctor_get(v_x_3273_, 0);
lean_inc(v_val_3276_);
lean_dec_ref_known(v_x_3273_, 1);
lean_inc_ref(v_f_3270_);
v___x_3277_ = lean_apply_2(v_f_3270_, v_val_3276_, lean_box(0));
v___x_3278_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3270_, v_ch_3271_, v_prio_3272_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3279_, lean_object* v_ch_3280_, lean_object* v_prio_3281_, lean_object* v_x_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3279_, v_ch_3280_, v_prio_3281_, v_x_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3285_, lean_object* v_ch_3286_, lean_object* v_prio_3287_){
_start:
{
lean_object* v___x_3289_; lean_object* v___f_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; 
lean_inc_ref(v_ch_3286_);
v___x_3289_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3286_);
lean_inc(v_prio_3287_);
v___f_3290_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3290_, 0, v_f_3285_);
lean_closure_set(v___f_3290_, 1, v_ch_3286_);
lean_closure_set(v___f_3290_, 2, v_prio_3287_);
v___x_3291_ = 0;
v___x_3292_ = lean_io_bind_task(v___x_3289_, v___f_3290_, v_prio_3287_, v___x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3293_, lean_object* v_ch_3294_, lean_object* v_prio_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3293_, v_ch_3294_, v_prio_3295_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3298_, lean_object* v_f_3299_, lean_object* v_ch_3300_, lean_object* v_prio_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3299_, v_ch_3300_, v_prio_3301_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3304_, lean_object* v_f_3305_, lean_object* v_ch_3306_, lean_object* v_prio_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3304_, v_f_3305_, v_ch_3306_, v_prio_3307_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3310_, lean_object* v_val_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_pos_3313_; lean_object* v_toPure_3314_; uint8_t v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_pos_3313_ = lean_ctor_get(v_a_3312_, 1);
v_toPure_3314_ = lean_ctor_get(v_toApplicative_3310_, 1);
lean_inc(v_toPure_3314_);
lean_dec_ref(v_toApplicative_3310_);
v___x_3315_ = lean_nat_dec_eq(v_pos_3313_, v_val_3311_);
v___x_3316_ = lean_box(v___x_3315_);
v___x_3317_ = lean_apply_2(v_toPure_3314_, lean_box(0), v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3318_, lean_object* v_val_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3318_, v_val_3319_, v_a_3320_);
lean_dec_ref(v_a_3320_);
lean_dec(v_val_3319_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3322_, lean_object* v_toBind_3323_, lean_object* v___f_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3326_, 0, lean_box(0));
lean_closure_set(v___x_3326_, 1, lean_box(0));
lean_closure_set(v___x_3326_, 2, v_a_3325_);
v___x_3327_ = lean_apply_2(v_inst_3322_, lean_box(0), v___x_3326_);
v___x_3328_ = lean_apply_4(v_toBind_3323_, lean_box(0), lean_box(0), v___x_3327_, v___f_3324_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3329_, lean_object* v_receiverId_3330_, lean_object* v_toApplicative_3331_, lean_object* v_inst_3332_, lean_object* v_toBind_3333_, lean_object* v_inst_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_){
_start:
{
uint8_t v_closed_3337_; 
v_closed_3337_ = lean_ctor_get_uint8(v_a_3336_, sizeof(void*)*10);
if (v_closed_3337_ == 0)
{
lean_object* v_capacity_3338_; lean_object* v_size_3339_; lean_object* v_receivers_3340_; lean_object* v___x_3341_; 
v_capacity_3338_ = lean_ctor_get(v_a_3336_, 2);
lean_inc(v_capacity_3338_);
v_size_3339_ = lean_ctor_get(v_a_3336_, 3);
lean_inc(v_size_3339_);
v_receivers_3340_ = lean_ctor_get(v_a_3336_, 7);
lean_inc(v_receivers_3340_);
lean_dec_ref(v_a_3336_);
v___x_3341_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3329_, v_receivers_3340_, v_receiverId_3330_);
if (lean_obj_tag(v___x_3341_) == 1)
{
lean_object* v_val_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v_val_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_val_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = lean_unsigned_to_nat(0u);
v___x_3344_ = lean_nat_dec_eq(v_size_3339_, v___x_3343_);
lean_dec(v_size_3339_);
if (v___x_3344_ == 0)
{
lean_object* v___f_3345_; lean_object* v___f_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
lean_inc(v_val_3342_);
v___f_3345_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3345_, 0, v_toApplicative_3331_);
lean_closure_set(v___f_3345_, 1, v_val_3342_);
lean_inc(v_toBind_3333_);
lean_inc(v_inst_3332_);
v___f_3346_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3346_, 0, v_inst_3332_);
lean_closure_set(v___f_3346_, 1, v_toBind_3333_);
lean_closure_set(v___f_3346_, 2, v___f_3345_);
v___x_3347_ = lean_nat_mod(v_val_3342_, v_capacity_3338_);
lean_dec(v_capacity_3338_);
lean_dec(v_val_3342_);
v___x_3348_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3334_, v_inst_3332_, v___x_3347_, v_a_3335_);
v___x_3349_ = lean_apply_4(v_toBind_3333_, lean_box(0), lean_box(0), v___x_3348_, v___f_3346_);
return v___x_3349_;
}
else
{
lean_object* v_toPure_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_dec(v_val_3342_);
lean_dec(v_capacity_3338_);
lean_dec_ref(v_inst_3334_);
lean_dec(v_toBind_3333_);
lean_dec(v_inst_3332_);
v_toPure_3350_ = lean_ctor_get(v_toApplicative_3331_, 1);
lean_inc(v_toPure_3350_);
lean_dec_ref(v_toApplicative_3331_);
v___x_3351_ = lean_box(v_closed_3337_);
v___x_3352_ = lean_apply_2(v_toPure_3350_, lean_box(0), v___x_3351_);
return v___x_3352_;
}
}
else
{
lean_object* v_toPure_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec(v___x_3341_);
lean_dec(v_size_3339_);
lean_dec(v_capacity_3338_);
lean_dec_ref(v_inst_3334_);
lean_dec(v_toBind_3333_);
lean_dec(v_inst_3332_);
v_toPure_3353_ = lean_ctor_get(v_toApplicative_3331_, 1);
lean_inc(v_toPure_3353_);
lean_dec_ref(v_toApplicative_3331_);
v___x_3354_ = lean_box(v_closed_3337_);
v___x_3355_ = lean_apply_2(v_toPure_3353_, lean_box(0), v___x_3354_);
return v___x_3355_;
}
}
else
{
lean_object* v_toPure_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref(v_a_3336_);
lean_dec_ref(v_inst_3334_);
lean_dec(v_toBind_3333_);
lean_dec(v_inst_3332_);
lean_dec(v_receiverId_3330_);
lean_dec_ref(v___f_3329_);
v_toPure_3356_ = lean_ctor_get(v_toApplicative_3331_, 1);
lean_inc(v_toPure_3356_);
lean_dec_ref(v_toApplicative_3331_);
v___x_3357_ = lean_box(v_closed_3337_);
v___x_3358_ = lean_apply_2(v_toPure_3356_, lean_box(0), v___x_3357_);
return v___x_3358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object* v___f_3359_, lean_object* v_receiverId_3360_, lean_object* v_toApplicative_3361_, lean_object* v_inst_3362_, lean_object* v_toBind_3363_, lean_object* v_inst_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(v___f_3359_, v_receiverId_3360_, v_toApplicative_3361_, v_inst_3362_, v_toBind_3363_, v_inst_3364_, v_a_3365_, v_a_3366_);
lean_dec(v_a_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3368_, lean_object* v_inst_3369_, lean_object* v_receiverId_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_toApplicative_3372_; lean_object* v_toBind_3373_; lean_object* v___f_3374_; lean_object* v___f_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_toApplicative_3372_ = lean_ctor_get(v_inst_3368_, 0);
lean_inc_ref(v_toApplicative_3372_);
v_toBind_3373_ = lean_ctor_get(v_inst_3368_, 1);
lean_inc_n(v_toBind_3373_, 2);
v___f_3374_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3371_, 2);
lean_inc(v_inst_3369_);
v___f_3375_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3375_, 0, v___f_3374_);
lean_closure_set(v___f_3375_, 1, v_receiverId_3370_);
lean_closure_set(v___f_3375_, 2, v_toApplicative_3372_);
lean_closure_set(v___f_3375_, 3, v_inst_3369_);
lean_closure_set(v___f_3375_, 4, v_toBind_3373_);
lean_closure_set(v___f_3375_, 5, v_inst_3368_);
lean_closure_set(v___f_3375_, 6, v_a_3371_);
v___x_3376_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3376_, 0, lean_box(0));
lean_closure_set(v___x_3376_, 1, lean_box(0));
lean_closure_set(v___x_3376_, 2, v_a_3371_);
v___x_3377_ = lean_apply_2(v_inst_3369_, lean_box(0), v___x_3376_);
v___x_3378_ = lean_apply_4(v_toBind_3373_, lean_box(0), lean_box(0), v___x_3377_, v___f_3375_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object* v_inst_3379_, lean_object* v_inst_3380_, lean_object* v_receiverId_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(v_inst_3379_, v_inst_3380_, v_receiverId_3381_, v_a_3382_);
lean_dec(v_a_3382_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3384_, lean_object* v_00_u03b1_3385_, lean_object* v_inst_3386_, lean_object* v_inst_3387_, lean_object* v_inst_3388_, lean_object* v_inst_3389_, lean_object* v_receiverId_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_toApplicative_3392_; lean_object* v_toBind_3393_; lean_object* v___f_3394_; lean_object* v___f_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_toApplicative_3392_ = lean_ctor_get(v_inst_3386_, 0);
lean_inc_ref(v_toApplicative_3392_);
v_toBind_3393_ = lean_ctor_get(v_inst_3386_, 1);
lean_inc_n(v_toBind_3393_, 2);
v___f_3394_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3391_, 2);
lean_inc(v_inst_3387_);
v___f_3395_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3395_, 0, v___f_3394_);
lean_closure_set(v___f_3395_, 1, v_receiverId_3390_);
lean_closure_set(v___f_3395_, 2, v_toApplicative_3392_);
lean_closure_set(v___f_3395_, 3, v_inst_3387_);
lean_closure_set(v___f_3395_, 4, v_toBind_3393_);
lean_closure_set(v___f_3395_, 5, v_inst_3386_);
lean_closure_set(v___f_3395_, 6, v_a_3391_);
v___x_3396_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3396_, 0, lean_box(0));
lean_closure_set(v___x_3396_, 1, lean_box(0));
lean_closure_set(v___x_3396_, 2, v_a_3391_);
v___x_3397_ = lean_apply_2(v_inst_3387_, lean_box(0), v___x_3396_);
v___x_3398_ = lean_apply_4(v_toBind_3393_, lean_box(0), lean_box(0), v___x_3397_, v___f_3395_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3399_, lean_object* v_00_u03b1_3400_, lean_object* v_inst_3401_, lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_receiverId_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3399_, v_00_u03b1_3400_, v_inst_3401_, v_inst_3402_, v_inst_3403_, v_inst_3404_, v_receiverId_3405_, v_a_3406_);
lean_dec(v_a_3406_);
lean_dec(v_inst_3404_);
lean_dec(v_inst_3403_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3410_, lean_object* v_lose_3411_){
_start:
{
lean_object* v_finished_3413_; lean_object* v_promise_3414_; lean_object* v___x_3415_; uint8_t v___y_3417_; uint8_t v___x_3425_; 
v_finished_3413_ = lean_ctor_get(v_w_3410_, 0);
v_promise_3414_ = lean_ctor_get(v_w_3410_, 1);
v___x_3415_ = lean_st_ref_take(v_finished_3413_);
v___x_3425_ = lean_unbox(v___x_3415_);
lean_dec(v___x_3415_);
if (v___x_3425_ == 0)
{
uint8_t v___x_3426_; 
v___x_3426_ = 1;
v___y_3417_ = v___x_3426_;
goto v___jp_3416_;
}
else
{
uint8_t v___x_3427_; 
v___x_3427_ = 0;
v___y_3417_ = v___x_3427_;
goto v___jp_3416_;
}
v___jp_3416_:
{
uint8_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = 1;
v___x_3419_ = lean_box(v___x_3418_);
v___x_3420_ = lean_st_ref_put(v_finished_3413_, v___x_3419_);
if (v___y_3417_ == 0)
{
lean_object* v___x_3421_; 
v___x_3421_ = lean_apply_1(v_lose_3411_, lean_box(0));
return v___x_3421_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec_ref(v_lose_3411_);
v___x_3422_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3423_ = lean_io_promise_resolve(v___x_3422_, v_promise_3414_);
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3428_, lean_object* v_lose_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3428_, v_lose_3429_);
lean_dec_ref(v_w_3428_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3432_, lean_object* v_w_3433_, lean_object* v_lose_3434_){
_start:
{
lean_object* v___x_3436_; 
v___x_3436_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3433_, v_lose_3434_);
return v___x_3436_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3437_, lean_object* v_w_3438_, lean_object* v_lose_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3437_, v_w_3438_, v_lose_3439_);
lean_dec_ref(v_w_3438_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v___x_3445_; lean_object* v_receivers_3446_; lean_object* v___x_3447_; 
v___x_3445_ = lean_st_ref_get(v_a_3443_);
v_receivers_3446_ = lean_ctor_get(v___x_3445_, 7);
lean_inc(v_receivers_3446_);
lean_dec(v___x_3445_);
v___x_3447_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3446_, v_receiverId_3442_);
if (lean_obj_tag(v___x_3447_) == 1)
{
lean_object* v_val_3448_; lean_object* v___x_3449_; 
v_val_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_val_3448_);
lean_dec_ref_known(v___x_3447_, 1);
v___x_3449_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3448_, v_a_3443_);
lean_dec(v_val_3448_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3482_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3482_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3482_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
if (lean_obj_tag(v_a_3450_) == 1)
{
lean_object* v___x_3454_; lean_object* v_producers_3455_; lean_object* v_waiters_3456_; lean_object* v_capacity_3457_; lean_object* v_size_3458_; lean_object* v_buffer_3459_; lean_object* v_write_3460_; lean_object* v_read_3461_; lean_object* v_nextId_3462_; uint8_t v_closed_3463_; lean_object* v_pos_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3476_; 
v___x_3454_ = lean_st_ref_take(v_a_3443_);
v_producers_3455_ = lean_ctor_get(v___x_3454_, 0);
v_waiters_3456_ = lean_ctor_get(v___x_3454_, 1);
v_capacity_3457_ = lean_ctor_get(v___x_3454_, 2);
v_size_3458_ = lean_ctor_get(v___x_3454_, 3);
v_buffer_3459_ = lean_ctor_get(v___x_3454_, 4);
v_write_3460_ = lean_ctor_get(v___x_3454_, 5);
v_read_3461_ = lean_ctor_get(v___x_3454_, 6);
v_nextId_3462_ = lean_ctor_get(v___x_3454_, 8);
v_closed_3463_ = lean_ctor_get_uint8(v___x_3454_, sizeof(void*)*10);
v_pos_3464_ = lean_ctor_get(v___x_3454_, 9);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v___x_3454_, 7);
lean_dec(v_unused_3477_);
v___x_3466_ = v___x_3454_;
v_isShared_3467_ = v_isSharedCheck_3476_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_pos_3464_);
lean_inc(v_nextId_3462_);
lean_inc(v_read_3461_);
lean_inc(v_write_3460_);
lean_inc(v_buffer_3459_);
lean_inc(v_size_3458_);
lean_inc(v_capacity_3457_);
lean_inc(v_waiters_3456_);
lean_inc(v_producers_3455_);
lean_dec(v___x_3454_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3476_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3468_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3442_, v_receivers_3446_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 7, v___x_3468_);
v___x_3470_ = v___x_3466_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_producers_3455_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_waiters_3456_);
lean_ctor_set(v_reuseFailAlloc_3475_, 2, v_capacity_3457_);
lean_ctor_set(v_reuseFailAlloc_3475_, 3, v_size_3458_);
lean_ctor_set(v_reuseFailAlloc_3475_, 4, v_buffer_3459_);
lean_ctor_set(v_reuseFailAlloc_3475_, 5, v_write_3460_);
lean_ctor_set(v_reuseFailAlloc_3475_, 6, v_read_3461_);
lean_ctor_set(v_reuseFailAlloc_3475_, 7, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3475_, 8, v_nextId_3462_);
lean_ctor_set(v_reuseFailAlloc_3475_, 9, v_pos_3464_);
lean_ctor_set_uint8(v_reuseFailAlloc_3475_, sizeof(void*)*10, v_closed_3463_);
v___x_3470_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_st_ref_put(v_a_3443_, v___x_3470_);
if (v_isShared_3453_ == 0)
{
v___x_3473_ = v___x_3452_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3450_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3480_; 
lean_dec(v_a_3450_);
lean_dec(v_receivers_3446_);
lean_dec(v_receiverId_3442_);
v___x_3478_ = lean_box(0);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3478_);
v___x_3480_ = v___x_3452_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_dec(v_receivers_3446_);
lean_dec(v_receiverId_3442_);
return v___x_3449_;
}
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_dec(v___x_3447_);
lean_dec(v_receivers_3446_);
lean_dec(v_receiverId_3442_);
v___x_3483_ = lean_box(0);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
return v___x_3484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3485_, lean_object* v_a_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3485_, v_a_3486_);
lean_dec(v_a_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3489_, lean_object* v_w_3490_, lean_object* v_lose_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v_finished_3494_; lean_object* v_promise_3495_; lean_object* v___x_3496_; uint8_t v___y_3498_; uint8_t v___x_3522_; 
v_finished_3494_ = lean_ctor_get(v_w_3490_, 0);
v_promise_3495_ = lean_ctor_get(v_w_3490_, 1);
v___x_3496_ = lean_st_ref_take(v_finished_3494_);
v___x_3522_ = lean_unbox(v___x_3496_);
lean_dec(v___x_3496_);
if (v___x_3522_ == 0)
{
uint8_t v___x_3523_; 
v___x_3523_ = 1;
v___y_3498_ = v___x_3523_;
goto v___jp_3497_;
}
else
{
uint8_t v___x_3524_; 
v___x_3524_ = 0;
v___y_3498_ = v___x_3524_;
goto v___jp_3497_;
}
v___jp_3497_:
{
uint8_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = 1;
v___x_3500_ = lean_box(v___x_3499_);
v___x_3501_ = lean_st_ref_put(v_finished_3494_, v___x_3500_);
if (v___y_3498_ == 0)
{
lean_object* v___x_3502_; 
lean_dec(v___x_3489_);
lean_inc(v___y_3492_);
v___x_3502_ = lean_apply_2(v_lose_3491_, v___y_3492_, lean_box(0));
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; 
lean_dec_ref(v_lose_3491_);
v___x_3503_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3489_, v___y_3492_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3513_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3506_ = v___x_3503_;
v_isShared_3507_ = v_isSharedCheck_3513_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3503_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3513_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_a_3504_);
v___x_3509_ = lean_io_promise_resolve(v___x_3508_, v_promise_3495_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3509_);
v___x_3511_ = v___x_3506_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
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
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
v_a_3514_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3503_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3503_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3525_, lean_object* v_w_3526_, lean_object* v_lose_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3525_, v_w_3526_, v_lose_3527_, v___y_3528_);
lean_dec(v___y_3528_);
lean_dec_ref(v_w_3526_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3531_, lean_object* v___x_3532_, lean_object* v_w_3533_, lean_object* v_lose_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3532_, v_w_3533_, v_lose_3534_, v___y_3535_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3538_, lean_object* v___x_3539_, lean_object* v_w_3540_, lean_object* v_lose_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3538_, v___x_3539_, v_w_3540_, v_lose_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v_w_3540_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3545_){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3548_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3551_, lean_object* v___f_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___x_3555_; uint8_t v_closed_3556_; 
v___x_3555_ = lean_st_ref_get(v___y_3553_);
v_closed_3556_ = lean_ctor_get_uint8(v___x_3555_, sizeof(void*)*10);
if (v_closed_3556_ == 0)
{
lean_object* v_capacity_3557_; lean_object* v_size_3558_; lean_object* v_receivers_3559_; lean_object* v___x_3560_; 
v_capacity_3557_ = lean_ctor_get(v___x_3555_, 2);
lean_inc(v_capacity_3557_);
v_size_3558_ = lean_ctor_get(v___x_3555_, 3);
lean_inc(v_size_3558_);
v_receivers_3559_ = lean_ctor_get(v___x_3555_, 7);
lean_inc(v_receivers_3559_);
lean_dec(v___x_3555_);
v___x_3560_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3559_, v_id_3551_);
lean_dec(v_receivers_3559_);
if (lean_obj_tag(v___x_3560_) == 1)
{
lean_object* v_val_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v_val_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_val_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = lean_unsigned_to_nat(0u);
v___x_3563_ = lean_nat_dec_eq(v_size_3558_, v___x_3562_);
lean_dec(v_size_3558_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_nat_mod(v_val_3561_, v_capacity_3557_);
lean_dec(v_capacity_3557_);
v___x_3565_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3564_, v___y_3553_);
lean_dec(v___x_3564_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3567_; lean_object* v_pos_3568_; uint8_t v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v___x_3567_ = lean_st_ref_get(v_a_3566_);
lean_dec(v_a_3566_);
v_pos_3568_ = lean_ctor_get(v___x_3567_, 1);
lean_inc(v_pos_3568_);
lean_dec(v___x_3567_);
v___x_3569_ = lean_nat_dec_eq(v_pos_3568_, v_val_3561_);
lean_dec(v_val_3561_);
lean_dec(v_pos_3568_);
v___x_3570_ = lean_box(v___x_3569_);
lean_inc(v___y_3553_);
v___x_3571_ = lean_apply_3(v___f_3552_, v___x_3570_, v___y_3553_, lean_box(0));
return v___x_3571_;
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v_val_3561_);
lean_dec_ref(v___f_3552_);
v_a_3572_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3565_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3565_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
lean_dec(v_val_3561_);
lean_dec(v_capacity_3557_);
v___x_3580_ = lean_box(v_closed_3556_);
lean_inc(v___y_3553_);
v___x_3581_ = lean_apply_3(v___f_3552_, v___x_3580_, v___y_3553_, lean_box(0));
return v___x_3581_;
}
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec(v___x_3560_);
lean_dec(v_size_3558_);
lean_dec(v_capacity_3557_);
v___x_3582_ = lean_box(v_closed_3556_);
lean_inc(v___y_3553_);
v___x_3583_ = lean_apply_3(v___f_3552_, v___x_3582_, v___y_3553_, lean_box(0));
return v___x_3583_;
}
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
lean_dec(v___x_3555_);
v___x_3584_ = lean_box(v_closed_3556_);
lean_inc(v___y_3553_);
v___x_3585_ = lean_apply_3(v___f_3552_, v___x_3584_, v___y_3553_, lean_box(0));
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3586_, lean_object* v___f_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3586_, v___f_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec(v_id_3586_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; lean_object* v_producers_3595_; lean_object* v_waiters_3596_; lean_object* v_capacity_3597_; lean_object* v_size_3598_; lean_object* v_buffer_3599_; lean_object* v_write_3600_; lean_object* v_read_3601_; lean_object* v_receivers_3602_; lean_object* v_nextId_3603_; uint8_t v_closed_3604_; lean_object* v_pos_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3628_; 
v___x_3594_ = lean_st_ref_get(v___y_3592_);
v_producers_3595_ = lean_ctor_get(v___x_3594_, 0);
v_waiters_3596_ = lean_ctor_get(v___x_3594_, 1);
v_capacity_3597_ = lean_ctor_get(v___x_3594_, 2);
v_size_3598_ = lean_ctor_get(v___x_3594_, 3);
v_buffer_3599_ = lean_ctor_get(v___x_3594_, 4);
v_write_3600_ = lean_ctor_get(v___x_3594_, 5);
v_read_3601_ = lean_ctor_get(v___x_3594_, 6);
v_receivers_3602_ = lean_ctor_get(v___x_3594_, 7);
v_nextId_3603_ = lean_ctor_get(v___x_3594_, 8);
v_closed_3604_ = lean_ctor_get_uint8(v___x_3594_, sizeof(void*)*10);
v_pos_3605_ = lean_ctor_get(v___x_3594_, 9);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3607_ = v___x_3594_;
v_isShared_3608_ = v_isSharedCheck_3628_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_pos_3605_);
lean_inc(v_nextId_3603_);
lean_inc(v_receivers_3602_);
lean_inc(v_read_3601_);
lean_inc(v_write_3600_);
lean_inc(v_buffer_3599_);
lean_inc(v_size_3598_);
lean_inc(v_capacity_3597_);
lean_inc(v_waiters_3596_);
lean_inc(v_producers_3595_);
lean_dec(v___x_3594_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3628_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; 
v___x_3609_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3596_);
if (lean_obj_tag(v___x_3609_) == 1)
{
lean_object* v_val_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3625_; 
v_val_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3625_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_val_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3625_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v_fst_3614_; lean_object* v_snd_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v_fst_3614_ = lean_ctor_get(v_val_3610_, 0);
lean_inc(v_fst_3614_);
v_snd_3615_ = lean_ctor_get(v_val_3610_, 1);
lean_inc(v_snd_3615_);
lean_dec(v_val_3610_);
v___x_3616_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3614_, v_____do__lift_3591_);
lean_dec(v_fst_3614_);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 1, v_snd_3615_);
v___x_3618_ = v___x_3607_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_producers_3595_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_snd_3615_);
lean_ctor_set(v_reuseFailAlloc_3624_, 2, v_capacity_3597_);
lean_ctor_set(v_reuseFailAlloc_3624_, 3, v_size_3598_);
lean_ctor_set(v_reuseFailAlloc_3624_, 4, v_buffer_3599_);
lean_ctor_set(v_reuseFailAlloc_3624_, 5, v_write_3600_);
lean_ctor_set(v_reuseFailAlloc_3624_, 6, v_read_3601_);
lean_ctor_set(v_reuseFailAlloc_3624_, 7, v_receivers_3602_);
lean_ctor_set(v_reuseFailAlloc_3624_, 8, v_nextId_3603_);
lean_ctor_set(v_reuseFailAlloc_3624_, 9, v_pos_3605_);
lean_ctor_set_uint8(v_reuseFailAlloc_3624_, sizeof(void*)*10, v_closed_3604_);
v___x_3618_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3622_; 
v___x_3619_ = lean_st_ref_swap(v___y_3592_, v___x_3618_);
lean_dec(v___x_3619_);
v___x_3620_ = lean_box(0);
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3620_);
v___x_3622_ = v___x_3612_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_dec(v___x_3609_);
lean_del_object(v___x_3607_);
lean_dec(v_pos_3605_);
lean_dec(v_nextId_3603_);
lean_dec(v_receivers_3602_);
lean_dec(v_read_3601_);
lean_dec(v_write_3600_);
lean_dec_ref(v_buffer_3599_);
lean_dec(v_size_3598_);
lean_dec(v_capacity_3597_);
lean_dec_ref(v_producers_3595_);
v___x_3626_ = lean_box(0);
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
return v___x_3627_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
uint8_t v_____do__lift_4183__boxed_3632_; lean_object* v_res_3633_; 
v_____do__lift_4183__boxed_3632_ = lean_unbox(v_____do__lift_3629_);
v_res_3633_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_4183__boxed_3632_, v___y_3630_);
lean_dec(v___y_3630_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3634_, lean_object* v___f_3635_, lean_object* v_id_3636_, uint8_t v_____do__lift_3637_, lean_object* v___y_3638_){
_start:
{
if (v_____do__lift_3637_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v_producers_3642_; lean_object* v_waiters_3643_; lean_object* v_capacity_3644_; lean_object* v_size_3645_; lean_object* v_buffer_3646_; lean_object* v_write_3647_; lean_object* v_read_3648_; lean_object* v_receivers_3649_; lean_object* v_nextId_3650_; uint8_t v_closed_3651_; lean_object* v_pos_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3666_; 
lean_dec(v_id_3636_);
v___x_3640_ = lean_io_promise_new();
v___x_3641_ = lean_st_ref_take(v___y_3638_);
v_producers_3642_ = lean_ctor_get(v___x_3641_, 0);
v_waiters_3643_ = lean_ctor_get(v___x_3641_, 1);
v_capacity_3644_ = lean_ctor_get(v___x_3641_, 2);
v_size_3645_ = lean_ctor_get(v___x_3641_, 3);
v_buffer_3646_ = lean_ctor_get(v___x_3641_, 4);
v_write_3647_ = lean_ctor_get(v___x_3641_, 5);
v_read_3648_ = lean_ctor_get(v___x_3641_, 6);
v_receivers_3649_ = lean_ctor_get(v___x_3641_, 7);
v_nextId_3650_ = lean_ctor_get(v___x_3641_, 8);
v_closed_3651_ = lean_ctor_get_uint8(v___x_3641_, sizeof(void*)*10);
v_pos_3652_ = lean_ctor_get(v___x_3641_, 9);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3654_ = v___x_3641_;
v_isShared_3655_ = v_isSharedCheck_3666_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_pos_3652_);
lean_inc(v_nextId_3650_);
lean_inc(v_receivers_3649_);
lean_inc(v_read_3648_);
lean_inc(v_write_3647_);
lean_inc(v_buffer_3646_);
lean_inc(v_size_3645_);
lean_inc(v_capacity_3644_);
lean_inc(v_waiters_3643_);
lean_inc(v_producers_3642_);
lean_dec(v___x_3641_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3666_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_waiter_3634_);
lean_inc(v___x_3640_);
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3640_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_Std_Queue_enqueue___redArg(v___x_3657_, v_waiters_3643_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 1, v___x_3658_);
v___x_3660_ = v___x_3654_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_producers_3642_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3665_, 2, v_capacity_3644_);
lean_ctor_set(v_reuseFailAlloc_3665_, 3, v_size_3645_);
lean_ctor_set(v_reuseFailAlloc_3665_, 4, v_buffer_3646_);
lean_ctor_set(v_reuseFailAlloc_3665_, 5, v_write_3647_);
lean_ctor_set(v_reuseFailAlloc_3665_, 6, v_read_3648_);
lean_ctor_set(v_reuseFailAlloc_3665_, 7, v_receivers_3649_);
lean_ctor_set(v_reuseFailAlloc_3665_, 8, v_nextId_3650_);
lean_ctor_set(v_reuseFailAlloc_3665_, 9, v_pos_3652_);
lean_ctor_set_uint8(v_reuseFailAlloc_3665_, sizeof(void*)*10, v_closed_3651_);
v___x_3660_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3661_ = lean_st_ref_put(v___y_3638_, v___x_3660_);
v___x_3662_ = lean_io_promise_result_opt(v___x_3640_);
lean_dec(v___x_3640_);
v___x_3663_ = lean_unsigned_to_nat(0u);
v___x_3664_ = l_EIO_chainTask___redArg(v___x_3662_, v___f_3635_, v___x_3663_, v_____do__lift_3637_);
return v___x_3664_;
}
}
}
else
{
lean_object* v___x_3667_; lean_object* v_lose_3668_; lean_object* v___x_3669_; 
lean_dec_ref(v___f_3635_);
v___x_3667_ = lean_box(v_____do__lift_3637_);
v_lose_3668_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3668_, 0, v___x_3667_);
v___x_3669_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3636_, v_waiter_3634_, v_lose_3668_, v___y_3638_);
lean_dec_ref(v_waiter_3634_);
return v___x_3669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3670_, lean_object* v___f_3671_, lean_object* v_id_3672_, lean_object* v_____do__lift_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
uint8_t v_____do__lift_4241__boxed_3676_; lean_object* v_res_3677_; 
v_____do__lift_4241__boxed_3676_ = lean_unbox(v_____do__lift_3673_);
v_res_3677_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3670_, v___f_3671_, v_id_3672_, v_____do__lift_4241__boxed_3676_, v___y_3674_);
lean_dec(v___y_3674_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3680_, lean_object* v_ch_3681_, lean_object* v_res_x3f_3682_){
_start:
{
if (lean_obj_tag(v_res_x3f_3682_) == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_dec_ref(v_ch_3681_);
lean_dec_ref(v_waiter_3680_);
v___x_3684_ = lean_box(0);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
return v___x_3685_;
}
else
{
lean_object* v_val_3686_; uint8_t v___x_3687_; 
v_val_3686_ = lean_ctor_get(v_res_x3f_3682_, 0);
v___x_3687_ = lean_unbox(v_val_3686_);
if (v___x_3687_ == 0)
{
lean_object* v___f_3688_; lean_object* v___x_3689_; 
lean_dec_ref(v_ch_3681_);
v___f_3688_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3689_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3680_, v___f_3688_);
lean_dec_ref(v_waiter_3680_);
return v___x_3689_;
}
else
{
lean_object* v___x_3690_; 
v___x_3690_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3681_, v_waiter_3680_);
return v___x_3690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3691_, lean_object* v_ch_3692_, lean_object* v_res_x3f_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3691_, v_ch_3692_, v_res_x3f_3693_);
lean_dec(v_res_x3f_3693_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3696_, lean_object* v_waiter_3697_){
_start:
{
lean_object* v_state_3699_; lean_object* v_id_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___f_3703_; lean_object* v___x_3704_; 
v_state_3699_ = lean_ctor_get(v_ch_3696_, 0);
lean_inc_ref(v_state_3699_);
v_id_3700_ = lean_ctor_get(v_ch_3696_, 1);
lean_inc_n(v_id_3700_, 2);
lean_inc_ref(v_waiter_3697_);
v___f_3701_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3701_, 0, v_waiter_3697_);
lean_closure_set(v___f_3701_, 1, v_ch_3696_);
v___f_3702_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3702_, 0, v_waiter_3697_);
lean_closure_set(v___f_3702_, 1, v___f_3701_);
lean_closure_set(v___f_3702_, 2, v_id_3700_);
v___f_3703_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3703_, 0, v_id_3700_);
lean_closure_set(v___f_3703_, 1, v___f_3702_);
v___x_3704_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3699_, v___f_3703_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3705_, lean_object* v_waiter_3706_, lean_object* v_a_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3705_, v_waiter_3706_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3709_, lean_object* v_ch_3710_, lean_object* v_waiter_3711_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3710_, v_waiter_3711_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3714_, lean_object* v_ch_3715_, lean_object* v_waiter_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3714_, v_ch_3715_, v_waiter_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3719_, lean_object* v_receiverId_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3720_, v_a_3721_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3724_, lean_object* v_receiverId_3725_, lean_object* v_a_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3724_, v_receiverId_3725_, v_a_3726_);
lean_dec(v_a_3726_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3729_, lean_object* v_x_3730_){
_start:
{
if (lean_obj_tag(v_x_3730_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3740_; 
v_a_3732_ = lean_ctor_get(v_x_3730_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_x_3730_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3734_ = v_x_3730_;
v_isShared_3735_ = v_isSharedCheck_3740_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v_x_3730_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3740_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
return v___x_3738_;
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3753_; 
v_a_3741_ = lean_ctor_get(v_x_3730_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_x_3730_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3743_ = v_x_3730_;
v_isShared_3744_ = v_isSharedCheck_3753_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v_x_3730_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3753_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v_capacity_3745_; lean_object* v_buffer_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3750_; 
v_capacity_3745_ = lean_ctor_get(v_a_3741_, 2);
lean_inc(v_capacity_3745_);
v_buffer_3746_ = lean_ctor_get(v_a_3741_, 4);
lean_inc_ref(v_buffer_3746_);
lean_dec(v_a_3741_);
v___x_3747_ = lean_nat_mod(v_place_3729_, v_capacity_3745_);
lean_dec(v_capacity_3745_);
v___x_3748_ = lean_array_fget(v_buffer_3746_, v___x_3747_);
lean_dec(v___x_3747_);
lean_dec_ref(v_buffer_3746_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3748_);
v___x_3750_ = v___x_3743_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3751_; 
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
return v___x_3751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3754_, lean_object* v_x_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3754_, v_x_3755_);
lean_dec(v_place_3754_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v___f_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; lean_object* v___x_3767_; 
v___x_3761_ = lean_st_ref_get(v_a_3759_);
v___f_3762_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3762_, 0, v_place_3758_);
v___x_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
v___x_3765_ = lean_unsigned_to_nat(0u);
v___x_3766_ = 0;
v___x_3767_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3765_, v___x_3766_, v___x_3764_, v___f_3762_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3768_, lean_object* v_a_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3768_, v_a_3769_);
lean_dec(v_a_3769_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3772_, lean_object* v_place_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3773_, v_a_3774_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3777_, lean_object* v_place_3778_, lean_object* v_a_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3777_, v_place_3778_, v_a_3779_);
lean_dec(v_a_3779_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_3782_, lean_object* v_x_3783_){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = lean_io_basemutex_unlock(v_mutex_3782_);
v___x_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3785_);
v___x_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_3788_, lean_object* v_x_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(v_mutex_3788_, v_x_3789_);
lean_dec(v_x_3789_);
lean_dec(v_mutex_3788_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_3792_, lean_object* v_ref_3793_, lean_object* v_x_3794_){
_start:
{
if (lean_obj_tag(v_x_3794_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_ref_3793_);
lean_dec_ref(v_k_3792_);
v_a_3796_ = lean_ctor_get(v_x_3794_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_x_3794_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3798_ = v_x_3794_;
v_isShared_3799_ = v_isSharedCheck_3804_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v_x_3794_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3804_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3801_);
return v___x_3802_;
}
}
}
else
{
lean_object* v___x_3805_; 
lean_dec_ref_known(v_x_3794_, 1);
v___x_3805_ = lean_apply_2(v_k_3792_, v_ref_3793_, lean_box(0));
return v___x_3805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_3806_, lean_object* v_ref_3807_, lean_object* v_x_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_k_3806_, v_ref_3807_, v_x_3808_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_3811_, lean_object* v___f_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; 
v___x_3814_ = lean_io_basemutex_lock(v_mutex_3811_);
v___x_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
v___x_3817_ = lean_unsigned_to_nat(0u);
v___x_3818_ = 0;
v___x_3819_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3817_, v___x_3818_, v___x_3816_, v___f_3812_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_3820_, lean_object* v___f_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_mutex_3820_, v___f_3821_);
lean_dec(v_mutex_3820_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_3824_){
_start:
{
if (lean_obj_tag(v___y_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___y_3824_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___y_3824_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___y_3824_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___y_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3841_; 
v_a_3833_ = lean_ctor_get(v___y_3824_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___y_3824_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3835_ = v___y_3824_;
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___y_3824_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v_fst_3837_; lean_object* v___x_3839_; 
v_fst_3837_ = lean_ctor_get(v_a_3833_, 0);
lean_inc(v_fst_3837_);
lean_dec(v_a_3833_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v_fst_3837_);
v___x_3839_ = v___x_3835_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_fst_3837_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_3843_, lean_object* v_k_3844_){
_start:
{
lean_object* v_ref_3846_; lean_object* v_mutex_3847_; lean_object* v___f_3848_; lean_object* v___f_3849_; lean_object* v___f_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; lean_object* v___x_3853_; lean_object* v___y_3855_; 
v_ref_3846_ = lean_ctor_get(v_mutex_3843_, 0);
lean_inc(v_ref_3846_);
v_mutex_3847_ = lean_ctor_get(v_mutex_3843_, 1);
lean_inc_n(v_mutex_3847_, 2);
lean_dec_ref(v_mutex_3843_);
v___f_3848_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3848_, 0, v_mutex_3847_);
v___f_3849_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3849_, 0, v_k_3844_);
lean_closure_set(v___f_3849_, 1, v_ref_3846_);
v___f_3850_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3850_, 0, v_mutex_3847_);
lean_closure_set(v___f_3850_, 1, v___f_3849_);
v___x_3851_ = lean_unsigned_to_nat(0u);
v___x_3852_ = 0;
v___x_3853_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_3850_, v___f_3848_, v___x_3851_, v___x_3852_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3857_; 
v_a_3857_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3853_, 1);
if (lean_obj_tag(v_a_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
v_a_3858_ = lean_ctor_get(v_a_3857_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_a_3857_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v_a_3857_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v_a_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
v___y_3855_ = v___x_3863_;
goto v___jp_3854_;
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3874_; 
v_a_3866_ = lean_ctor_get(v_a_3857_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_a_3857_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3868_ = v_a_3857_;
v_isShared_3869_ = v_isSharedCheck_3874_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v_a_3857_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3874_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v_fst_3870_; lean_object* v___x_3872_; 
v_fst_3870_ = lean_ctor_get(v_a_3866_, 0);
lean_inc(v_fst_3870_);
lean_dec(v_a_3866_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v_fst_3870_);
v___x_3872_ = v___x_3868_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_fst_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
v___y_3855_ = v___x_3872_;
goto v___jp_3854_;
}
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3884_; 
v_a_3875_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3877_ = v___x_3853_;
v_isShared_3878_ = v_isSharedCheck_3884_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3853_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3884_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___f_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
v___f_3879_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___x_3880_ = lean_task_map(v___f_3879_, v_a_3875_, v___x_3851_, v___x_3852_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 0, v___x_3880_);
v___x_3882_ = v___x_3877_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
v___jp_3854_:
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3856_, 0, v___y_3855_);
return v___x_3856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_3885_, lean_object* v_k_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3885_, v_k_3886_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_3889_, lean_object* v_00_u03b2_3890_, lean_object* v_mutex_3891_, lean_object* v_k_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3891_, v_k_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_3895_, lean_object* v_00_u03b2_3896_, lean_object* v_mutex_3897_, lean_object* v_k_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_3895_, v_00_u03b2_3896_, v_mutex_3897_, v_k_3898_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_3905_, lean_object* v_capacity_3906_, lean_object* v_size_3907_, lean_object* v_buffer_3908_, lean_object* v_write_3909_, lean_object* v_read_3910_, lean_object* v_receivers_3911_, lean_object* v_nextId_3912_, uint8_t v_closed_3913_, lean_object* v_pos_3914_, lean_object* v___y_3915_, lean_object* v_x_3916_){
_start:
{
if (lean_obj_tag(v_x_3916_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3926_; 
lean_dec(v_pos_3914_);
lean_dec(v_nextId_3912_);
lean_dec(v_receivers_3911_);
lean_dec(v_read_3910_);
lean_dec(v_write_3909_);
lean_dec_ref(v_buffer_3908_);
lean_dec(v_size_3907_);
lean_dec(v_capacity_3906_);
lean_dec_ref(v_producers_3905_);
v_a_3918_ = lean_ctor_get(v_x_3916_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_x_3916_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3920_ = v_x_3916_;
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v_x_3916_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3926_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3924_; 
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_a_3927_ = lean_ctor_get(v_x_3916_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v_x_3916_, 1);
v___x_3928_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3928_, 0, v_producers_3905_);
lean_ctor_set(v___x_3928_, 1, v_a_3927_);
lean_ctor_set(v___x_3928_, 2, v_capacity_3906_);
lean_ctor_set(v___x_3928_, 3, v_size_3907_);
lean_ctor_set(v___x_3928_, 4, v_buffer_3908_);
lean_ctor_set(v___x_3928_, 5, v_write_3909_);
lean_ctor_set(v___x_3928_, 6, v_read_3910_);
lean_ctor_set(v___x_3928_, 7, v_receivers_3911_);
lean_ctor_set(v___x_3928_, 8, v_nextId_3912_);
lean_ctor_set(v___x_3928_, 9, v_pos_3914_);
lean_ctor_set_uint8(v___x_3928_, sizeof(void*)*10, v_closed_3913_);
v___x_3929_ = lean_st_ref_swap(v___y_3915_, v___x_3928_);
lean_dec(v___x_3929_);
v___x_3930_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_3930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_3931_, lean_object* v_capacity_3932_, lean_object* v_size_3933_, lean_object* v_buffer_3934_, lean_object* v_write_3935_, lean_object* v_read_3936_, lean_object* v_receivers_3937_, lean_object* v_nextId_3938_, lean_object* v_closed_3939_, lean_object* v_pos_3940_, lean_object* v___y_3941_, lean_object* v_x_3942_, lean_object* v___y_3943_){
_start:
{
uint8_t v_closed_boxed_3944_; lean_object* v_res_3945_; 
v_closed_boxed_3944_ = lean_unbox(v_closed_3939_);
v_res_3945_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_3931_, v_capacity_3932_, v_size_3933_, v_buffer_3934_, v_write_3935_, v_read_3936_, v_receivers_3937_, v_nextId_3938_, v_closed_boxed_3944_, v_pos_3940_, v___y_3941_, v_x_3942_);
lean_dec(v___y_3941_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_3946_){
_start:
{
if (lean_obj_tag(v_x_3946_) == 0)
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_x_3946_);
return v___x_3948_;
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3958_; 
v_a_3949_ = lean_ctor_get(v_x_3946_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_x_3946_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3951_ = v_x_3946_;
v_isShared_3952_ = v_isSharedCheck_3958_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v_x_3946_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3958_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3953_ = l_List_reverse___redArg(v_a_3949_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 0, v___x_3953_);
v___x_3955_ = v___x_3951_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3953_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_3959_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_3962_, lean_object* v___x_3963_, lean_object* v_x_3964_){
_start:
{
if (lean_obj_tag(v_x_3964_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v___x_3963_);
lean_dec(v_a_3962_);
v_a_3966_ = lean_ctor_get(v_x_3964_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_x_3964_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3968_ = v_x_3964_;
v_isShared_3969_ = v_isSharedCheck_3974_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v_x_3964_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3974_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3991_; 
v_a_3975_ = lean_ctor_get(v_x_3964_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v_x_3964_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3977_ = v_x_3964_;
v_isShared_3978_ = v_isSharedCheck_3991_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v_x_3964_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3991_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
uint8_t v___x_3979_; 
v___x_3979_ = l_List_isEmpty___redArg(v_a_3962_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3982_; 
lean_dec(v___x_3963_);
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v_a_3975_);
lean_ctor_set(v___x_3980_, 1, v_a_3962_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v___x_3980_);
v___x_3982_ = v___x_3977_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
return v___x_3983_;
}
}
else
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3988_; 
lean_dec(v_a_3962_);
v___x_3985_ = l_List_reverse___redArg(v_a_3975_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3963_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v___x_3986_);
v___x_3988_ = v___x_3977_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3989_; 
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
return v___x_3989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_3992_, lean_object* v___x_3993_, lean_object* v_x_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_3992_, v___x_3993_, v_x_3994_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_3997_){
_start:
{
uint8_t v___y_4000_; 
if (lean_obj_tag(v_x_3997_) == 0)
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v_x_3997_);
return v___x_4004_;
}
else
{
lean_object* v_a_4005_; uint8_t v___x_4006_; 
v_a_4005_ = lean_ctor_get(v_x_3997_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v_x_3997_, 1);
v___x_4006_ = lean_unbox(v_a_4005_);
lean_dec(v_a_4005_);
if (v___x_4006_ == 0)
{
uint8_t v___x_4007_; 
v___x_4007_ = 1;
v___y_4000_ = v___x_4007_;
goto v___jp_3999_;
}
else
{
uint8_t v___x_4008_; 
v___x_4008_ = 0;
v___y_4000_ = v___x_4008_;
goto v___jp_3999_;
}
}
v___jp_3999_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = lean_box(v___y_4000_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
return v___x_4003_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4009_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_4012_, lean_object* v_x_4013_, lean_object* v_head_4014_, lean_object* v_x_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4012_, v_x_4013_, v_head_4014_, v_x_4015_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_4024_, lean_object* v_x_4025_){
_start:
{
if (lean_obj_tag(v_x_4024_) == 0)
{
lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4027_, 0, v_x_4025_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
return v___x_4028_;
}
else
{
lean_object* v_head_4029_; lean_object* v_tail_4030_; lean_object* v_waiter_4031_; lean_object* v___f_4032_; lean_object* v_val_4034_; 
v_head_4029_ = lean_ctor_get(v_x_4024_, 0);
lean_inc(v_head_4029_);
v_tail_4030_ = lean_ctor_get(v_x_4024_, 1);
lean_inc(v_tail_4030_);
lean_dec_ref_known(v_x_4024_, 2);
v_waiter_4031_ = lean_ctor_get(v_head_4029_, 1);
lean_inc(v_waiter_4031_);
v___f_4032_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4032_, 0, v_tail_4030_);
lean_closure_set(v___f_4032_, 1, v_x_4025_);
lean_closure_set(v___f_4032_, 2, v_head_4029_);
if (lean_obj_tag(v_waiter_4031_) == 0)
{
lean_object* v___x_4038_; 
v___x_4038_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v_val_4034_ = v___x_4038_;
goto v___jp_4033_;
}
else
{
lean_object* v_val_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4053_; 
v_val_4039_ = lean_ctor_get(v_waiter_4031_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v_waiter_4031_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4041_ = v_waiter_4031_;
v_isShared_4042_ = v_isSharedCheck_4053_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_val_4039_);
lean_dec(v_waiter_4031_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4053_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v_finished_4043_; lean_object* v___x_4044_; lean_object* v___f_4045_; lean_object* v___x_4047_; 
v_finished_4043_ = lean_ctor_get(v_val_4039_, 0);
lean_inc(v_finished_4043_);
lean_dec(v_val_4039_);
v___x_4044_ = lean_st_ref_get(v_finished_4043_);
lean_dec(v_finished_4043_);
v___f_4045_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v___x_4044_);
v___x_4047_ = v___x_4041_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4044_);
v___x_4047_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; lean_object* v___x_4051_; 
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = 0;
v___x_4051_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4049_, v___x_4050_, v___x_4048_, v___f_4045_);
v_val_4034_ = v___x_4051_;
goto v___jp_4033_;
}
}
}
v___jp_4033_:
{
lean_object* v___x_4035_; uint8_t v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = 0;
v___x_4037_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4035_, v___x_4036_, v_val_4034_, v___f_4032_);
return v___x_4037_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_4054_, lean_object* v_x_4055_, lean_object* v_head_4056_, lean_object* v_x_4057_){
_start:
{
if (lean_obj_tag(v_x_4057_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4067_; 
lean_dec_ref(v_head_4056_);
lean_dec(v_x_4055_);
lean_dec(v_tail_4054_);
v_a_4059_ = lean_ctor_get(v_x_4057_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_x_4057_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4061_ = v_x_4057_;
v_isShared_4062_ = v_isSharedCheck_4067_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v_x_4057_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4067_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4065_; 
v___x_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
return v___x_4065_;
}
}
}
else
{
lean_object* v_a_4068_; uint8_t v___x_4069_; 
v_a_4068_ = lean_ctor_get(v_x_4057_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v_x_4057_, 1);
v___x_4069_ = lean_unbox(v_a_4068_);
lean_dec(v_a_4068_);
if (v___x_4069_ == 0)
{
lean_object* v___x_4070_; 
lean_dec_ref(v_head_4056_);
v___x_4070_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4054_, v_x_4055_);
return v___x_4070_;
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_head_4056_);
lean_ctor_set(v___x_4071_, 1, v_x_4055_);
v___x_4072_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4054_, v___x_4071_);
return v___x_4072_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_4073_, lean_object* v_x_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4073_, v_x_4074_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_4077_, lean_object* v___x_4078_, lean_object* v___f_4079_, lean_object* v_x_4080_){
_start:
{
if (lean_obj_tag(v_x_4080_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4090_; 
lean_dec_ref(v___f_4079_);
lean_dec(v___x_4078_);
lean_dec(v_eList_4077_);
v_a_4082_ = lean_ctor_get(v_x_4080_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_x_4080_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4084_ = v_x_4080_;
v_isShared_4085_ = v_isSharedCheck_4090_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v_x_4080_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4090_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; 
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; lean_object* v___x_4095_; lean_object* v___f_4096_; lean_object* v___x_4097_; 
v_a_4091_ = lean_ctor_get(v_x_4080_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v_x_4080_, 1);
lean_inc(v___x_4078_);
v___x_4092_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4077_, v___x_4078_);
v___x_4093_ = lean_unsigned_to_nat(0u);
v___x_4094_ = 0;
v___x_4095_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4093_, v___x_4094_, v___x_4092_, v___f_4079_);
v___f_4096_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4096_, 0, v_a_4091_);
lean_closure_set(v___f_4096_, 1, v___x_4078_);
v___x_4097_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4093_, v___x_4094_, v___x_4095_, v___f_4096_);
return v___x_4097_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_4098_, lean_object* v___x_4099_, lean_object* v___f_4100_, lean_object* v_x_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v_eList_4098_, v___x_4099_, v___f_4100_, v_x_4101_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v_eList_4108_; lean_object* v_dList_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___f_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; lean_object* v___f_4116_; lean_object* v___x_4117_; 
v_eList_4108_ = lean_ctor_get(v_q_4105_, 0);
lean_inc(v_eList_4108_);
v_dList_4109_ = lean_ctor_get(v_q_4105_, 1);
lean_inc(v_dList_4109_);
lean_dec_ref(v_q_4105_);
v___x_4110_ = lean_box(0);
v___x_4111_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4109_, v___x_4110_);
v___f_4112_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = 0;
v___x_4115_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4113_, v___x_4114_, v___x_4111_, v___f_4112_);
v___f_4116_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4116_, 0, v_eList_4108_);
lean_closure_set(v___f_4116_, 1, v___x_4110_);
lean_closure_set(v___f_4116_, 2, v___f_4112_);
v___x_4117_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4113_, v___x_4114_, v___x_4115_, v___f_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4118_, v___y_4119_);
lean_dec(v___y_4119_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4122_, lean_object* v_x_4123_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4133_; 
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
lean_object* v_a_4134_; lean_object* v_producers_4135_; lean_object* v_waiters_4136_; lean_object* v_capacity_4137_; lean_object* v_size_4138_; lean_object* v_buffer_4139_; lean_object* v_write_4140_; lean_object* v_read_4141_; lean_object* v_receivers_4142_; lean_object* v_nextId_4143_; uint8_t v_closed_4144_; lean_object* v_pos_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___f_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; lean_object* v___x_4151_; 
v_a_4134_ = lean_ctor_get(v_x_4123_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v_x_4123_, 1);
v_producers_4135_ = lean_ctor_get(v_a_4134_, 0);
lean_inc_ref(v_producers_4135_);
v_waiters_4136_ = lean_ctor_get(v_a_4134_, 1);
lean_inc_ref(v_waiters_4136_);
v_capacity_4137_ = lean_ctor_get(v_a_4134_, 2);
lean_inc(v_capacity_4137_);
v_size_4138_ = lean_ctor_get(v_a_4134_, 3);
lean_inc(v_size_4138_);
v_buffer_4139_ = lean_ctor_get(v_a_4134_, 4);
lean_inc_ref(v_buffer_4139_);
v_write_4140_ = lean_ctor_get(v_a_4134_, 5);
lean_inc(v_write_4140_);
v_read_4141_ = lean_ctor_get(v_a_4134_, 6);
lean_inc(v_read_4141_);
v_receivers_4142_ = lean_ctor_get(v_a_4134_, 7);
lean_inc(v_receivers_4142_);
v_nextId_4143_ = lean_ctor_get(v_a_4134_, 8);
lean_inc(v_nextId_4143_);
v_closed_4144_ = lean_ctor_get_uint8(v_a_4134_, sizeof(void*)*10);
v_pos_4145_ = lean_ctor_get(v_a_4134_, 9);
lean_inc(v_pos_4145_);
lean_dec(v_a_4134_);
v___x_4146_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4136_, v___y_4122_);
v___x_4147_ = lean_box(v_closed_4144_);
lean_inc(v___y_4122_);
v___f_4148_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4148_, 0, v_producers_4135_);
lean_closure_set(v___f_4148_, 1, v_capacity_4137_);
lean_closure_set(v___f_4148_, 2, v_size_4138_);
lean_closure_set(v___f_4148_, 3, v_buffer_4139_);
lean_closure_set(v___f_4148_, 4, v_write_4140_);
lean_closure_set(v___f_4148_, 5, v_read_4141_);
lean_closure_set(v___f_4148_, 6, v_receivers_4142_);
lean_closure_set(v___f_4148_, 7, v_nextId_4143_);
lean_closure_set(v___f_4148_, 8, v___x_4147_);
lean_closure_set(v___f_4148_, 9, v_pos_4145_);
lean_closure_set(v___f_4148_, 10, v___y_4122_);
v___x_4149_ = lean_unsigned_to_nat(0u);
v___x_4150_ = 0;
v___x_4151_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4149_, v___x_4150_, v___x_4146_, v___f_4148_);
return v___x_4151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4152_, lean_object* v_x_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4152_, v_x_4153_);
lean_dec(v___y_4152_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v___f_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; lean_object* v___x_4164_; 
v___x_4158_ = lean_st_ref_get(v___y_4156_);
lean_inc(v___y_4156_);
v___f_4159_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4159_, 0, v___y_4156_);
v___x_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
v___x_4162_ = lean_unsigned_to_nat(0u);
v___x_4163_ = 0;
v___x_4164_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4162_, v___x_4163_, v___x_4161_, v___f_4159_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4165_);
lean_dec(v___y_4165_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4168_, lean_object* v_waiter_4169_){
_start:
{
lean_object* v_val_4172_; lean_object* v___x_4174_; 
v___x_4174_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4168_, v_waiter_4169_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4174_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4174_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set_tag(v___x_4177_, 1);
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
v_val_4172_ = v___x_4180_;
goto v___jp_4171_;
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4174_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4174_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
lean_ctor_set_tag(v___x_4185_, 0);
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
v_val_4172_ = v___x_4188_;
goto v___jp_4171_;
}
}
}
v___jp_4171_:
{
lean_object* v___x_4173_; 
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v_val_4172_);
return v___x_4173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4191_, lean_object* v_waiter_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4191_, v_waiter_4192_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4195_){
_start:
{
if (lean_obj_tag(v_x_4195_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4205_; 
v_a_4197_ = lean_ctor_get(v_x_4195_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v_x_4195_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4199_ = v_x_4195_;
v_isShared_4200_ = v_isSharedCheck_4205_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v_x_4195_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4205_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4202_);
return v___x_4203_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4215_; 
v_a_4206_ = lean_ctor_get(v_x_4195_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v_x_4195_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4208_ = v_x_4195_;
v_isShared_4209_ = v_isSharedCheck_4215_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v_x_4195_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4215_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_a_4206_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 0, v___x_4210_);
v___x_4212_ = v___x_4208_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
lean_object* v___x_4213_; 
v___x_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4212_);
return v___x_4213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4216_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_val_4219_, lean_object* v_x_4220_){
_start:
{
if (lean_obj_tag(v_x_4220_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4230_; 
v_a_4222_ = lean_ctor_get(v_x_4220_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v_x_4220_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4224_ = v_x_4220_;
v_isShared_4225_ = v_isSharedCheck_4230_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v_x_4220_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4230_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
lean_object* v___x_4228_; 
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
return v___x_4228_;
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4242_; 
v_a_4231_ = lean_ctor_get(v_x_4220_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_x_4220_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4233_ = v_x_4220_;
v_isShared_4234_ = v_isSharedCheck_4242_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v_x_4220_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4242_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v_pos_4235_; uint8_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4239_; 
v_pos_4235_ = lean_ctor_get(v_a_4231_, 1);
lean_inc(v_pos_4235_);
lean_dec(v_a_4231_);
v___x_4236_ = lean_nat_dec_eq(v_pos_4235_, v_val_4219_);
lean_dec(v_pos_4235_);
v___x_4237_ = lean_box(v___x_4236_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4237_);
v___x_4239_ = v___x_4233_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
return v___x_4240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_val_4243_, lean_object* v_x_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_val_4243_, v_x_4244_);
lean_dec(v_val_4243_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v___x_4247_, uint8_t v_closed_4248_, lean_object* v___f_4249_, lean_object* v_x_4250_){
_start:
{
if (lean_obj_tag(v_x_4250_) == 0)
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4260_; 
lean_dec_ref(v___f_4249_);
lean_dec(v___x_4247_);
v_a_4252_ = lean_ctor_get(v_x_4250_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_x_4250_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4254_ = v_x_4250_;
v_isShared_4255_ = v_isSharedCheck_4260_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v_x_4250_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4260_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
lean_object* v___x_4258_; 
v___x_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
return v___x_4258_;
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4271_; 
v_a_4261_ = lean_ctor_get(v_x_4250_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_x_4250_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4263_ = v_x_4250_;
v_isShared_4264_ = v_isSharedCheck_4271_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v_x_4250_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4271_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4265_; lean_object* v___x_4267_; 
v___x_4265_ = lean_st_ref_get(v_a_4261_);
lean_dec(v_a_4261_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v___x_4265_);
v___x_4267_ = v___x_4263_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4265_);
v___x_4267_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
v___x_4269_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4247_, v_closed_4248_, v___x_4268_, v___f_4249_);
return v___x_4269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v___x_4272_, lean_object* v_closed_4273_, lean_object* v___f_4274_, lean_object* v_x_4275_, lean_object* v___y_4276_){
_start:
{
uint8_t v_closed_boxed_4277_; lean_object* v_res_4278_; 
v_closed_boxed_4277_ = lean_unbox(v_closed_4273_);
v_res_4278_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v___x_4272_, v_closed_boxed_4277_, v___f_4274_, v_x_4275_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v_id_4279_, lean_object* v___y_4280_, lean_object* v_x_4281_){
_start:
{
if (lean_obj_tag(v_x_4281_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4291_; 
v_a_4283_ = lean_ctor_get(v_x_4281_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_x_4281_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4285_ = v_x_4281_;
v_isShared_4286_ = v_isSharedCheck_4291_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v_x_4281_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4291_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
return v___x_4289_;
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4331_; 
v_a_4292_ = lean_ctor_get(v_x_4281_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v_x_4281_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4294_ = v_x_4281_;
v_isShared_4295_ = v_isSharedCheck_4331_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v_x_4281_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4331_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
uint8_t v_closed_4296_; 
v_closed_4296_ = lean_ctor_get_uint8(v_a_4292_, sizeof(void*)*10);
if (v_closed_4296_ == 0)
{
lean_object* v_capacity_4297_; lean_object* v_size_4298_; lean_object* v_receivers_4299_; lean_object* v___x_4300_; 
v_capacity_4297_ = lean_ctor_get(v_a_4292_, 2);
lean_inc(v_capacity_4297_);
v_size_4298_ = lean_ctor_get(v_a_4292_, 3);
lean_inc(v_size_4298_);
v_receivers_4299_ = lean_ctor_get(v_a_4292_, 7);
lean_inc(v_receivers_4299_);
lean_dec(v_a_4292_);
v___x_4300_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4299_, v_id_4279_);
lean_dec(v_receivers_4299_);
if (lean_obj_tag(v___x_4300_) == 1)
{
lean_object* v_val_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4320_; 
v_val_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4320_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_val_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4320_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4305_ = lean_unsigned_to_nat(0u);
v___x_4306_ = lean_nat_dec_eq(v_size_4298_, v___x_4305_);
lean_dec(v_size_4298_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___f_4309_; lean_object* v___x_4310_; lean_object* v___f_4311_; lean_object* v___x_4312_; 
lean_del_object(v___x_4303_);
lean_del_object(v___x_4294_);
v___x_4307_ = lean_nat_mod(v_val_4301_, v_capacity_4297_);
lean_dec(v_capacity_4297_);
v___x_4308_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4307_, v___y_4280_);
v___f_4309_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4309_, 0, v_val_4301_);
v___x_4310_ = lean_box(v_closed_4296_);
v___f_4311_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_4311_, 0, v___x_4305_);
lean_closure_set(v___f_4311_, 1, v___x_4310_);
lean_closure_set(v___f_4311_, 2, v___f_4309_);
v___x_4312_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4305_, v_closed_4296_, v___x_4308_, v___f_4311_);
return v___x_4312_;
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4315_; 
lean_dec(v_val_4301_);
lean_dec(v_capacity_4297_);
v___x_4313_ = lean_box(v_closed_4296_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v___x_4313_);
v___x_4315_ = v___x_4294_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4313_);
v___x_4315_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4317_; 
if (v_isShared_4304_ == 0)
{
lean_ctor_set_tag(v___x_4303_, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4315_);
v___x_4317_ = v___x_4303_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4315_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
else
{
lean_object* v___x_4321_; lean_object* v___x_4323_; 
lean_dec(v___x_4300_);
lean_dec(v_size_4298_);
lean_dec(v_capacity_4297_);
v___x_4321_ = lean_box(v_closed_4296_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v___x_4321_);
v___x_4323_ = v___x_4294_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4321_);
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
lean_object* v___x_4326_; lean_object* v___x_4328_; 
lean_dec(v_a_4292_);
v___x_4326_ = lean_box(v_closed_4296_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v___x_4326_);
v___x_4328_ = v___x_4294_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v_id_4332_, lean_object* v___y_4333_, lean_object* v_x_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v_id_4332_, v___y_4333_, v_x_4334_);
lean_dec(v___y_4333_);
lean_dec(v_id_4332_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4337_, lean_object* v_x_4338_){
_start:
{
if (lean_obj_tag(v_x_4338_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4348_; 
lean_dec_ref(v_x_4337_);
v_a_4340_ = lean_ctor_get(v_x_4338_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v_x_4338_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4342_ = v_x_4338_;
v_isShared_4343_ = v_isSharedCheck_4348_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v_x_4338_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4348_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4346_; 
v___x_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4345_);
return v___x_4346_;
}
}
}
else
{
lean_object* v___x_4349_; 
lean_dec_ref_known(v_x_4338_, 1);
v___x_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4349_, 0, v_x_4337_);
return v___x_4349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4350_, lean_object* v_x_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4350_, v_x_4351_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4356_, lean_object* v_receiverId_4357_, lean_object* v_receivers_4358_, lean_object* v_x_4359_){
_start:
{
if (lean_obj_tag(v_x_4359_) == 0)
{
lean_object* v___x_4361_; 
lean_dec(v_receivers_4358_);
lean_dec(v_receiverId_4357_);
v___x_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4361_, 0, v_x_4359_);
return v___x_4361_;
}
else
{
lean_object* v_a_4362_; 
v_a_4362_ = lean_ctor_get(v_x_4359_, 0);
if (lean_obj_tag(v_a_4362_) == 1)
{
lean_object* v___x_4363_; lean_object* v_producers_4364_; lean_object* v_waiters_4365_; lean_object* v_capacity_4366_; lean_object* v_size_4367_; lean_object* v_buffer_4368_; lean_object* v_write_4369_; lean_object* v_read_4370_; lean_object* v_nextId_4371_; uint8_t v_closed_4372_; lean_object* v_pos_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4387_; 
v___x_4363_ = lean_st_ref_take(v_a_4356_);
v_producers_4364_ = lean_ctor_get(v___x_4363_, 0);
v_waiters_4365_ = lean_ctor_get(v___x_4363_, 1);
v_capacity_4366_ = lean_ctor_get(v___x_4363_, 2);
v_size_4367_ = lean_ctor_get(v___x_4363_, 3);
v_buffer_4368_ = lean_ctor_get(v___x_4363_, 4);
v_write_4369_ = lean_ctor_get(v___x_4363_, 5);
v_read_4370_ = lean_ctor_get(v___x_4363_, 6);
v_nextId_4371_ = lean_ctor_get(v___x_4363_, 8);
v_closed_4372_ = lean_ctor_get_uint8(v___x_4363_, sizeof(void*)*10);
v_pos_4373_ = lean_ctor_get(v___x_4363_, 9);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4387_ == 0)
{
lean_object* v_unused_4388_; 
v_unused_4388_ = lean_ctor_get(v___x_4363_, 7);
lean_dec(v_unused_4388_);
v___x_4375_ = v___x_4363_;
v_isShared_4376_ = v_isSharedCheck_4387_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_pos_4373_);
lean_inc(v_nextId_4371_);
lean_inc(v_read_4370_);
lean_inc(v_write_4369_);
lean_inc(v_buffer_4368_);
lean_inc(v_size_4367_);
lean_inc(v_capacity_4366_);
lean_inc(v_waiters_4365_);
lean_inc(v_producers_4364_);
lean_dec(v___x_4363_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4387_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v___x_4379_; 
v___x_4377_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4357_, v_receivers_4358_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 7, v___x_4377_);
v___x_4379_ = v___x_4375_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_producers_4364_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_waiters_4365_);
lean_ctor_set(v_reuseFailAlloc_4386_, 2, v_capacity_4366_);
lean_ctor_set(v_reuseFailAlloc_4386_, 3, v_size_4367_);
lean_ctor_set(v_reuseFailAlloc_4386_, 4, v_buffer_4368_);
lean_ctor_set(v_reuseFailAlloc_4386_, 5, v_write_4369_);
lean_ctor_set(v_reuseFailAlloc_4386_, 6, v_read_4370_);
lean_ctor_set(v_reuseFailAlloc_4386_, 7, v___x_4377_);
lean_ctor_set(v_reuseFailAlloc_4386_, 8, v_nextId_4371_);
lean_ctor_set(v_reuseFailAlloc_4386_, 9, v_pos_4373_);
lean_ctor_set_uint8(v_reuseFailAlloc_4386_, sizeof(void*)*10, v_closed_4372_);
v___x_4379_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4380_; lean_object* v___f_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; lean_object* v___x_4385_; 
v___x_4380_ = lean_st_ref_put(v_a_4356_, v___x_4379_);
v___f_4381_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4381_, 0, v_x_4359_);
v___x_4382_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4383_ = lean_unsigned_to_nat(0u);
v___x_4384_ = 0;
v___x_4385_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4383_, v___x_4384_, v___x_4382_, v___f_4381_);
return v___x_4385_;
}
}
}
else
{
lean_object* v___x_4389_; 
lean_dec_ref_known(v_x_4359_, 1);
lean_dec(v_receivers_4358_);
lean_dec(v_receiverId_4357_);
v___x_4389_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4390_, lean_object* v_receiverId_4391_, lean_object* v_receivers_4392_, lean_object* v_x_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4390_, v_receiverId_4391_, v_receivers_4392_, v_x_4393_);
lean_dec(v_a_4390_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4396_){
_start:
{
if (lean_obj_tag(v_x_4396_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4406_; 
v_a_4398_ = lean_ctor_get(v_x_4396_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_x_4396_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4400_ = v_x_4396_;
v_isShared_4401_ = v_isSharedCheck_4406_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v_x_4396_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4406_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4419_; 
v_a_4407_ = lean_ctor_get(v_x_4396_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v_x_4396_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4409_ = v_x_4396_;
v_isShared_4410_ = v_isSharedCheck_4419_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v_x_4396_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4419_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v_size_4411_; lean_object* v___x_4412_; uint8_t v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
v_size_4411_ = lean_ctor_get(v_a_4407_, 3);
lean_inc(v_size_4411_);
lean_dec(v_a_4407_);
v___x_4412_ = lean_unsigned_to_nat(0u);
v___x_4413_ = lean_nat_dec_eq(v_size_4411_, v___x_4412_);
lean_dec(v_size_4411_);
v___x_4414_ = lean_box(v___x_4413_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4414_);
v___x_4416_ = v___x_4409_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; 
v___x_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
return v___x_4417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4420_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4424_){
_start:
{
lean_object* v___x_4426_; lean_object* v___f_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; lean_object* v___x_4432_; 
v___x_4426_ = lean_st_ref_get(v_a_4424_);
v___f_4427_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4426_);
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
v___x_4430_ = lean_unsigned_to_nat(0u);
v___x_4431_ = 0;
v___x_4432_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4430_, v___x_4431_, v___x_4429_, v___f_4427_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4433_);
lean_dec(v_a_4433_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4436_, lean_object* v_next_4437_){
_start:
{
lean_object* v___x_4439_; lean_object* v_fst_4441_; lean_object* v_snd_4442_; lean_object* v_value_4446_; lean_object* v_pos_4447_; lean_object* v_remaining_4448_; uint8_t v___x_4449_; 
v___x_4439_ = lean_st_ref_take(v_slot_4436_);
v_value_4446_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_value_4446_);
v_pos_4447_ = lean_ctor_get(v___x_4439_, 1);
lean_inc(v_pos_4447_);
v_remaining_4448_ = lean_ctor_get(v___x_4439_, 2);
lean_inc(v_remaining_4448_);
v___x_4449_ = lean_nat_dec_eq(v_next_4437_, v_pos_4447_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
lean_dec(v_remaining_4448_);
lean_dec(v_pos_4447_);
lean_dec(v_value_4446_);
v___x_4450_ = lean_box(0);
v___x_4451_ = lean_box(v___x_4449_);
v___x_4452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4450_);
lean_ctor_set(v___x_4452_, 1, v___x_4451_);
v_fst_4441_ = v___x_4452_;
v_snd_4442_ = v___x_4439_;
goto v___jp_4440_;
}
else
{
lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4471_; 
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4471_ == 0)
{
lean_object* v_unused_4472_; lean_object* v_unused_4473_; lean_object* v_unused_4474_; 
v_unused_4472_ = lean_ctor_get(v___x_4439_, 2);
lean_dec(v_unused_4472_);
v_unused_4473_ = lean_ctor_get(v___x_4439_, 1);
lean_dec(v_unused_4473_);
v_unused_4474_ = lean_ctor_get(v___x_4439_, 0);
lean_dec(v_unused_4474_);
v___x_4454_ = v___x_4439_;
v_isShared_4455_ = v_isSharedCheck_4471_;
goto v_resetjp_4453_;
}
else
{
lean_dec(v___x_4439_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4471_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; uint8_t v___x_4457_; 
v___x_4456_ = lean_unsigned_to_nat(1u);
v___x_4457_ = lean_nat_dec_eq(v_remaining_4448_, v___x_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4462_; 
v___x_4458_ = lean_box(v___x_4457_);
lean_inc(v_value_4446_);
v___x_4459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4459_, 0, v_value_4446_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
v___x_4460_ = lean_nat_sub(v_remaining_4448_, v___x_4456_);
lean_dec(v_remaining_4448_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 2, v___x_4460_);
v___x_4462_ = v___x_4454_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_value_4446_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v_pos_4447_);
lean_ctor_set(v_reuseFailAlloc_4463_, 2, v___x_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
v_fst_4441_ = v___x_4459_;
v_snd_4442_ = v___x_4462_;
goto v___jp_4440_;
}
}
else
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4469_; 
lean_dec(v_remaining_4448_);
v___x_4464_ = lean_box(v___x_4449_);
v___x_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4465_, 0, v_value_4446_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
v___x_4466_ = lean_box(0);
v___x_4467_ = lean_unsigned_to_nat(0u);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 2, v___x_4467_);
lean_ctor_set(v___x_4454_, 0, v___x_4466_);
v___x_4469_ = v___x_4454_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4466_);
lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_pos_4447_);
lean_ctor_set(v_reuseFailAlloc_4470_, 2, v___x_4467_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
v_fst_4441_ = v___x_4465_;
v_snd_4442_ = v___x_4469_;
goto v___jp_4440_;
}
}
}
}
v___jp_4440_:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v___x_4443_ = lean_st_ref_put(v_slot_4436_, v_snd_4442_);
v___x_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4444_, 0, v_fst_4441_);
v___x_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4444_);
return v___x_4445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4475_, lean_object* v_next_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v_res_4478_; 
v_res_4478_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4475_, v_next_4476_);
lean_dec(v_next_4476_);
lean_dec(v_slot_4475_);
return v_res_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4479_, uint8_t v_a_4480_, lean_object* v___f_4481_, lean_object* v_x_4482_){
_start:
{
if (lean_obj_tag(v_x_4482_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4492_; 
lean_dec_ref(v___f_4481_);
v_a_4484_ = lean_ctor_get(v_x_4482_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v_x_4482_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4486_ = v_x_4482_;
v_isShared_4487_ = v_isSharedCheck_4492_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v_x_4482_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4492_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4490_; 
v___x_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
return v___x_4490_;
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v_a_4493_ = lean_ctor_get(v_x_4482_, 0);
lean_inc(v_a_4493_);
lean_dec_ref_known(v_x_4482_, 1);
v___x_4494_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4493_, v_next_4479_);
lean_dec(v_a_4493_);
v___x_4495_ = lean_unsigned_to_nat(0u);
v___x_4496_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4495_, v_a_4480_, v___x_4494_, v___f_4481_);
return v___x_4496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4497_, lean_object* v_a_4498_, lean_object* v___f_4499_, lean_object* v_x_4500_, lean_object* v___y_4501_){
_start:
{
uint8_t v_a_12281__boxed_4502_; lean_object* v_res_4503_; 
v_a_12281__boxed_4502_ = lean_unbox(v_a_4498_);
v_res_4503_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4497_, v_a_12281__boxed_4502_, v___f_4499_, v_x_4500_);
lean_dec(v_next_4497_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4504_, lean_object* v___f_4505_, lean_object* v_____r_4506_, lean_object* v_st_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4510_ = lean_st_ref_swap(v___y_4508_, v_st_4507_);
lean_dec(v___x_4510_);
v___x_4511_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4512_ = lean_unsigned_to_nat(0u);
v___x_4513_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4512_, v_a_4504_, v___x_4511_, v___f_4505_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4514_, lean_object* v___f_4515_, lean_object* v_____r_4516_, lean_object* v_st_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
uint8_t v_a_12323__boxed_4520_; lean_object* v_res_4521_; 
v_a_12323__boxed_4520_ = lean_unbox(v_a_4514_);
v_res_4521_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_12323__boxed_4520_, v___f_4515_, v_____r_4516_, v_st_4517_, v___y_4518_);
lean_dec(v___y_4518_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4522_, lean_object* v_waiters_4523_, lean_object* v_capacity_4524_, lean_object* v_size_4525_, lean_object* v_buffer_4526_, lean_object* v_write_4527_, lean_object* v_read_4528_, lean_object* v_receivers_4529_, lean_object* v_nextId_4530_, uint8_t v_closed_4531_, lean_object* v_pos_4532_, lean_object* v___f_4533_, lean_object* v_a_4534_, lean_object* v_x_4535_){
_start:
{
if (lean_obj_tag(v_x_4535_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4545_; 
lean_dec_ref(v___f_4533_);
lean_dec(v_pos_4532_);
lean_dec(v_nextId_4530_);
lean_dec(v_receivers_4529_);
lean_dec(v_read_4528_);
lean_dec(v_write_4527_);
lean_dec_ref(v_buffer_4526_);
lean_dec(v_size_4525_);
lean_dec(v_capacity_4524_);
lean_dec_ref(v_waiters_4523_);
lean_dec_ref(v_snd_4522_);
v_a_4537_ = lean_ctor_get(v_x_4535_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_x_4535_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4539_ = v_x_4535_;
v_isShared_4540_ = v_isSharedCheck_4545_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v_x_4535_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4545_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
lean_object* v___x_4543_; 
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
lean_dec_ref_known(v_x_4535_, 1);
v___x_4546_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4546_, 0, v_snd_4522_);
lean_ctor_set(v___x_4546_, 1, v_waiters_4523_);
lean_ctor_set(v___x_4546_, 2, v_capacity_4524_);
lean_ctor_set(v___x_4546_, 3, v_size_4525_);
lean_ctor_set(v___x_4546_, 4, v_buffer_4526_);
lean_ctor_set(v___x_4546_, 5, v_write_4527_);
lean_ctor_set(v___x_4546_, 6, v_read_4528_);
lean_ctor_set(v___x_4546_, 7, v_receivers_4529_);
lean_ctor_set(v___x_4546_, 8, v_nextId_4530_);
lean_ctor_set(v___x_4546_, 9, v_pos_4532_);
lean_ctor_set_uint8(v___x_4546_, sizeof(void*)*10, v_closed_4531_);
v___x_4547_ = lean_box(0);
lean_inc(v_a_4534_);
v___x_4548_ = lean_apply_4(v___f_4533_, v___x_4547_, v___x_4546_, v_a_4534_, lean_box(0));
return v___x_4548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4549_, lean_object* v_waiters_4550_, lean_object* v_capacity_4551_, lean_object* v_size_4552_, lean_object* v_buffer_4553_, lean_object* v_write_4554_, lean_object* v_read_4555_, lean_object* v_receivers_4556_, lean_object* v_nextId_4557_, lean_object* v_closed_4558_, lean_object* v_pos_4559_, lean_object* v___f_4560_, lean_object* v_a_4561_, lean_object* v_x_4562_, lean_object* v___y_4563_){
_start:
{
uint8_t v_closed_boxed_4564_; lean_object* v_res_4565_; 
v_closed_boxed_4564_ = lean_unbox(v_closed_4558_);
v_res_4565_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4549_, v_waiters_4550_, v_capacity_4551_, v_size_4552_, v_buffer_4553_, v_write_4554_, v_read_4555_, v_receivers_4556_, v_nextId_4557_, v_closed_boxed_4564_, v_pos_4559_, v___f_4560_, v_a_4561_, v_x_4562_);
lean_dec(v_a_4561_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4566_, lean_object* v_x_4567_){
_start:
{
if (lean_obj_tag(v_x_4567_) == 0)
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4577_; 
lean_dec(v_fst_4566_);
v_a_4569_ = lean_ctor_get(v_x_4567_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v_x_4567_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4571_ = v_x_4567_;
v_isShared_4572_ = v_isSharedCheck_4577_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v_x_4567_);
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
lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4585_; 
v_isSharedCheck_4585_ = !lean_is_exclusive(v_x_4567_);
if (v_isSharedCheck_4585_ == 0)
{
lean_object* v_unused_4586_; 
v_unused_4586_ = lean_ctor_get(v_x_4567_, 0);
lean_dec(v_unused_4586_);
v___x_4579_ = v_x_4567_;
v_isShared_4580_ = v_isSharedCheck_4585_;
goto v_resetjp_4578_;
}
else
{
lean_dec(v_x_4567_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4585_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
lean_ctor_set(v___x_4579_, 0, v_fst_4566_);
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_fst_4566_);
v___x_4582_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; 
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
return v___x_4583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4587_, lean_object* v_x_4588_, lean_object* v___y_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4587_, v_x_4588_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, uint8_t v___x_4594_, lean_object* v_x_4595_){
_start:
{
if (lean_obj_tag(v_x_4595_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4605_; 
lean_dec_ref(v_a_4592_);
v_a_4597_ = lean_ctor_get(v_x_4595_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v_x_4595_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4599_ = v_x_4595_;
v_isShared_4600_ = v_isSharedCheck_4605_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v_x_4595_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4605_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
return v___x_4603_;
}
}
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4653_; 
v_a_4606_ = lean_ctor_get(v_x_4595_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_x_4595_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4608_ = v_x_4595_;
v_isShared_4609_ = v_isSharedCheck_4653_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v_x_4595_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4653_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v_fst_4610_; 
v_fst_4610_ = lean_ctor_get(v_a_4606_, 0);
lean_inc(v_fst_4610_);
if (lean_obj_tag(v_fst_4610_) == 1)
{
lean_object* v_snd_4611_; lean_object* v___f_4612_; lean_object* v___x_4613_; lean_object* v___f_4614_; uint8_t v___x_4615_; 
v_snd_4611_ = lean_ctor_get(v_a_4606_, 1);
lean_inc(v_snd_4611_);
lean_dec(v_a_4606_);
v___f_4612_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4612_, 0, v_fst_4610_);
v___x_4613_ = lean_box(v_a_4591_);
lean_inc_ref(v___f_4612_);
v___f_4614_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4614_, 0, v___x_4613_);
lean_closure_set(v___f_4614_, 1, v___f_4612_);
v___x_4615_ = lean_unbox(v_snd_4611_);
lean_dec(v_snd_4611_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
lean_dec_ref(v___f_4614_);
lean_del_object(v___x_4608_);
v___x_4616_ = lean_box(0);
v___x_4617_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4591_, v___f_4612_, v___x_4616_, v_a_4592_, v_a_4593_);
return v___x_4617_;
}
else
{
lean_object* v___x_4618_; lean_object* v_producers_4619_; lean_object* v_waiters_4620_; lean_object* v_capacity_4621_; lean_object* v_size_4622_; lean_object* v_buffer_4623_; lean_object* v_write_4624_; lean_object* v_read_4625_; lean_object* v_receivers_4626_; lean_object* v_nextId_4627_; uint8_t v_closed_4628_; lean_object* v_pos_4629_; lean_object* v___x_4630_; 
v___x_4618_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4592_);
v_producers_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc_ref(v_producers_4619_);
v_waiters_4620_ = lean_ctor_get(v___x_4618_, 1);
lean_inc_ref(v_waiters_4620_);
v_capacity_4621_ = lean_ctor_get(v___x_4618_, 2);
lean_inc(v_capacity_4621_);
v_size_4622_ = lean_ctor_get(v___x_4618_, 3);
lean_inc(v_size_4622_);
v_buffer_4623_ = lean_ctor_get(v___x_4618_, 4);
lean_inc_ref(v_buffer_4623_);
v_write_4624_ = lean_ctor_get(v___x_4618_, 5);
lean_inc(v_write_4624_);
v_read_4625_ = lean_ctor_get(v___x_4618_, 6);
lean_inc(v_read_4625_);
v_receivers_4626_ = lean_ctor_get(v___x_4618_, 7);
lean_inc(v_receivers_4626_);
v_nextId_4627_ = lean_ctor_get(v___x_4618_, 8);
lean_inc(v_nextId_4627_);
v_closed_4628_ = lean_ctor_get_uint8(v___x_4618_, sizeof(void*)*10);
v_pos_4629_ = lean_ctor_get(v___x_4618_, 9);
lean_inc(v_pos_4629_);
v___x_4630_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4619_);
if (lean_obj_tag(v___x_4630_) == 1)
{
lean_object* v_val_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4649_; 
lean_dec_ref(v___x_4618_);
lean_dec_ref(v___f_4612_);
v_val_4631_ = lean_ctor_get(v___x_4630_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4633_ = v___x_4630_;
v_isShared_4634_ = v_isSharedCheck_4649_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_val_4631_);
lean_dec(v___x_4630_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4649_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v_fst_4635_; lean_object* v_snd_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___f_4640_; lean_object* v___x_4642_; 
v_fst_4635_ = lean_ctor_get(v_val_4631_, 0);
lean_inc(v_fst_4635_);
v_snd_4636_ = lean_ctor_get(v_val_4631_, 1);
lean_inc(v_snd_4636_);
lean_dec(v_val_4631_);
v___x_4637_ = lean_box(v___x_4594_);
v___x_4638_ = lean_io_promise_resolve(v___x_4637_, v_fst_4635_);
lean_dec(v_fst_4635_);
v___x_4639_ = lean_box(v_closed_4628_);
lean_inc(v_a_4593_);
v___f_4640_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4640_, 0, v_snd_4636_);
lean_closure_set(v___f_4640_, 1, v_waiters_4620_);
lean_closure_set(v___f_4640_, 2, v_capacity_4621_);
lean_closure_set(v___f_4640_, 3, v_size_4622_);
lean_closure_set(v___f_4640_, 4, v_buffer_4623_);
lean_closure_set(v___f_4640_, 5, v_write_4624_);
lean_closure_set(v___f_4640_, 6, v_read_4625_);
lean_closure_set(v___f_4640_, 7, v_receivers_4626_);
lean_closure_set(v___f_4640_, 8, v_nextId_4627_);
lean_closure_set(v___f_4640_, 9, v___x_4639_);
lean_closure_set(v___f_4640_, 10, v_pos_4629_);
lean_closure_set(v___f_4640_, 11, v___f_4614_);
lean_closure_set(v___f_4640_, 12, v_a_4593_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v___x_4638_);
v___x_4642_ = v___x_4608_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4638_);
v___x_4642_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4644_; 
if (v_isShared_4634_ == 0)
{
lean_ctor_set_tag(v___x_4633_, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4642_);
v___x_4644_ = v___x_4633_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = lean_unsigned_to_nat(0u);
v___x_4646_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4645_, v_a_4591_, v___x_4644_, v___f_4640_);
return v___x_4646_;
}
}
}
}
else
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
lean_dec(v___x_4630_);
lean_dec(v_pos_4629_);
lean_dec(v_nextId_4627_);
lean_dec(v_receivers_4626_);
lean_dec(v_read_4625_);
lean_dec(v_write_4624_);
lean_dec_ref(v_buffer_4623_);
lean_dec(v_size_4622_);
lean_dec(v_capacity_4621_);
lean_dec_ref(v_waiters_4620_);
lean_dec_ref(v___f_4614_);
lean_del_object(v___x_4608_);
v___x_4650_ = lean_box(0);
v___x_4651_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4591_, v___f_4612_, v___x_4650_, v___x_4618_, v_a_4593_);
return v___x_4651_;
}
}
}
else
{
lean_object* v___x_4652_; 
lean_dec(v_fst_4610_);
lean_del_object(v___x_4608_);
lean_dec(v_a_4606_);
lean_dec_ref(v_a_4592_);
v___x_4652_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v___x_4657_, lean_object* v_x_4658_, lean_object* v___y_4659_){
_start:
{
uint8_t v_a_12435__boxed_4660_; uint8_t v___x_12437__boxed_4661_; lean_object* v_res_4662_; 
v_a_12435__boxed_4660_ = lean_unbox(v_a_4654_);
v___x_12437__boxed_4661_ = lean_unbox(v___x_4657_);
v_res_4662_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12435__boxed_4660_, v_a_4655_, v_a_4656_, v___x_12437__boxed_4661_, v_x_4658_);
lean_dec(v_a_4656_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4663_, lean_object* v_next_4664_, lean_object* v_a_4665_, lean_object* v_x_4666_){
_start:
{
if (lean_obj_tag(v_x_4666_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4676_; 
lean_dec(v_next_4664_);
lean_dec_ref(v_a_4663_);
v_a_4668_ = lean_ctor_get(v_x_4666_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_x_4666_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4670_ = v_x_4666_;
v_isShared_4671_ = v_isSharedCheck_4676_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v_x_4666_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4676_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
lean_object* v___x_4674_; 
v___x_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
return v___x_4674_;
}
}
}
else
{
lean_object* v_a_4677_; uint8_t v___x_4678_; 
v_a_4677_ = lean_ctor_get(v_x_4666_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v_x_4666_, 1);
v___x_4678_ = lean_unbox(v_a_4677_);
if (v___x_4678_ == 0)
{
lean_object* v_capacity_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; uint8_t v___x_4682_; lean_object* v___x_4683_; lean_object* v___f_4684_; lean_object* v___f_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; lean_object* v___x_4688_; 
v_capacity_4679_ = lean_ctor_get(v_a_4663_, 2);
v___x_4680_ = lean_nat_mod(v_next_4664_, v_capacity_4679_);
v___x_4681_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4680_, v_a_4665_);
v___x_4682_ = 1;
v___x_4683_ = lean_box(v___x_4682_);
lean_inc(v_a_4665_);
lean_inc_n(v_a_4677_, 2);
v___f_4684_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4684_, 0, v_a_4677_);
lean_closure_set(v___f_4684_, 1, v_a_4663_);
lean_closure_set(v___f_4684_, 2, v_a_4665_);
lean_closure_set(v___f_4684_, 3, v___x_4683_);
v___f_4685_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4685_, 0, v_next_4664_);
lean_closure_set(v___f_4685_, 1, v_a_4677_);
lean_closure_set(v___f_4685_, 2, v___f_4684_);
v___x_4686_ = lean_unsigned_to_nat(0u);
v___x_4687_ = lean_unbox(v_a_4677_);
lean_dec(v_a_4677_);
v___x_4688_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4686_, v___x_4687_, v___x_4681_, v___f_4685_);
return v___x_4688_;
}
else
{
lean_object* v___x_4689_; 
lean_dec(v_a_4677_);
lean_dec(v_next_4664_);
lean_dec_ref(v_a_4663_);
v___x_4689_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4690_, lean_object* v_next_4691_, lean_object* v_a_4692_, lean_object* v_x_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4690_, v_next_4691_, v_a_4692_, v_x_4693_);
lean_dec(v_a_4692_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4696_, lean_object* v_next_4697_, lean_object* v_x_4698_){
_start:
{
if (lean_obj_tag(v_x_4698_) == 0)
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4708_; 
lean_dec(v_next_4697_);
v_a_4700_ = lean_ctor_get(v_x_4698_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v_x_4698_);
if (v_isSharedCheck_4708_ == 0)
{
v___x_4702_ = v_x_4698_;
v_isShared_4703_ = v_isSharedCheck_4708_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v_x_4698_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4708_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
lean_object* v___x_4706_; 
v___x_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
return v___x_4706_;
}
}
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4710_; lean_object* v___f_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; lean_object* v___x_4714_; 
v_a_4709_ = lean_ctor_get(v_x_4698_, 0);
lean_inc(v_a_4709_);
lean_dec_ref_known(v_x_4698_, 1);
v___x_4710_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4696_);
lean_inc(v_a_4696_);
v___f_4711_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4711_, 0, v_a_4709_);
lean_closure_set(v___f_4711_, 1, v_next_4697_);
lean_closure_set(v___f_4711_, 2, v_a_4696_);
v___x_4712_ = lean_unsigned_to_nat(0u);
v___x_4713_ = 0;
v___x_4714_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4712_, v___x_4713_, v___x_4710_, v___f_4711_);
return v___x_4714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4715_, lean_object* v_next_4716_, lean_object* v_x_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4715_, v_next_4716_, v_x_4717_);
lean_dec(v_a_4715_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4720_, lean_object* v_a_4721_){
_start:
{
lean_object* v___x_4723_; lean_object* v___f_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; lean_object* v___x_4729_; 
v___x_4723_ = lean_st_ref_get(v_a_4721_);
lean_inc(v_a_4721_);
v___f_4724_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4724_, 0, v_a_4721_);
lean_closure_set(v___f_4724_, 1, v_next_4720_);
v___x_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4723_);
v___x_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4725_);
v___x_4727_ = lean_unsigned_to_nat(0u);
v___x_4728_ = 0;
v___x_4729_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4727_, v___x_4728_, v___x_4726_, v___f_4724_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4730_, lean_object* v_a_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4730_, v_a_4731_);
lean_dec(v_a_4731_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4734_, lean_object* v_a_4735_, lean_object* v_x_4736_){
_start:
{
if (lean_obj_tag(v_x_4736_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4746_; 
lean_dec(v_receiverId_4734_);
v_a_4738_ = lean_ctor_get(v_x_4736_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v_x_4736_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4740_ = v_x_4736_;
v_isShared_4741_ = v_isSharedCheck_4746_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v_x_4736_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4746_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
lean_object* v___x_4744_; 
v___x_4744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
return v___x_4744_;
}
}
}
else
{
lean_object* v_a_4747_; lean_object* v_receivers_4748_; lean_object* v___x_4749_; 
v_a_4747_ = lean_ctor_get(v_x_4736_, 0);
lean_inc(v_a_4747_);
lean_dec_ref_known(v_x_4736_, 1);
v_receivers_4748_ = lean_ctor_get(v_a_4747_, 7);
lean_inc(v_receivers_4748_);
lean_dec(v_a_4747_);
v___x_4749_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4748_, v_receiverId_4734_);
if (lean_obj_tag(v___x_4749_) == 1)
{
lean_object* v_val_4750_; lean_object* v___x_4751_; lean_object* v___f_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; lean_object* v___x_4755_; 
v_val_4750_ = lean_ctor_get(v___x_4749_, 0);
lean_inc(v_val_4750_);
lean_dec_ref_known(v___x_4749_, 1);
v___x_4751_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4750_, v_a_4735_);
lean_inc(v_a_4735_);
v___f_4752_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4752_, 0, v_a_4735_);
lean_closure_set(v___f_4752_, 1, v_receiverId_4734_);
lean_closure_set(v___f_4752_, 2, v_receivers_4748_);
v___x_4753_ = lean_unsigned_to_nat(0u);
v___x_4754_ = 0;
v___x_4755_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4753_, v___x_4754_, v___x_4751_, v___f_4752_);
return v___x_4755_;
}
else
{
lean_object* v___x_4756_; 
lean_dec(v___x_4749_);
lean_dec(v_receivers_4748_);
lean_dec(v_receiverId_4734_);
v___x_4756_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4757_, lean_object* v_a_4758_, lean_object* v_x_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4757_, v_a_4758_, v_x_4759_);
lean_dec(v_a_4758_);
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4762_, lean_object* v_a_4763_){
_start:
{
lean_object* v___x_4765_; lean_object* v___f_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; uint8_t v___x_4770_; lean_object* v___x_4771_; 
v___x_4765_ = lean_st_ref_get(v_a_4763_);
lean_inc(v_a_4763_);
v___f_4766_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4766_, 0, v_receiverId_4762_);
lean_closure_set(v___f_4766_, 1, v_a_4763_);
v___x_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4765_);
v___x_4768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4767_);
v___x_4769_ = lean_unsigned_to_nat(0u);
v___x_4770_ = 0;
v___x_4771_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4769_, v___x_4770_, v___x_4768_, v___f_4766_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4772_, lean_object* v_a_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4772_, v_a_4773_);
lean_dec(v_a_4773_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4780_, lean_object* v___y_4781_, lean_object* v___f_4782_, lean_object* v_x_4783_){
_start:
{
if (lean_obj_tag(v_x_4783_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4793_; 
lean_dec_ref(v___f_4782_);
lean_dec(v_id_4780_);
v_a_4785_ = lean_ctor_get(v_x_4783_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v_x_4783_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4787_ = v_x_4783_;
v_isShared_4788_ = v_isSharedCheck_4793_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v_x_4783_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4793_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4788_ == 0)
{
v___x_4790_ = v___x_4787_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4785_);
v___x_4790_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
lean_object* v___x_4791_; 
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
return v___x_4791_;
}
}
}
else
{
lean_object* v_a_4794_; uint8_t v___x_4795_; 
v_a_4794_ = lean_ctor_get(v_x_4783_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v_x_4783_, 1);
v___x_4795_ = lean_unbox(v_a_4794_);
lean_dec(v_a_4794_);
if (v___x_4795_ == 0)
{
lean_object* v___x_4796_; 
lean_dec_ref(v___f_4782_);
lean_dec(v_id_4780_);
v___x_4796_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1));
return v___x_4796_;
}
else
{
lean_object* v___x_4797_; lean_object* v___x_4798_; uint8_t v___x_4799_; lean_object* v___x_4800_; 
v___x_4797_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4780_, v___y_4781_);
v___x_4798_ = lean_unsigned_to_nat(0u);
v___x_4799_ = 0;
v___x_4800_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4798_, v___x_4799_, v___x_4797_, v___f_4782_);
return v___x_4800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4801_, lean_object* v___y_4802_, lean_object* v___f_4803_, lean_object* v_x_4804_, lean_object* v___y_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4801_, v___y_4802_, v___f_4803_, v_x_4804_);
lean_dec(v___y_4802_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4807_, lean_object* v___f_4808_, lean_object* v___y_4809_){
_start:
{
lean_object* v___x_4811_; lean_object* v___f_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; uint8_t v___x_4816_; lean_object* v___x_4817_; lean_object* v___f_4818_; lean_object* v___x_4819_; 
v___x_4811_ = lean_st_ref_get(v___y_4809_);
lean_inc_n(v___y_4809_, 2);
lean_inc(v_id_4807_);
v___f_4812_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_4812_, 0, v_id_4807_);
lean_closure_set(v___f_4812_, 1, v___y_4809_);
v___x_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4811_);
v___x_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4813_);
v___x_4815_ = lean_unsigned_to_nat(0u);
v___x_4816_ = 0;
v___x_4817_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4815_, v___x_4816_, v___x_4814_, v___f_4812_);
v___f_4818_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4818_, 0, v_id_4807_);
lean_closure_set(v___f_4818_, 1, v___y_4809_);
lean_closure_set(v___f_4818_, 2, v___f_4808_);
v___x_4819_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4815_, v___x_4816_, v___x_4817_, v___f_4818_);
return v___x_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4820_, lean_object* v___f_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4820_, v___f_4821_, v___y_4822_);
lean_dec(v___y_4822_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4827_){
_start:
{
lean_object* v_state_4828_; lean_object* v_id_4829_; lean_object* v___f_4830_; lean_object* v___f_4831_; lean_object* v___f_4832_; lean_object* v___f_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; 
v_state_4828_ = lean_ctor_get(v_ch_4827_, 0);
lean_inc_ref_n(v_state_4828_, 2);
v_id_4829_ = lean_ctor_get(v_ch_4827_, 1);
lean_inc(v_id_4829_);
v___f_4830_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4831_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4831_, 0, v_ch_4827_);
v___f_4832_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4833_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4833_, 0, v_id_4829_);
lean_closure_set(v___f_4833_, 1, v___f_4832_);
v___x_4834_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4834_, 0, lean_box(0));
lean_closure_set(v___x_4834_, 1, lean_box(0));
lean_closure_set(v___x_4834_, 2, v_state_4828_);
lean_closure_set(v___x_4834_, 3, v___f_4833_);
v___x_4835_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4835_, 0, lean_box(0));
lean_closure_set(v___x_4835_, 1, lean_box(0));
lean_closure_set(v___x_4835_, 2, v_state_4828_);
lean_closure_set(v___x_4835_, 3, v___f_4830_);
v___x_4836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4834_);
lean_ctor_set(v___x_4836_, 1, v___f_4831_);
lean_ctor_set(v___x_4836_, 2, v___x_4835_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4837_, lean_object* v_ch_4838_){
_start:
{
lean_object* v___x_4839_; 
v___x_4839_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4838_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4840_, lean_object* v_receiverId_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4841_, v_a_4842_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4845_, lean_object* v_receiverId_4846_, lean_object* v_a_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4845_, v_receiverId_4846_, v_a_4847_);
lean_dec(v_a_4847_);
return v_res_4849_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4850_, lean_object* v_q_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v___x_4854_; 
v___x_4854_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4851_, v___y_4852_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4855_, lean_object* v_q_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4855_, v_q_4856_, v___y_4857_);
lean_dec(v___y_4857_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4860_, lean_object* v_slot_4861_, lean_object* v_next_4862_, lean_object* v_a_4863_){
_start:
{
lean_object* v___x_4865_; 
v___x_4865_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4861_, v_next_4862_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4866_, lean_object* v_slot_4867_, lean_object* v_next_4868_, lean_object* v_a_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4866_, v_slot_4867_, v_next_4868_, v_a_4869_);
lean_dec(v_a_4869_);
lean_dec(v_next_4868_);
lean_dec(v_slot_4867_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4873_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4876_, lean_object* v_a_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4876_, v_a_4877_);
lean_dec(v_a_4877_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4880_, lean_object* v_next_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v___x_4884_; 
v___x_4884_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4881_, v_a_4882_);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4885_, lean_object* v_next_4886_, lean_object* v_a_4887_, lean_object* v___y_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4885_, v_next_4886_, v_a_4887_);
lean_dec(v_a_4887_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4890_, lean_object* v_x_4891_, lean_object* v_x_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4891_, v_x_4892_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4896_, lean_object* v_x_4897_, lean_object* v_x_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4896_, v_x_4897_, v_x_4898_, v___y_4899_);
lean_dec(v___y_4899_);
return v_res_4901_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4903_){
_start:
{
lean_object* v___x_4905_; 
v___x_4905_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4903_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4906_, lean_object* v_a_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Std_Broadcast_new___redArg(v_capacity_4906_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4909_, lean_object* v_capacity_4910_, lean_object* v_h_4911_){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4910_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4914_, lean_object* v_capacity_4915_, lean_object* v_h_4916_, lean_object* v_a_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Std_Broadcast_new(v_00_u03b1_4914_, v_capacity_4915_, v_h_4916_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4919_, lean_object* v_v_4920_){
_start:
{
lean_object* v___x_4922_; 
v___x_4922_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4919_, v_v_4920_);
return v___x_4922_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4923_, lean_object* v_v_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v_res_4926_; 
v_res_4926_ = l_Std_Broadcast_trySend___redArg(v_ch_4923_, v_v_4924_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4927_, lean_object* v_ch_4928_, lean_object* v_v_4929_){
_start:
{
lean_object* v___x_4931_; 
v___x_4931_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4928_, v_v_4929_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4932_, lean_object* v_ch_4933_, lean_object* v_v_4934_, lean_object* v_a_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Std_Broadcast_trySend(v_00_u03b1_4932_, v_ch_4933_, v_v_4934_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4937_){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4937_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
v_a_4940_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4942_ = v___x_4939_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_a_4940_);
lean_dec(v___x_4939_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
v_a_4948_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4939_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4939_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_4956_, lean_object* v_a_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l_Std_Broadcast_subscribe___redArg(v_ch_4956_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_4959_, lean_object* v_ch_4960_){
_start:
{
lean_object* v___x_4962_; 
v___x_4962_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4960_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_object* v_a_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4970_; 
v_a_4963_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4965_ = v___x_4962_;
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_a_4963_);
lean_dec(v___x_4962_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4968_; 
if (v_isShared_4966_ == 0)
{
v___x_4968_ = v___x_4965_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v_a_4963_);
v___x_4968_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
return v___x_4968_;
}
}
}
else
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4978_; 
v_a_4971_ = lean_ctor_get(v___x_4962_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4962_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4973_ = v___x_4962_;
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4962_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4976_; 
if (v_isShared_4974_ == 0)
{
v___x_4976_ = v___x_4973_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4971_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_4979_, lean_object* v_ch_4980_, lean_object* v_a_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Std_Broadcast_subscribe(v_00_u03b1_4979_, v_ch_4980_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_4983_){
_start:
{
lean_object* v___x_4985_; 
v___x_4985_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_4983_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4993_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4988_ = v___x_4985_;
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4985_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
if (v_isShared_4989_ == 0)
{
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4986_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5011_; 
v_a_4994_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_4996_ = v___x_4985_;
v_isShared_4997_ = v_isSharedCheck_5011_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4985_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5011_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
uint8_t v___x_4998_; 
v___x_4998_ = lean_unbox(v_a_4994_);
lean_dec(v_a_4994_);
switch(v___x_4998_)
{
case 0:
{
lean_object* v___x_4999_; lean_object* v___x_5001_; 
v___x_4999_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 0, v___x_4999_);
v___x_5001_ = v___x_4996_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v___x_4999_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
case 1:
{
lean_object* v___x_5003_; lean_object* v___x_5005_; 
v___x_5003_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 0, v___x_5003_);
v___x_5005_ = v___x_4996_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5003_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
default: 
{
lean_object* v___x_5007_; lean_object* v___x_5009_; 
v___x_5007_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 0, v___x_5007_);
v___x_5009_ = v___x_4996_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_5007_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l_Std_Broadcast_close___redArg(v_ch_5012_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5015_, lean_object* v_ch_5016_){
_start:
{
lean_object* v___x_5018_; 
v___x_5018_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5016_);
if (lean_obj_tag(v___x_5018_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
v_a_5019_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_5018_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5044_; 
v_a_5027_ = lean_ctor_get(v___x_5018_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5018_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5029_ = v___x_5018_;
v_isShared_5030_ = v_isSharedCheck_5044_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5018_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5044_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
uint8_t v___x_5031_; 
v___x_5031_ = lean_unbox(v_a_5027_);
lean_dec(v_a_5027_);
switch(v___x_5031_)
{
case 0:
{
lean_object* v___x_5032_; lean_object* v___x_5034_; 
v___x_5032_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5032_);
v___x_5034_ = v___x_5029_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
case 1:
{
lean_object* v___x_5036_; lean_object* v___x_5038_; 
v___x_5036_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5036_);
v___x_5038_ = v___x_5029_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5036_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
default: 
{
lean_object* v___x_5040_; lean_object* v___x_5042_; 
v___x_5040_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5030_ == 0)
{
lean_ctor_set(v___x_5029_, 0, v___x_5040_);
v___x_5042_ = v___x_5029_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v___x_5040_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5045_, lean_object* v_ch_5046_, lean_object* v_a_5047_){
_start:
{
lean_object* v_res_5048_; 
v_res_5048_ = l_Std_Broadcast_close(v_00_u03b1_5045_, v_ch_5046_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5049_){
_start:
{
lean_object* v___y_5052_; 
if (lean_obj_tag(v_x_5049_) == 0)
{
lean_object* v_a_5056_; uint8_t v___x_5057_; 
v_a_5056_ = lean_ctor_get(v_x_5049_, 0);
lean_inc(v_a_5056_);
lean_dec_ref_known(v_x_5049_, 1);
v___x_5057_ = lean_unbox(v_a_5056_);
lean_dec(v_a_5056_);
switch(v___x_5057_)
{
case 0:
{
lean_object* v___x_5058_; 
v___x_5058_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5052_ = v___x_5058_;
goto v___jp_5051_;
}
case 1:
{
lean_object* v___x_5059_; 
v___x_5059_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5052_ = v___x_5059_;
goto v___jp_5051_;
}
default: 
{
lean_object* v___x_5060_; 
v___x_5060_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5052_ = v___x_5060_;
goto v___jp_5051_;
}
}
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5069_; 
v_a_5061_ = lean_ctor_get(v_x_5049_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v_x_5049_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5063_ = v_x_5049_;
v_isShared_5064_ = v_isSharedCheck_5069_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v_x_5049_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5069_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
lean_object* v___x_5067_; 
v___x_5067_ = lean_task_pure(v___x_5066_);
return v___x_5067_;
}
}
}
v___jp_5051_:
{
lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
lean_inc_ref(v___y_5052_);
v___x_5053_ = lean_mk_io_user_error(v___y_5052_);
v___x_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5054_, 0, v___x_5053_);
v___x_5055_ = lean_task_pure(v___x_5054_);
return v___x_5055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5070_, lean_object* v___y_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5070_);
return v_res_5072_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5074_, lean_object* v_v_5075_){
_start:
{
lean_object* v___x_5077_; lean_object* v___f_5078_; lean_object* v___x_5079_; uint8_t v___x_5080_; lean_object* v___x_5081_; 
v___x_5077_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5074_, v_v_5075_);
v___f_5078_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5079_ = lean_unsigned_to_nat(0u);
v___x_5080_ = 1;
v___x_5081_ = lean_io_bind_task(v___x_5077_, v___f_5078_, v___x_5079_, v___x_5080_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5082_, lean_object* v_v_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Std_Broadcast_send___redArg(v_ch_5082_, v_v_5083_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5086_, lean_object* v_ch_5087_, lean_object* v_v_5088_){
_start:
{
lean_object* v___x_5090_; lean_object* v___f_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; lean_object* v___x_5094_; 
v___x_5090_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5087_, v_v_5088_);
v___f_5091_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5092_ = lean_unsigned_to_nat(0u);
v___x_5093_ = 1;
v___x_5094_ = lean_io_bind_task(v___x_5090_, v___f_5091_, v___x_5092_, v___x_5093_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5095_, lean_object* v_ch_5096_, lean_object* v_v_5097_, lean_object* v_a_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l_Std_Broadcast_send(v_00_u03b1_5095_, v_ch_5096_, v_v_5097_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5100_){
_start:
{
lean_object* v___x_5102_; 
v___x_5102_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5100_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5103_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5106_, lean_object* v_ch_5107_){
_start:
{
lean_object* v___x_5109_; 
v___x_5109_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5107_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5110_, lean_object* v_ch_5111_, lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5110_, v_ch_5111_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5114_){
_start:
{
lean_object* v___x_5116_; 
v___x_5116_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5114_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5117_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5120_, lean_object* v_inst_5121_, lean_object* v_ch_5122_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5122_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5125_, lean_object* v_inst_5126_, lean_object* v_ch_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v_res_5129_; 
v_res_5129_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5125_, v_inst_5126_, v_ch_5127_);
lean_dec(v_inst_5126_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5130_){
_start:
{
lean_object* v___x_5131_; 
v___x_5131_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5130_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5132_, lean_object* v_inst_5133_, lean_object* v_ch_5134_){
_start:
{
lean_object* v___x_5135_; 
v___x_5135_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5134_);
return v___x_5135_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5136_, lean_object* v_inst_5137_, lean_object* v_ch_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5136_, v_inst_5137_, v_ch_5138_);
lean_dec(v_inst_5137_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5140_){
_start:
{
lean_object* v___x_5142_; 
v___x_5142_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5140_);
return v___x_5142_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5143_, lean_object* v_a_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5143_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5146_, lean_object* v_ch_5147_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5147_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5150_, lean_object* v_ch_5151_, lean_object* v_a_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5150_, v_ch_5151_);
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5154_, lean_object* v_ch_5155_, lean_object* v_prio_5156_){
_start:
{
lean_object* v___x_5158_; 
v___x_5158_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5154_, v_ch_5155_, v_prio_5156_);
return v___x_5158_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5159_, lean_object* v_ch_5160_, lean_object* v_prio_5161_, lean_object* v_a_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5159_, v_ch_5160_, v_prio_5161_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5164_, lean_object* v_f_5165_, lean_object* v_ch_5166_, lean_object* v_prio_5167_){
_start:
{
lean_object* v___x_5169_; 
v___x_5169_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5165_, v_ch_5166_, v_prio_5167_);
return v___x_5169_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5170_, lean_object* v_f_5171_, lean_object* v_ch_5172_, lean_object* v_prio_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5170_, v_f_5171_, v_ch_5172_, v_prio_5173_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5181_, lean_object* v_inst_5182_){
_start:
{
lean_object* v___x_5183_; 
v___x_5183_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_5183_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5184_, lean_object* v_inst_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5184_, v_inst_5185_);
lean_dec(v_inst_5185_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_5187_){
_start:
{
lean_object* v___x_5188_; 
v___x_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5188_, 0, v_a_5187_);
return v___x_5188_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_5189_, lean_object* v_x_5190_){
_start:
{
if (lean_obj_tag(v_x_5190_) == 0)
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5200_; 
lean_dec_ref(v___f_5189_);
v_a_5192_ = lean_ctor_get(v_x_5190_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v_x_5190_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5194_ = v_x_5190_;
v_isShared_5195_ = v_isSharedCheck_5200_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v_x_5190_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5200_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v___x_5197_; 
if (v_isShared_5195_ == 0)
{
v___x_5197_ = v___x_5194_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5192_);
v___x_5197_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
lean_object* v___x_5198_; 
v___x_5198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
return v___x_5198_;
}
}
}
else
{
lean_object* v_a_5201_; 
v_a_5201_ = lean_ctor_get(v_x_5190_, 0);
lean_inc(v_a_5201_);
lean_dec_ref_known(v_x_5190_, 1);
if (lean_obj_tag(v_a_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5210_; 
lean_dec_ref(v___f_5189_);
v_a_5202_ = lean_ctor_get(v_a_5201_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v_a_5201_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5204_ = v_a_5201_;
v_isShared_5205_ = v_isSharedCheck_5210_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v_a_5201_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5210_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
lean_object* v___x_5208_; 
v___x_5208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5208_, 0, v___x_5207_);
return v___x_5208_;
}
}
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5212_; uint8_t v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v_a_5211_ = lean_ctor_get(v_a_5201_, 0);
lean_inc(v_a_5211_);
lean_dec_ref_known(v_a_5201_, 1);
v___x_5212_ = lean_unsigned_to_nat(0u);
v___x_5213_ = 0;
v___x_5214_ = lean_task_map(v___f_5189_, v_a_5211_, v___x_5212_, v___x_5213_);
v___x_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5215_, 0, v___x_5214_);
return v___x_5215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_5216_, lean_object* v_x_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(v___f_5216_, v_x_5217_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_5220_, lean_object* v_receiver_5221_){
_start:
{
lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; uint8_t v___x_5228_; lean_object* v___x_5229_; 
v___x_5223_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5221_);
v___x_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5224_, 0, v___x_5223_);
v___x_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5224_);
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v___x_5225_);
v___x_5227_ = lean_unsigned_to_nat(0u);
v___x_5228_ = 0;
v___x_5229_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5227_, v___x_5228_, v___x_5226_, v___f_5220_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_5230_, lean_object* v_receiver_5231_, lean_object* v___y_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(v___f_5230_, v_receiver_5231_);
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5239_, lean_object* v_inst_5240_){
_start:
{
lean_object* v___f_5241_; 
v___f_5241_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2));
return v___f_5241_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5242_, lean_object* v_inst_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5242_, v_inst_5243_);
lean_dec(v_inst_5243_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__1(lean_object* v_a_5245_){
_start:
{
lean_object* v___x_5246_; 
v___x_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5246_, 0, v_a_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_5251_, lean_object* v_x_5252_){
_start:
{
if (lean_obj_tag(v_x_5252_) == 0)
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5262_; 
lean_dec_ref(v___f_5251_);
v_a_5254_ = lean_ctor_get(v_x_5252_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v_x_5252_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5256_ = v_x_5252_;
v_isShared_5257_ = v_isSharedCheck_5262_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v_x_5252_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5262_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
lean_object* v___x_5260_; 
v___x_5260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5259_);
return v___x_5260_;
}
}
}
else
{
lean_object* v_a_5263_; lean_object* v___x_5264_; uint8_t v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
v_a_5263_ = lean_ctor_get(v_x_5252_, 0);
lean_inc(v_a_5263_);
lean_dec_ref_known(v_x_5252_, 1);
v___x_5264_ = lean_unsigned_to_nat(0u);
v___x_5265_ = 0;
v___x_5266_ = lean_task_map(v___f_5251_, v_a_5263_, v___x_5264_, v___x_5265_);
v___x_5267_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1));
v___x_5268_ = lean_task_map(v___x_5267_, v___x_5266_, v___x_5264_, v___x_5265_);
v___x_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5269_, 0, v___x_5268_);
return v___x_5269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_5270_, lean_object* v_x_5271_, lean_object* v___y_5272_){
_start:
{
lean_object* v_res_5273_; 
v_res_5273_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(v___f_5270_, v_x_5271_);
return v_res_5273_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5274_, lean_object* v___f_5275_, lean_object* v_receiver_5276_, lean_object* v_x_5277_){
_start:
{
lean_object* v___x_5279_; lean_object* v___x_5280_; uint8_t v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; uint8_t v___x_5285_; lean_object* v___x_5286_; 
v___x_5279_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5276_, v_x_5277_);
v___x_5280_ = lean_unsigned_to_nat(0u);
v___x_5281_ = 1;
v___x_5282_ = lean_io_bind_task(v___x_5279_, v___f_5274_, v___x_5280_, v___x_5281_);
v___x_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5282_);
v___x_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5284_, 0, v___x_5283_);
v___x_5285_ = 0;
v___x_5286_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5280_, v___x_5285_, v___x_5284_, v___f_5275_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5287_, lean_object* v___f_5288_, lean_object* v_receiver_5289_, lean_object* v_x_5290_, lean_object* v___y_5291_){
_start:
{
lean_object* v_res_5292_; 
v_res_5292_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(v___f_5287_, v___f_5288_, v_receiver_5289_, v_x_5290_);
return v_res_5292_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(lean_object* v_x_5293_){
_start:
{
lean_object* v___x_5295_; 
v___x_5295_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5295_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v_x_5296_, lean_object* v___y_5297_){
_start:
{
lean_object* v_res_5298_; 
v_res_5298_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(v_x_5296_);
lean_dec_ref(v_x_5296_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_5299_, lean_object* v_socket_5300_, lean_object* v_x_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v___x_5304_; 
v___x_5304_ = lean_apply_3(v___f_5299_, v_socket_5300_, v___y_5302_, lean_box(0));
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_5305_, lean_object* v_socket_5306_, lean_object* v_x_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(v___f_5305_, v_socket_5306_, v_x_5307_, v___y_5308_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(lean_object* v___f_5311_, lean_object* v___x_5312_, lean_object* v_socket_5313_, lean_object* v_data_5314_){
_start:
{
lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; uint8_t v___x_5319_; 
v___x_5316_ = lean_unsigned_to_nat(0u);
v___x_5317_ = lean_array_get_size(v_data_5314_);
v___x_5318_ = lean_box(0);
v___x_5319_ = lean_nat_dec_lt(v___x_5316_, v___x_5317_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; 
lean_dec_ref(v_data_5314_);
lean_dec_ref(v_socket_5313_);
lean_dec_ref(v___x_5312_);
lean_dec_ref(v___f_5311_);
v___x_5320_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5320_;
}
else
{
lean_object* v___f_5321_; uint8_t v___x_5322_; 
v___f_5321_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5321_, 0, v___f_5311_);
lean_closure_set(v___f_5321_, 1, v_socket_5313_);
v___x_5322_ = lean_nat_dec_le(v___x_5317_, v___x_5317_);
if (v___x_5322_ == 0)
{
if (v___x_5319_ == 0)
{
lean_object* v___x_5323_; 
lean_dec_ref(v___f_5321_);
lean_dec_ref(v_data_5314_);
lean_dec_ref(v___x_5312_);
v___x_5323_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5323_;
}
else
{
size_t v___x_5324_; size_t v___x_5325_; lean_object* v___x_899__overap_5326_; lean_object* v___x_5327_; 
v___x_5324_ = ((size_t)0ULL);
v___x_5325_ = lean_usize_of_nat(v___x_5317_);
v___x_899__overap_5326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5312_, v___f_5321_, v_data_5314_, v___x_5324_, v___x_5325_, v___x_5318_);
v___x_5327_ = lean_apply_1(v___x_899__overap_5326_, lean_box(0));
return v___x_5327_;
}
}
else
{
size_t v___x_5328_; size_t v___x_5329_; lean_object* v___x_902__overap_5330_; lean_object* v___x_5331_; 
v___x_5328_ = ((size_t)0ULL);
v___x_5329_ = lean_usize_of_nat(v___x_5317_);
v___x_902__overap_5330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5312_, v___f_5321_, v_data_5314_, v___x_5328_, v___x_5329_, v___x_5318_);
v___x_5331_ = lean_apply_1(v___x_902__overap_5330_, lean_box(0));
return v___x_5331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed(lean_object* v___f_5332_, lean_object* v___x_5333_, lean_object* v_socket_5334_, lean_object* v_data_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(v___f_5332_, v___x_5333_, v_socket_5334_, v_data_5335_);
return v_res_5337_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_5345_; 
v___x_5345_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_5345_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___x_5346_; lean_object* v___f_5347_; lean_object* v___f_5348_; 
v___x_5346_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4);
v___f_5347_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___f_5348_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed), 5, 2);
lean_closure_set(v___f_5348_, 0, v___f_5347_);
lean_closure_set(v___f_5348_, 1, v___x_5346_);
return v___f_5348_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6(void){
_start:
{
lean_object* v___f_5349_; lean_object* v___f_5350_; lean_object* v___f_5351_; lean_object* v___x_5352_; 
v___f_5349_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3));
v___f_5350_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5);
v___f_5351_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___x_5352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5352_, 0, v___f_5351_);
lean_ctor_set(v___x_5352_, 1, v___f_5350_);
lean_ctor_set(v___x_5352_, 2, v___f_5349_);
return v___x_5352_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5353_, lean_object* v_inst_5354_){
_start:
{
lean_object* v___x_5355_; 
v___x_5355_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6);
return v___x_5355_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5356_, lean_object* v_inst_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5356_, v_inst_5357_);
lean_dec(v_inst_5357_);
return v_res_5358_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5359_; 
v___x_5359_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5360_){
_start:
{
lean_object* v___x_5362_; 
v___x_5362_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5360_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5363_, lean_object* v_a_5364_){
_start:
{
lean_object* v_res_5365_; 
v_res_5365_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5363_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5366_, lean_object* v_capacity_5367_, lean_object* v_h_5368_){
_start:
{
lean_object* v___x_5370_; 
v___x_5370_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5367_);
return v___x_5370_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5371_, lean_object* v_capacity_5372_, lean_object* v_h_5373_, lean_object* v_a_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5371_, v_capacity_5372_, v_h_5373_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5376_, lean_object* v_v_5377_){
_start:
{
lean_object* v___x_5379_; 
v___x_5379_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5376_, v_v_5377_);
return v___x_5379_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5380_, lean_object* v_v_5381_, lean_object* v_a_5382_){
_start:
{
lean_object* v_res_5383_; 
v_res_5383_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5380_, v_v_5381_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5384_, lean_object* v_ch_5385_, lean_object* v_v_5386_){
_start:
{
lean_object* v___x_5388_; 
v___x_5388_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5385_, v_v_5386_);
return v___x_5388_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5389_, lean_object* v_ch_5390_, lean_object* v_v_5391_, lean_object* v_a_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5389_, v_ch_5390_, v_v_5391_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5395_, lean_object* v_v_5396_){
_start:
{
lean_object* v___x_5398_; lean_object* v___f_5399_; lean_object* v___x_5400_; uint8_t v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5398_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5395_, v_v_5396_);
v___f_5399_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5400_ = lean_unsigned_to_nat(0u);
v___x_5401_ = 1;
v___x_5402_ = lean_io_bind_task(v___x_5398_, v___f_5399_, v___x_5400_, v___x_5401_);
v___x_5403_ = lean_io_wait(v___x_5402_);
v___x_5404_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5405_ = l_IO_ofExcept___redArg(v___x_5404_, v___x_5403_);
return v___x_5405_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5406_, lean_object* v_v_5407_, lean_object* v_a_5408_){
_start:
{
lean_object* v_res_5409_; 
v_res_5409_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5406_, v_v_5407_);
return v_res_5409_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5410_, lean_object* v_ch_5411_, lean_object* v_v_5412_){
_start:
{
lean_object* v___x_5414_; lean_object* v___f_5415_; lean_object* v___x_5416_; uint8_t v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5414_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5411_, v_v_5412_);
v___f_5415_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5416_ = lean_unsigned_to_nat(0u);
v___x_5417_ = 1;
v___x_5418_ = lean_io_bind_task(v___x_5414_, v___f_5415_, v___x_5416_, v___x_5417_);
v___x_5419_ = lean_io_wait(v___x_5418_);
v___x_5420_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5421_ = l_IO_ofExcept___redArg(v___x_5420_, v___x_5419_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5422_, lean_object* v_ch_5423_, lean_object* v_v_5424_, lean_object* v_a_5425_){
_start:
{
lean_object* v_res_5426_; 
v_res_5426_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5422_, v_ch_5423_, v_v_5424_);
return v_res_5426_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5427_){
_start:
{
lean_object* v___x_5429_; 
v___x_5429_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5427_);
return v___x_5429_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5430_, lean_object* v_a_5431_){
_start:
{
lean_object* v_res_5432_; 
v_res_5432_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5430_);
return v_res_5432_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5433_, lean_object* v_ch_5434_){
_start:
{
lean_object* v___x_5436_; 
v___x_5436_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5434_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5437_, lean_object* v_ch_5438_, lean_object* v_a_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5437_, v_ch_5438_);
return v_res_5440_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5441_){
_start:
{
lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5443_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5441_);
v___x_5444_ = lean_io_wait(v___x_5443_);
return v___x_5444_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5445_, lean_object* v_a_5446_){
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5445_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5448_, lean_object* v_inst_5449_, lean_object* v_ch_5450_){
_start:
{
lean_object* v___x_5452_; 
v___x_5452_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5450_);
return v___x_5452_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5453_, lean_object* v_inst_5454_, lean_object* v_ch_5455_, lean_object* v_a_5456_){
_start:
{
lean_object* v_res_5457_; 
v_res_5457_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5453_, v_inst_5454_, v_ch_5455_);
lean_dec(v_inst_5454_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5458_, lean_object* v_b_5459_, lean_object* v_f_5460_, lean_object* v_toBind_5461_, lean_object* v___f_5462_, lean_object* v_a_5463_){
_start:
{
if (lean_obj_tag(v_a_5463_) == 0)
{
lean_object* v___x_5464_; 
lean_dec(v___f_5462_);
lean_dec(v_toBind_5461_);
lean_dec(v_f_5460_);
v___x_5464_ = lean_apply_2(v_toPure_5458_, lean_box(0), v_b_5459_);
return v___x_5464_;
}
else
{
lean_object* v_val_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; 
lean_dec(v_toPure_5458_);
v_val_5465_ = lean_ctor_get(v_a_5463_, 0);
lean_inc(v_val_5465_);
lean_dec_ref_known(v_a_5463_, 1);
v___x_5466_ = lean_apply_2(v_f_5460_, v_val_5465_, v_b_5459_);
v___x_5467_ = lean_apply_4(v_toBind_5461_, lean_box(0), lean_box(0), v___x_5466_, v___f_5462_);
return v___x_5467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5468_, lean_object* v_inst_5469_, lean_object* v_inst_5470_, lean_object* v_ch_5471_, lean_object* v_f_5472_, lean_object* v_b_5473_){
_start:
{
lean_object* v_toApplicative_5474_; lean_object* v_toBind_5475_; lean_object* v_toPure_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___f_5479_; lean_object* v___f_5480_; lean_object* v___x_5481_; 
v_toApplicative_5474_ = lean_ctor_get(v_inst_5469_, 0);
v_toBind_5475_ = lean_ctor_get(v_inst_5469_, 1);
lean_inc_n(v_toBind_5475_, 2);
v_toPure_5476_ = lean_ctor_get(v_toApplicative_5474_, 1);
lean_inc_n(v_toPure_5476_, 2);
lean_inc_ref(v_ch_5471_);
lean_inc(v_inst_5468_);
v___x_5477_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5477_, 0, lean_box(0));
lean_closure_set(v___x_5477_, 1, v_inst_5468_);
lean_closure_set(v___x_5477_, 2, v_ch_5471_);
lean_inc(v_inst_5470_);
v___x_5478_ = lean_apply_2(v_inst_5470_, lean_box(0), v___x_5477_);
lean_inc(v_f_5472_);
v___f_5479_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5479_, 0, v_toPure_5476_);
lean_closure_set(v___f_5479_, 1, v_inst_5468_);
lean_closure_set(v___f_5479_, 2, v_inst_5469_);
lean_closure_set(v___f_5479_, 3, v_inst_5470_);
lean_closure_set(v___f_5479_, 4, v_ch_5471_);
lean_closure_set(v___f_5479_, 5, v_f_5472_);
v___f_5480_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5480_, 0, v_toPure_5476_);
lean_closure_set(v___f_5480_, 1, v_b_5473_);
lean_closure_set(v___f_5480_, 2, v_f_5472_);
lean_closure_set(v___f_5480_, 3, v_toBind_5475_);
lean_closure_set(v___f_5480_, 4, v___f_5479_);
v___x_5481_ = lean_apply_4(v_toBind_5475_, lean_box(0), lean_box(0), v___x_5478_, v___f_5480_);
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5482_, lean_object* v_inst_5483_, lean_object* v_inst_5484_, lean_object* v_inst_5485_, lean_object* v_ch_5486_, lean_object* v_f_5487_, lean_object* v_____do__lift_5488_){
_start:
{
if (lean_obj_tag(v_____do__lift_5488_) == 0)
{
lean_object* v_a_5489_; lean_object* v___x_5490_; 
lean_dec(v_f_5487_);
lean_dec_ref(v_ch_5486_);
lean_dec(v_inst_5485_);
lean_dec_ref(v_inst_5484_);
lean_dec(v_inst_5483_);
v_a_5489_ = lean_ctor_get(v_____do__lift_5488_, 0);
lean_inc(v_a_5489_);
lean_dec_ref_known(v_____do__lift_5488_, 1);
v___x_5490_ = lean_apply_2(v_toPure_5482_, lean_box(0), v_a_5489_);
return v___x_5490_;
}
else
{
lean_object* v_a_5491_; lean_object* v___x_5492_; 
lean_dec(v_toPure_5482_);
v_a_5491_ = lean_ctor_get(v_____do__lift_5488_, 0);
lean_inc(v_a_5491_);
lean_dec_ref_known(v_____do__lift_5488_, 1);
v___x_5492_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5483_, v_inst_5484_, v_inst_5485_, v_ch_5486_, v_f_5487_, v_a_5491_);
return v___x_5492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5493_, lean_object* v_m_5494_, lean_object* v_00_u03b2_5495_, lean_object* v_inst_5496_, lean_object* v_inst_5497_, lean_object* v_inst_5498_, lean_object* v_ch_5499_, lean_object* v_f_5500_, lean_object* v_b_5501_){
_start:
{
lean_object* v___x_5502_; 
v___x_5502_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5496_, v_inst_5497_, v_inst_5498_, v_ch_5499_, v_f_5500_, v_b_5501_);
return v___x_5502_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5503_, lean_object* v_inst_5504_, lean_object* v_inst_5505_, lean_object* v_00_u03b2_5506_, lean_object* v_ch_5507_, lean_object* v_b_5508_, lean_object* v_f_5509_){
_start:
{
lean_object* v___x_5510_; 
v___x_5510_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5503_, v_inst_5504_, v_inst_5505_, v_ch_5507_, v_f_5509_, v_b_5508_);
return v___x_5510_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5511_, lean_object* v_inst_5512_, lean_object* v_inst_5513_){
_start:
{
lean_object* v___f_5514_; 
v___f_5514_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5514_, 0, v_inst_5511_);
lean_closure_set(v___f_5514_, 1, v_inst_5512_);
lean_closure_set(v___f_5514_, 2, v_inst_5513_);
return v___f_5514_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5515_, lean_object* v_m_5516_, lean_object* v_inst_5517_, lean_object* v_inst_5518_, lean_object* v_inst_5519_){
_start:
{
lean_object* v___f_5520_; 
v___f_5520_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5520_, 0, v_inst_5517_);
lean_closure_set(v___f_5520_, 1, v_inst_5518_);
lean_closure_set(v___f_5520_, 2, v_inst_5519_);
return v___f_5520_;
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

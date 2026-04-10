// Lean compiler output
// Module: Std.Sync.Broadcast
// Imports: public import Std.Data public import Init.Data.Queue public import Init.Data.Vector public import Std.Sync.Mutex public import Std.Internal.Async.IO
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Std_Internal_IO_Async_EAsync_instMonad(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2_value;
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
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Std_Broadcast_Error_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Std_Broadcast_Error_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Std_Broadcast_Error_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Std_Broadcast_Error_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg(lean_object* v_closed_28_){
_start:
{
lean_inc(v_closed_28_);
return v_closed_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg___boxed(lean_object* v_closed_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Broadcast_Error_closed_elim___redArg(v_closed_29_);
lean_dec(v_closed_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_closed_34_){
_start:
{
lean_inc(v_closed_34_);
return v_closed_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_closed_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Std_Broadcast_Error_closed_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_closed_38_);
lean_dec(v_closed_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg(lean_object* v_alreadyClosed_41_){
_start:
{
lean_inc(v_alreadyClosed_41_);
return v_alreadyClosed_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg___boxed(lean_object* v_alreadyClosed_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_Broadcast_Error_alreadyClosed_elim___redArg(v_alreadyClosed_42_);
lean_dec(v_alreadyClosed_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_alreadyClosed_47_){
_start:
{
lean_inc(v_alreadyClosed_47_);
return v_alreadyClosed_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_alreadyClosed_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Std_Broadcast_Error_alreadyClosed_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_alreadyClosed_51_);
lean_dec(v_alreadyClosed_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg(lean_object* v_notSubscribed_54_){
_start:
{
lean_inc(v_notSubscribed_54_);
return v_notSubscribed_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg___boxed(lean_object* v_notSubscribed_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Broadcast_Error_notSubscribed_elim___redArg(v_notSubscribed_55_);
lean_dec(v_notSubscribed_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_notSubscribed_60_){
_start:
{
lean_inc(v_notSubscribed_60_);
return v_notSubscribed_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_notSubscribed_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Std_Broadcast_Error_notSubscribed_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_notSubscribed_64_);
lean_dec(v_notSubscribed_64_);
return v_res_66_;
}
}
static lean_object* _init_l_Std_Broadcast_instReprError_repr___closed__6(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Broadcast_instReprError_repr___closed__7(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr(uint8_t v_x_80_, lean_object* v_prec_81_){
_start:
{
lean_object* v___y_83_; lean_object* v___y_90_; lean_object* v___y_97_; 
switch(v_x_80_)
{
case 0:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_prec_81_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_83_ = v___x_105_;
goto v___jp_82_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_83_ = v___x_106_;
goto v___jp_82_;
}
}
case 1:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_81_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_90_ = v___x_109_;
goto v___jp_89_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_90_ = v___x_110_;
goto v___jp_89_;
}
}
default: 
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1024u);
v___x_112_ = lean_nat_dec_le(v___x_111_, v_prec_81_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_97_ = v___x_113_;
goto v___jp_96_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_97_ = v___x_114_;
goto v___jp_96_;
}
}
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__1));
lean_inc(v___y_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___y_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = 0;
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_86_);
v___x_88_ = l_Repr_addAppParen(v___x_87_, v_prec_81_);
return v___x_88_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__3));
lean_inc(v___y_90_);
v___x_92_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_92_, 0, v___y_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = 0;
v___x_94_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_93_);
v___x_95_ = l_Repr_addAppParen(v___x_94_, v_prec_81_);
return v___x_95_;
}
v___jp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_98_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__5));
lean_inc(v___y_97_);
v___x_99_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_99_, 0, v___y_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_100_);
v___x_102_ = l_Repr_addAppParen(v___x_101_, v_prec_81_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_177__boxed_117_; lean_object* v_res_118_; 
v_x_177__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Std_Broadcast_instReprError_repr(v_x_177__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
LEAN_EXPORT uint8_t l_Std_Broadcast_Error_ofNat(lean_object* v_n_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_nat_dec_le(v_n_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_dec_le(v_n_121_, v___x_124_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = 2;
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ofNat___boxed(lean_object* v_n_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Std_Broadcast_Error_ofNat(v_n_129_);
lean_dec(v_n_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Std_Broadcast_instDecidableEqError(uint8_t v_x_132_, uint8_t v_y_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_134_ = l_Std_Broadcast_Error_ctorIdx(v_x_132_);
v___x_135_ = l_Std_Broadcast_Error_ctorIdx(v_y_133_);
v___x_136_ = lean_nat_dec_eq(v___x_134_, v___x_135_);
lean_dec(v___x_135_);
lean_dec(v___x_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instDecidableEqError___boxed(lean_object* v_x_137_, lean_object* v_y_138_){
_start:
{
uint8_t v_x_13__boxed_139_; uint8_t v_y_14__boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_x_13__boxed_139_ = lean_unbox(v_x_137_);
v_y_14__boxed_140_ = lean_unbox(v_y_138_);
v_res_141_ = l_Std_Broadcast_instDecidableEqError(v_x_13__boxed_139_, v_y_14__boxed_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint64_t l_Std_Broadcast_instHashableError_hash(uint8_t v_x_143_){
_start:
{
switch(v_x_143_)
{
case 0:
{
uint64_t v___x_144_; 
v___x_144_ = 0ULL;
return v___x_144_;
}
case 1:
{
uint64_t v___x_145_; 
v___x_145_ = 1ULL;
return v___x_145_;
}
default: 
{
uint64_t v___x_146_; 
v___x_146_ = 2ULL;
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instHashableError_hash___boxed(lean_object* v_x_147_){
_start:
{
uint8_t v_x_40__boxed_148_; uint64_t v_res_149_; lean_object* v_r_150_; 
v_x_40__boxed_148_ = lean_unbox(v_x_147_);
v_res_149_ = l_Std_Broadcast_instHashableError_hash(v_x_40__boxed_148_);
v_r_150_ = lean_box_uint64(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0(uint8_t v_x_156_){
_start:
{
switch(v_x_156_)
{
case 0:
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
return v___x_157_;
}
case 1:
{
lean_object* v___x_158_; 
v___x_158_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
return v___x_158_;
}
default: 
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0___boxed(lean_object* v_x_160_){
_start:
{
uint8_t v_x_36__boxed_161_; lean_object* v_res_162_; 
v_x_36__boxed_161_ = lean_unbox(v_x_160_);
v_res_162_ = l_Std_instToStringBroadcastError___lam__0(v_x_36__boxed_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0(lean_object* v_00_u03b1_171_, lean_object* v_x_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_apply_1(v_x_172_, lean_box(0));
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_200_; 
v_a_183_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_200_ == 0)
{
v___x_185_ = v___x_174_;
v_isShared_186_ = v_isSharedCheck_200_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_174_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_200_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
uint8_t v___x_187_; 
v___x_187_ = lean_unbox(v_a_183_);
lean_dec(v_a_183_);
switch(v___x_187_)
{
case 0:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
case 1:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_192_);
v___x_194_ = v___x_185_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
default: 
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_196_);
v___x_198_ = v___x_185_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0___boxed(lean_object* v_00_u03b1_201_, lean_object* v_x_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_instMonadLiftBroadcastIO___lam__0(v_00_u03b1_201_, v_x_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(lean_object* v_c_207_, uint8_t v_b_208_){
_start:
{
lean_object* v_promise_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_promise_210_ = lean_ctor_get(v_c_207_, 0);
v___x_211_ = lean_box(v_b_208_);
v___x_212_ = lean_io_promise_resolve(v___x_211_, v_promise_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg___boxed(lean_object* v_c_213_, lean_object* v_b_214_, lean_object* v_a_215_){
_start:
{
uint8_t v_b_boxed_216_; lean_object* v_res_217_; 
v_b_boxed_216_ = lean_unbox(v_b_214_);
v_res_217_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_213_, v_b_boxed_216_);
lean_dec_ref(v_c_213_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(lean_object* v_00_u03b1_218_, lean_object* v_c_219_, uint8_t v_b_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_219_, v_b_220_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___boxed(lean_object* v_00_u03b1_223_, lean_object* v_c_224_, lean_object* v_b_225_, lean_object* v_a_226_){
_start:
{
uint8_t v_b_boxed_227_; lean_object* v_res_228_; 
v_b_boxed_227_ = lean_unbox(v_b_225_);
v_res_228_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(v_00_u03b1_223_, v_c_224_, v_b_boxed_227_);
lean_dec_ref(v_c_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default(lean_object* v_00_u03b1_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = ((lean_object*)(l_Std_instInhabitedSlot_default___closed__0));
return v___x_233_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_instInhabitedSlot_default(lean_box(0));
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot(lean_object* v_a_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0, &l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0);
return v___x_236_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(9u);
v___x_251_ = lean_nat_to_int(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(7u);
v___x_259_ = lean_nat_to_int(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(13u);
v___x_264_ = lean_nat_to_int(v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0));
v___x_267_ = lean_string_length(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17);
v___x_269_ = lean_nat_to_int(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(lean_object* v_inst_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_value_276_; lean_object* v_pos_277_; lean_object* v_remaining_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_value_276_ = lean_ctor_get(v_x_275_, 0);
lean_inc(v_value_276_);
v_pos_277_ = lean_ctor_get(v_x_275_, 1);
lean_inc(v_pos_277_);
v_remaining_278_ = lean_ctor_get(v_x_275_, 2);
lean_inc(v_remaining_278_);
lean_dec_ref(v_x_275_);
v___x_279_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5));
v___x_280_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__6));
v___x_281_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = l_Option_repr___redArg(v_inst_274_, v_value_276_, v___x_282_);
v___x_284_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_281_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = 0;
v___x_286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*1, v___x_285_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_280_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__9));
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_box(1);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__11));
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v___x_279_);
v___x_295_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12);
v___x_296_ = l_Nat_reprFast(v_pos_277_);
v___x_297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*1, v___x_285_);
v___x_300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_294_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_288_);
v___x_302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_290_);
v___x_303_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__14));
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_279_);
v___x_306_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15);
v___x_307_ = l_Nat_reprFast(v_remaining_278_);
v___x_308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_306_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*1, v___x_285_);
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_305_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18);
v___x_313_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__19));
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_311_);
v___x_315_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__20));
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_312_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*1, v___x_285_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_x_321_, lean_object* v_prec_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(v_inst_320_, v_x_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed(lean_object* v_00_u03b1_324_, lean_object* v_inst_325_, lean_object* v_x_326_, lean_object* v_prec_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(v_00_u03b1_324_, v_inst_325_, v_x_326_, v_prec_327_);
lean_dec(v_prec_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot___redArg(lean_object* v_inst_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_330_, 0, lean_box(0));
lean_closure_set(v___x_330_, 1, v_inst_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot(lean_object* v_00_u03b1_331_, lean_object* v_inst_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_333_, 0, lean_box(0));
lean_closure_set(v___x_333_, 1, v_inst_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10));
v___x_361_ = l_Lean_mkAtom(v___x_360_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12);
v___x_363_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_364_ = lean_array_push(v___x_363_, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__16));
v___x_376_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_377_ = lean_array_push(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_378_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17);
v___x_379_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15));
v___x_380_ = lean_box(2);
v___x_381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
lean_ctor_set(v___x_381_, 2, v___x_378_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18);
v___x_383_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13);
v___x_384_ = lean_array_push(v___x_383_, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19);
v___x_386_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11));
v___x_387_ = lean_box(2);
v___x_388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
lean_ctor_set(v___x_388_, 2, v___x_385_);
return v___x_388_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20);
v___x_390_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_391_ = lean_array_push(v___x_390_, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21);
v___x_393_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9));
v___x_394_ = lean_box(2);
v___x_395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_393_);
lean_ctor_set(v___x_395_, 2, v___x_392_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22);
v___x_397_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_398_ = lean_array_push(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23);
v___x_400_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7));
v___x_401_ = lean_box(2);
v___x_402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
lean_ctor_set(v___x_402_, 2, v___x_399_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24);
v___x_404_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_405_ = lean_array_push(v___x_404_, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25);
v___x_407_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4));
v___x_408_ = lean_box(2);
v___x_409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_406_);
return v___x_409_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(lean_object* v_x_411_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = ((lean_object*)(l_Std_instInhabitedSlot_default___closed__0));
v___x_414_ = lean_st_mk_ref(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(v_x_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(lean_object* v_n_418_, lean_object* v_f_419_, lean_object* v_xs_420_, lean_object* v_k_421_, lean_object* v_acc_422_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = lean_nat_dec_lt(v_k_421_, v_n_418_);
if (v___x_424_ == 0)
{
lean_dec(v_k_421_);
lean_dec_ref(v_f_419_);
return v_acc_422_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_425_ = lean_array_fget_borrowed(v_xs_420_, v_k_421_);
lean_inc_ref(v_f_419_);
lean_inc(v___x_425_);
v___x_426_ = lean_apply_2(v_f_419_, v___x_425_, lean_box(0));
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_k_421_, v___x_427_);
lean_dec(v_k_421_);
v___x_429_ = lean_array_push(v_acc_422_, v___x_426_);
v_k_421_ = v___x_428_;
v_acc_422_ = v___x_429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_431_, lean_object* v_f_432_, lean_object* v_xs_433_, lean_object* v_k_434_, lean_object* v_acc_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_431_, v_f_432_, v_xs_433_, v_k_434_, v_acc_435_);
lean_dec_ref(v_xs_433_);
lean_dec(v_n_431_);
return v_res_437_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2(void){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_Queue_empty(lean_box(0));
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(lean_object* v_capacity_442_){
_start:
{
lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___f_444_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__0));
v___x_445_ = lean_box(0);
lean_inc(v_capacity_442_);
v___x_446_ = lean_mk_array(v_capacity_442_, v___x_445_);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__1));
v___x_449_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_capacity_442_, v___f_444_, v___x_446_, v___x_447_, v___x_448_);
lean_dec_ref(v___x_446_);
v___x_450_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_451_ = lean_box(1);
v___x_452_ = 0;
v___x_453_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_453_, 0, v___x_450_);
lean_ctor_set(v___x_453_, 1, v___x_450_);
lean_ctor_set(v___x_453_, 2, v_capacity_442_);
lean_ctor_set(v___x_453_, 3, v___x_447_);
lean_ctor_set(v___x_453_, 4, v___x_449_);
lean_ctor_set(v___x_453_, 5, v___x_447_);
lean_ctor_set(v___x_453_, 6, v___x_447_);
lean_ctor_set(v___x_453_, 7, v___x_451_);
lean_ctor_set(v___x_453_, 8, v___x_447_);
lean_ctor_set(v___x_453_, 9, v___x_447_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*10, v___x_452_);
v___x_454_ = l_Std_Mutex_new___redArg(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___boxed(lean_object* v_capacity_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new(lean_object* v_00_u03b1_458_, lean_object* v_capacity_459_, lean_object* v_h_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_459_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___boxed(lean_object* v_00_u03b1_463_, lean_object* v_capacity_464_, lean_object* v_h_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new(v_00_u03b1_463_, v_capacity_464_, v_h_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_n_470_, lean_object* v_f_471_, lean_object* v_xs_472_, lean_object* v_k_473_, lean_object* v_h_474_, lean_object* v_acc_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_470_, v_f_471_, v_xs_472_, v_k_473_, v_acc_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_478_, lean_object* v_00_u03b2_479_, lean_object* v_n_480_, lean_object* v_f_481_, lean_object* v_xs_482_, lean_object* v_k_483_, lean_object* v_h_484_, lean_object* v_acc_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(v_00_u03b1_478_, v_00_u03b2_479_, v_n_480_, v_f_481_, v_xs_482_, v_k_483_, v_h_484_, v_acc_485_);
lean_dec_ref(v_xs_482_);
lean_dec(v_n_480_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(lean_object* v_mutex_488_, lean_object* v_k_489_){
_start:
{
lean_object* v_ref_491_; lean_object* v_mutex_492_; lean_object* v___x_493_; lean_object* v_r_494_; 
v_ref_491_ = lean_ctor_get(v_mutex_488_, 0);
lean_inc(v_ref_491_);
v_mutex_492_ = lean_ctor_get(v_mutex_488_, 1);
lean_inc(v_mutex_492_);
lean_dec_ref(v_mutex_488_);
v___x_493_ = lean_io_basemutex_lock(v_mutex_492_);
v_r_494_ = lean_apply_2(v_k_489_, v_ref_491_, lean_box(0));
if (lean_obj_tag(v_r_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_a_495_ = lean_ctor_get(v_r_494_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_r_494_);
if (v_isSharedCheck_503_ == 0)
{
v___x_497_ = v_r_494_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v_r_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_499_ = lean_io_basemutex_unlock(v_mutex_492_);
lean_dec(v_mutex_492_);
if (v_isShared_498_ == 0)
{
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_495_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_a_504_ = lean_ctor_get(v_r_494_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_r_494_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v_r_494_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v_r_494_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_io_basemutex_unlock(v_mutex_492_);
lean_dec(v_mutex_492_);
if (v_isShared_507_ == 0)
{
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_504_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg___boxed(lean_object* v_mutex_513_, lean_object* v_k_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_513_, v_k_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_mutex_519_, lean_object* v_k_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_519_, v_k_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___boxed(lean_object* v_00_u03b1_523_, lean_object* v_00_u03b2_524_, lean_object* v_mutex_525_, lean_object* v_k_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(v_00_u03b1_523_, v_00_u03b2_524_, v_mutex_525_, v_k_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(lean_object* v_k_529_, lean_object* v_v_530_, lean_object* v_t_531_){
_start:
{
if (lean_obj_tag(v_t_531_) == 0)
{
lean_object* v_size_532_; lean_object* v_k_533_; lean_object* v_v_534_; lean_object* v_l_535_; lean_object* v_r_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_817_; 
v_size_532_ = lean_ctor_get(v_t_531_, 0);
v_k_533_ = lean_ctor_get(v_t_531_, 1);
v_v_534_ = lean_ctor_get(v_t_531_, 2);
v_l_535_ = lean_ctor_get(v_t_531_, 3);
v_r_536_ = lean_ctor_get(v_t_531_, 4);
v_isSharedCheck_817_ = !lean_is_exclusive(v_t_531_);
if (v_isSharedCheck_817_ == 0)
{
v___x_538_ = v_t_531_;
v_isShared_539_ = v_isSharedCheck_817_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_r_536_);
lean_inc(v_l_535_);
lean_inc(v_v_534_);
lean_inc(v_k_533_);
lean_inc(v_size_532_);
lean_dec(v_t_531_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_817_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
uint8_t v___x_540_; 
v___x_540_ = lean_nat_dec_lt(v_k_529_, v_k_533_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = lean_nat_dec_eq(v_k_529_, v_k_533_);
if (v___x_541_ == 0)
{
lean_object* v_impl_542_; lean_object* v___x_543_; 
lean_dec(v_size_532_);
v_impl_542_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_529_, v_v_530_, v_r_536_);
v___x_543_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_535_) == 0)
{
lean_object* v_size_544_; lean_object* v_size_545_; lean_object* v_k_546_; lean_object* v_v_547_; lean_object* v_l_548_; lean_object* v_r_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_size_544_ = lean_ctor_get(v_l_535_, 0);
v_size_545_ = lean_ctor_get(v_impl_542_, 0);
lean_inc(v_size_545_);
v_k_546_ = lean_ctor_get(v_impl_542_, 1);
lean_inc(v_k_546_);
v_v_547_ = lean_ctor_get(v_impl_542_, 2);
lean_inc(v_v_547_);
v_l_548_ = lean_ctor_get(v_impl_542_, 3);
lean_inc(v_l_548_);
v_r_549_ = lean_ctor_get(v_impl_542_, 4);
lean_inc(v_r_549_);
v___x_550_ = lean_unsigned_to_nat(3u);
v___x_551_ = lean_nat_mul(v___x_550_, v_size_544_);
v___x_552_ = lean_nat_dec_lt(v___x_551_, v_size_545_);
lean_dec(v___x_551_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
lean_dec(v_r_549_);
lean_dec(v_l_548_);
lean_dec(v_v_547_);
lean_dec(v_k_546_);
v___x_553_ = lean_nat_add(v___x_543_, v_size_544_);
v___x_554_ = lean_nat_add(v___x_553_, v_size_545_);
lean_dec(v_size_545_);
lean_dec(v___x_553_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_impl_542_);
lean_ctor_set(v___x_538_, 0, v___x_554_);
v___x_556_ = v___x_538_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_l_535_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_impl_542_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_621_; 
v_isSharedCheck_621_ = !lean_is_exclusive(v_impl_542_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; lean_object* v_unused_626_; 
v_unused_622_ = lean_ctor_get(v_impl_542_, 4);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_impl_542_, 3);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_impl_542_, 2);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_impl_542_, 1);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v_impl_542_, 0);
lean_dec(v_unused_626_);
v___x_559_ = v_impl_542_;
v_isShared_560_ = v_isSharedCheck_621_;
goto v_resetjp_558_;
}
else
{
lean_dec(v_impl_542_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_621_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_size_561_; lean_object* v_k_562_; lean_object* v_v_563_; lean_object* v_l_564_; lean_object* v_r_565_; lean_object* v_size_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_size_561_ = lean_ctor_get(v_l_548_, 0);
v_k_562_ = lean_ctor_get(v_l_548_, 1);
v_v_563_ = lean_ctor_get(v_l_548_, 2);
v_l_564_ = lean_ctor_get(v_l_548_, 3);
v_r_565_ = lean_ctor_get(v_l_548_, 4);
v_size_566_ = lean_ctor_get(v_r_549_, 0);
v___x_567_ = lean_unsigned_to_nat(2u);
v___x_568_ = lean_nat_mul(v___x_567_, v_size_566_);
v___x_569_ = lean_nat_dec_lt(v_size_561_, v___x_568_);
lean_dec(v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_597_; 
lean_inc(v_r_565_);
lean_inc(v_l_564_);
lean_inc(v_v_563_);
lean_inc(v_k_562_);
v_isSharedCheck_597_ = !lean_is_exclusive(v_l_548_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; lean_object* v_unused_599_; lean_object* v_unused_600_; lean_object* v_unused_601_; lean_object* v_unused_602_; 
v_unused_598_ = lean_ctor_get(v_l_548_, 4);
lean_dec(v_unused_598_);
v_unused_599_ = lean_ctor_get(v_l_548_, 3);
lean_dec(v_unused_599_);
v_unused_600_ = lean_ctor_get(v_l_548_, 2);
lean_dec(v_unused_600_);
v_unused_601_ = lean_ctor_get(v_l_548_, 1);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_l_548_, 0);
lean_dec(v_unused_602_);
v___x_571_ = v_l_548_;
v_isShared_572_ = v_isSharedCheck_597_;
goto v_resetjp_570_;
}
else
{
lean_dec(v_l_548_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_597_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_587_; 
v___x_573_ = lean_nat_add(v___x_543_, v_size_544_);
v___x_574_ = lean_nat_add(v___x_573_, v_size_545_);
lean_dec(v_size_545_);
if (lean_obj_tag(v_l_564_) == 0)
{
lean_object* v_size_595_; 
v_size_595_ = lean_ctor_get(v_l_564_, 0);
lean_inc(v_size_595_);
v___y_587_ = v_size_595_;
goto v___jp_586_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___y_587_ = v___x_596_;
goto v___jp_586_;
}
v___jp_575_:
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = lean_nat_add(v___y_576_, v___y_578_);
lean_dec(v___y_578_);
lean_dec(v___y_576_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 4, v_r_549_);
lean_ctor_set(v___x_571_, 3, v_r_565_);
lean_ctor_set(v___x_571_, 2, v_v_547_);
lean_ctor_set(v___x_571_, 1, v_k_546_);
lean_ctor_set(v___x_571_, 0, v___x_579_);
v___x_581_ = v___x_571_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_k_546_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_v_547_);
lean_ctor_set(v_reuseFailAlloc_585_, 3, v_r_565_);
lean_ctor_set(v_reuseFailAlloc_585_, 4, v_r_549_);
v___x_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 4, v___x_581_);
lean_ctor_set(v___x_559_, 3, v___y_577_);
lean_ctor_set(v___x_559_, 2, v_v_563_);
lean_ctor_set(v___x_559_, 1, v_k_562_);
lean_ctor_set(v___x_559_, 0, v___x_574_);
v___x_583_ = v___x_559_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_k_562_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_v_563_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v___y_577_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
v___jp_586_:
{
lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_588_ = lean_nat_add(v___x_573_, v___y_587_);
lean_dec(v___y_587_);
lean_dec(v___x_573_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_l_564_);
lean_ctor_set(v___x_538_, 0, v___x_588_);
v___x_590_ = v___x_538_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_l_535_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_l_564_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; 
v___x_591_ = lean_nat_add(v___x_543_, v_size_566_);
if (lean_obj_tag(v_r_565_) == 0)
{
lean_object* v_size_592_; 
v_size_592_ = lean_ctor_get(v_r_565_, 0);
lean_inc(v_size_592_);
v___y_576_ = v___x_591_;
v___y_577_ = v___x_590_;
v___y_578_ = v_size_592_;
goto v___jp_575_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___y_576_ = v___x_591_;
v___y_577_ = v___x_590_;
v___y_578_ = v___x_593_;
goto v___jp_575_;
}
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_del_object(v___x_538_);
v___x_603_ = lean_nat_add(v___x_543_, v_size_544_);
v___x_604_ = lean_nat_add(v___x_603_, v_size_545_);
lean_dec(v_size_545_);
v___x_605_ = lean_nat_add(v___x_603_, v_size_561_);
lean_dec(v___x_603_);
lean_inc_ref(v_l_535_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 4, v_l_548_);
lean_ctor_set(v___x_559_, 3, v_l_535_);
lean_ctor_set(v___x_559_, 2, v_v_534_);
lean_ctor_set(v___x_559_, 1, v_k_533_);
lean_ctor_set(v___x_559_, 0, v___x_605_);
v___x_607_ = v___x_559_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_l_535_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_l_548_);
v___x_607_ = v_reuseFailAlloc_620_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_isSharedCheck_614_ = !lean_is_exclusive(v_l_535_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; lean_object* v_unused_616_; lean_object* v_unused_617_; lean_object* v_unused_618_; lean_object* v_unused_619_; 
v_unused_615_ = lean_ctor_get(v_l_535_, 4);
lean_dec(v_unused_615_);
v_unused_616_ = lean_ctor_get(v_l_535_, 3);
lean_dec(v_unused_616_);
v_unused_617_ = lean_ctor_get(v_l_535_, 2);
lean_dec(v_unused_617_);
v_unused_618_ = lean_ctor_get(v_l_535_, 1);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_l_535_, 0);
lean_dec(v_unused_619_);
v___x_609_ = v_l_535_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_dec(v_l_535_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v_r_549_);
lean_ctor_set(v___x_609_, 3, v___x_607_);
lean_ctor_set(v___x_609_, 2, v_v_547_);
lean_ctor_set(v___x_609_, 1, v_k_546_);
lean_ctor_set(v___x_609_, 0, v___x_604_);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_k_546_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_v_547_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_r_549_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_627_; 
v_l_627_ = lean_ctor_get(v_impl_542_, 3);
lean_inc(v_l_627_);
if (lean_obj_tag(v_l_627_) == 0)
{
lean_object* v_r_628_; lean_object* v_k_629_; lean_object* v_v_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_653_; 
v_r_628_ = lean_ctor_get(v_impl_542_, 4);
v_k_629_ = lean_ctor_get(v_impl_542_, 1);
v_v_630_ = lean_ctor_get(v_impl_542_, 2);
v_isSharedCheck_653_ = !lean_is_exclusive(v_impl_542_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; lean_object* v_unused_655_; 
v_unused_654_ = lean_ctor_get(v_impl_542_, 3);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_impl_542_, 0);
lean_dec(v_unused_655_);
v___x_632_ = v_impl_542_;
v_isShared_633_ = v_isSharedCheck_653_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_r_628_);
lean_inc(v_v_630_);
lean_inc(v_k_629_);
lean_dec(v_impl_542_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_653_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_k_634_; lean_object* v_v_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_649_; 
v_k_634_ = lean_ctor_get(v_l_627_, 1);
v_v_635_ = lean_ctor_get(v_l_627_, 2);
v_isSharedCheck_649_ = !lean_is_exclusive(v_l_627_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_650_ = lean_ctor_get(v_l_627_, 4);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_l_627_, 3);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_l_627_, 0);
lean_dec(v_unused_652_);
v___x_637_ = v_l_627_;
v_isShared_638_ = v_isSharedCheck_649_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_v_635_);
lean_inc(v_k_634_);
lean_dec(v_l_627_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_649_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_628_, 2);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 4, v_r_628_);
lean_ctor_set(v___x_637_, 3, v_r_628_);
lean_ctor_set(v___x_637_, 2, v_v_534_);
lean_ctor_set(v___x_637_, 1, v_k_533_);
lean_ctor_set(v___x_637_, 0, v___x_543_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_648_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_648_, 3, v_r_628_);
lean_ctor_set(v_reuseFailAlloc_648_, 4, v_r_628_);
v___x_641_ = v_reuseFailAlloc_648_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_643_; 
lean_inc(v_r_628_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 3, v_r_628_);
lean_ctor_set(v___x_632_, 0, v___x_543_);
v___x_643_ = v___x_632_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_k_629_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_v_630_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_r_628_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_r_628_);
v___x_643_ = v_reuseFailAlloc_647_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v___x_643_);
lean_ctor_set(v___x_538_, 3, v___x_641_);
lean_ctor_set(v___x_538_, 2, v_v_635_);
lean_ctor_set(v___x_538_, 1, v_k_634_);
lean_ctor_set(v___x_538_, 0, v___x_639_);
v___x_645_ = v___x_538_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_k_634_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_v_635_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_646_, 4, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
else
{
lean_object* v_r_656_; 
v_r_656_ = lean_ctor_get(v_impl_542_, 4);
lean_inc(v_r_656_);
if (lean_obj_tag(v_r_656_) == 0)
{
lean_object* v_k_657_; lean_object* v_v_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_669_; 
v_k_657_ = lean_ctor_get(v_impl_542_, 1);
v_v_658_ = lean_ctor_get(v_impl_542_, 2);
v_isSharedCheck_669_ = !lean_is_exclusive(v_impl_542_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; lean_object* v_unused_672_; 
v_unused_670_ = lean_ctor_get(v_impl_542_, 4);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_impl_542_, 3);
lean_dec(v_unused_671_);
v_unused_672_ = lean_ctor_get(v_impl_542_, 0);
lean_dec(v_unused_672_);
v___x_660_ = v_impl_542_;
v_isShared_661_ = v_isSharedCheck_669_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_v_658_);
lean_inc(v_k_657_);
lean_dec(v_impl_542_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_669_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(3u);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 4, v_l_627_);
lean_ctor_set(v___x_660_, 2, v_v_534_);
lean_ctor_set(v___x_660_, 1, v_k_533_);
lean_ctor_set(v___x_660_, 0, v___x_543_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_l_627_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_l_627_);
v___x_664_ = v_reuseFailAlloc_668_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_666_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_r_656_);
lean_ctor_set(v___x_538_, 3, v___x_664_);
lean_ctor_set(v___x_538_, 2, v_v_658_);
lean_ctor_set(v___x_538_, 1, v_k_657_);
lean_ctor_set(v___x_538_, 0, v___x_662_);
v___x_666_ = v___x_538_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_657_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_v_658_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_r_656_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_unsigned_to_nat(2u);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_impl_542_);
lean_ctor_set(v___x_538_, 3, v_r_656_);
lean_ctor_set(v___x_538_, 0, v___x_673_);
v___x_675_ = v___x_538_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_r_656_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_impl_542_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v___x_678_; 
lean_dec(v_v_534_);
lean_dec(v_k_533_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 2, v_v_530_);
lean_ctor_set(v___x_538_, 1, v_k_529_);
v___x_678_ = v___x_538_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_size_532_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_k_529_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_v_530_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_l_535_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_r_536_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
lean_object* v_impl_680_; lean_object* v___x_681_; 
lean_dec(v_size_532_);
v_impl_680_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_529_, v_v_530_, v_l_535_);
v___x_681_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_536_) == 0)
{
lean_object* v_size_682_; lean_object* v_size_683_; lean_object* v_k_684_; lean_object* v_v_685_; lean_object* v_l_686_; lean_object* v_r_687_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_size_682_ = lean_ctor_get(v_r_536_, 0);
v_size_683_ = lean_ctor_get(v_impl_680_, 0);
lean_inc(v_size_683_);
v_k_684_ = lean_ctor_get(v_impl_680_, 1);
lean_inc(v_k_684_);
v_v_685_ = lean_ctor_get(v_impl_680_, 2);
lean_inc(v_v_685_);
v_l_686_ = lean_ctor_get(v_impl_680_, 3);
lean_inc(v_l_686_);
v_r_687_ = lean_ctor_get(v_impl_680_, 4);
lean_inc(v_r_687_);
v___x_688_ = lean_unsigned_to_nat(3u);
v___x_689_ = lean_nat_mul(v___x_688_, v_size_682_);
v___x_690_ = lean_nat_dec_lt(v___x_689_, v_size_683_);
lean_dec(v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
lean_dec(v_r_687_);
lean_dec(v_l_686_);
lean_dec(v_v_685_);
lean_dec(v_k_684_);
v___x_691_ = lean_nat_add(v___x_681_, v_size_683_);
lean_dec(v_size_683_);
v___x_692_ = lean_nat_add(v___x_691_, v_size_682_);
lean_dec(v___x_691_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 3, v_impl_680_);
lean_ctor_set(v___x_538_, 0, v___x_692_);
v___x_694_ = v___x_538_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_impl_680_);
lean_ctor_set(v_reuseFailAlloc_695_, 4, v_r_536_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
else
{
lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_761_; 
v_isSharedCheck_761_ = !lean_is_exclusive(v_impl_680_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; lean_object* v_unused_763_; lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; 
v_unused_762_ = lean_ctor_get(v_impl_680_, 4);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_impl_680_, 3);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_impl_680_, 2);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_impl_680_, 1);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_impl_680_, 0);
lean_dec(v_unused_766_);
v___x_697_ = v_impl_680_;
v_isShared_698_ = v_isSharedCheck_761_;
goto v_resetjp_696_;
}
else
{
lean_dec(v_impl_680_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_761_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_size_699_; lean_object* v_size_700_; lean_object* v_k_701_; lean_object* v_v_702_; lean_object* v_l_703_; lean_object* v_r_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_size_699_ = lean_ctor_get(v_l_686_, 0);
v_size_700_ = lean_ctor_get(v_r_687_, 0);
v_k_701_ = lean_ctor_get(v_r_687_, 1);
v_v_702_ = lean_ctor_get(v_r_687_, 2);
v_l_703_ = lean_ctor_get(v_r_687_, 3);
v_r_704_ = lean_ctor_get(v_r_687_, 4);
v___x_705_ = lean_unsigned_to_nat(2u);
v___x_706_ = lean_nat_mul(v___x_705_, v_size_699_);
v___x_707_ = lean_nat_dec_lt(v_size_700_, v___x_706_);
lean_dec(v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_736_; 
lean_inc(v_r_704_);
lean_inc(v_l_703_);
lean_inc(v_v_702_);
lean_inc(v_k_701_);
v_isSharedCheck_736_ = !lean_is_exclusive(v_r_687_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; lean_object* v_unused_738_; lean_object* v_unused_739_; lean_object* v_unused_740_; lean_object* v_unused_741_; 
v_unused_737_ = lean_ctor_get(v_r_687_, 4);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_r_687_, 3);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_r_687_, 2);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_r_687_, 1);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_r_687_, 0);
lean_dec(v_unused_741_);
v___x_709_ = v_r_687_;
v_isShared_710_ = v_isSharedCheck_736_;
goto v_resetjp_708_;
}
else
{
lean_dec(v_r_687_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_736_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___x_724_; lean_object* v___y_726_; 
v___x_711_ = lean_nat_add(v___x_681_, v_size_683_);
lean_dec(v_size_683_);
v___x_712_ = lean_nat_add(v___x_711_, v_size_682_);
lean_dec(v___x_711_);
v___x_724_ = lean_nat_add(v___x_681_, v_size_699_);
if (lean_obj_tag(v_l_703_) == 0)
{
lean_object* v_size_734_; 
v_size_734_ = lean_ctor_get(v_l_703_, 0);
lean_inc(v_size_734_);
v___y_726_ = v_size_734_;
goto v___jp_725_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = lean_unsigned_to_nat(0u);
v___y_726_ = v___x_735_;
goto v___jp_725_;
}
v___jp_713_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_nat_add(v___y_714_, v___y_716_);
lean_dec(v___y_716_);
lean_dec(v___y_714_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 4, v_r_536_);
lean_ctor_set(v___x_709_, 3, v_r_704_);
lean_ctor_set(v___x_709_, 2, v_v_534_);
lean_ctor_set(v___x_709_, 1, v_k_533_);
lean_ctor_set(v___x_709_, 0, v___x_717_);
v___x_719_ = v___x_709_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_r_704_);
lean_ctor_set(v_reuseFailAlloc_723_, 4, v_r_536_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 4, v___x_719_);
lean_ctor_set(v___x_697_, 3, v___y_715_);
lean_ctor_set(v___x_697_, 2, v_v_702_);
lean_ctor_set(v___x_697_, 1, v_k_701_);
lean_ctor_set(v___x_697_, 0, v___x_712_);
v___x_721_ = v___x_697_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_k_701_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_v_702_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v___y_715_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_nat_add(v___x_724_, v___y_726_);
lean_dec(v___y_726_);
lean_dec(v___x_724_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_l_703_);
lean_ctor_set(v___x_538_, 3, v_l_686_);
lean_ctor_set(v___x_538_, 2, v_v_685_);
lean_ctor_set(v___x_538_, 1, v_k_684_);
lean_ctor_set(v___x_538_, 0, v___x_727_);
v___x_729_ = v___x_538_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_k_684_);
lean_ctor_set(v_reuseFailAlloc_733_, 2, v_v_685_);
lean_ctor_set(v_reuseFailAlloc_733_, 3, v_l_686_);
lean_ctor_set(v_reuseFailAlloc_733_, 4, v_l_703_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; 
v___x_730_ = lean_nat_add(v___x_681_, v_size_682_);
if (lean_obj_tag(v_r_704_) == 0)
{
lean_object* v_size_731_; 
v_size_731_ = lean_ctor_get(v_r_704_, 0);
lean_inc(v_size_731_);
v___y_714_ = v___x_730_;
v___y_715_ = v___x_729_;
v___y_716_ = v_size_731_;
goto v___jp_713_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___y_714_ = v___x_730_;
v___y_715_ = v___x_729_;
v___y_716_ = v___x_732_;
goto v___jp_713_;
}
}
}
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
lean_del_object(v___x_538_);
v___x_742_ = lean_nat_add(v___x_681_, v_size_683_);
lean_dec(v_size_683_);
v___x_743_ = lean_nat_add(v___x_742_, v_size_682_);
lean_dec(v___x_742_);
v___x_744_ = lean_nat_add(v___x_681_, v_size_682_);
v___x_745_ = lean_nat_add(v___x_744_, v_size_700_);
lean_dec(v___x_744_);
lean_inc_ref(v_r_536_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 4, v_r_536_);
lean_ctor_set(v___x_697_, 3, v_r_687_);
lean_ctor_set(v___x_697_, 2, v_v_534_);
lean_ctor_set(v___x_697_, 1, v_k_533_);
lean_ctor_set(v___x_697_, 0, v___x_745_);
v___x_747_ = v___x_697_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_r_687_);
lean_ctor_set(v_reuseFailAlloc_760_, 4, v_r_536_);
v___x_747_ = v_reuseFailAlloc_760_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_isSharedCheck_754_ = !lean_is_exclusive(v_r_536_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; lean_object* v_unused_756_; lean_object* v_unused_757_; lean_object* v_unused_758_; lean_object* v_unused_759_; 
v_unused_755_ = lean_ctor_get(v_r_536_, 4);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_r_536_, 3);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_r_536_, 2);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_r_536_, 1);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_r_536_, 0);
lean_dec(v_unused_759_);
v___x_749_ = v_r_536_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_r_536_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 4, v___x_747_);
lean_ctor_set(v___x_749_, 3, v_l_686_);
lean_ctor_set(v___x_749_, 2, v_v_685_);
lean_ctor_set(v___x_749_, 1, v_k_684_);
lean_ctor_set(v___x_749_, 0, v___x_743_);
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_k_684_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_v_685_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_l_686_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v___x_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_767_; 
v_l_767_ = lean_ctor_get(v_impl_680_, 3);
lean_inc(v_l_767_);
if (lean_obj_tag(v_l_767_) == 0)
{
lean_object* v_r_768_; lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_781_; 
v_r_768_ = lean_ctor_get(v_impl_680_, 4);
v_k_769_ = lean_ctor_get(v_impl_680_, 1);
v_v_770_ = lean_ctor_get(v_impl_680_, 2);
v_isSharedCheck_781_ = !lean_is_exclusive(v_impl_680_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; lean_object* v_unused_783_; 
v_unused_782_ = lean_ctor_get(v_impl_680_, 3);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_impl_680_, 0);
lean_dec(v_unused_783_);
v___x_772_ = v_impl_680_;
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_r_768_);
lean_inc(v_v_770_);
lean_inc(v_k_769_);
lean_dec(v_impl_680_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_768_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 3, v_r_768_);
lean_ctor_set(v___x_772_, 2, v_v_534_);
lean_ctor_set(v___x_772_, 1, v_k_533_);
lean_ctor_set(v___x_772_, 0, v___x_681_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v_r_768_);
lean_ctor_set(v_reuseFailAlloc_780_, 4, v_r_768_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v___x_776_);
lean_ctor_set(v___x_538_, 3, v_l_767_);
lean_ctor_set(v___x_538_, 2, v_v_770_);
lean_ctor_set(v___x_538_, 1, v_k_769_);
lean_ctor_set(v___x_538_, 0, v___x_774_);
v___x_778_ = v___x_538_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_769_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_770_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_r_784_; 
v_r_784_ = lean_ctor_get(v_impl_680_, 4);
lean_inc(v_r_784_);
if (lean_obj_tag(v_r_784_) == 0)
{
lean_object* v_k_785_; lean_object* v_v_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_809_; 
v_k_785_ = lean_ctor_get(v_impl_680_, 1);
v_v_786_ = lean_ctor_get(v_impl_680_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_impl_680_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_810_ = lean_ctor_get(v_impl_680_, 4);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_impl_680_, 3);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_impl_680_, 0);
lean_dec(v_unused_812_);
v___x_788_ = v_impl_680_;
v_isShared_789_ = v_isSharedCheck_809_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_v_786_);
lean_inc(v_k_785_);
lean_dec(v_impl_680_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_809_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_k_790_; lean_object* v_v_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_805_; 
v_k_790_ = lean_ctor_get(v_r_784_, 1);
v_v_791_ = lean_ctor_get(v_r_784_, 2);
v_isSharedCheck_805_ = !lean_is_exclusive(v_r_784_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; lean_object* v_unused_807_; lean_object* v_unused_808_; 
v_unused_806_ = lean_ctor_get(v_r_784_, 4);
lean_dec(v_unused_806_);
v_unused_807_ = lean_ctor_get(v_r_784_, 3);
lean_dec(v_unused_807_);
v_unused_808_ = lean_ctor_get(v_r_784_, 0);
lean_dec(v_unused_808_);
v___x_793_ = v_r_784_;
v_isShared_794_ = v_isSharedCheck_805_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_v_791_);
lean_inc(v_k_790_);
lean_dec(v_r_784_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_805_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = lean_unsigned_to_nat(3u);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 4, v_l_767_);
lean_ctor_set(v___x_793_, 3, v_l_767_);
lean_ctor_set(v___x_793_, 2, v_v_786_);
lean_ctor_set(v___x_793_, 1, v_k_785_);
lean_ctor_set(v___x_793_, 0, v___x_681_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_k_785_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_v_786_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v_l_767_);
v___x_797_ = v_reuseFailAlloc_804_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_799_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 4, v_l_767_);
lean_ctor_set(v___x_788_, 2, v_v_534_);
lean_ctor_set(v___x_788_, 1, v_k_533_);
lean_ctor_set(v___x_788_, 0, v___x_681_);
v___x_799_ = v___x_788_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v_l_767_);
lean_ctor_set(v_reuseFailAlloc_803_, 4, v_l_767_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v___x_799_);
lean_ctor_set(v___x_538_, 3, v___x_797_);
lean_ctor_set(v___x_538_, 2, v_v_791_);
lean_ctor_set(v___x_538_, 1, v_k_790_);
lean_ctor_set(v___x_538_, 0, v___x_795_);
v___x_801_ = v___x_538_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_k_790_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_v_791_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_unsigned_to_nat(2u);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v_r_784_);
lean_ctor_set(v___x_538_, 3, v_impl_680_);
lean_ctor_set(v___x_538_, 0, v___x_813_);
v___x_815_ = v___x_538_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_impl_680_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_r_784_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v_k_529_);
lean_ctor_set(v___x_819_, 2, v_v_530_);
lean_ctor_set(v___x_819_, 3, v_t_531_);
lean_ctor_set(v___x_819_, 4, v_t_531_);
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_producers_823_; lean_object* v_waiters_824_; lean_object* v_capacity_825_; lean_object* v_size_826_; lean_object* v_buffer_827_; lean_object* v_write_828_; lean_object* v_read_829_; lean_object* v_receivers_830_; lean_object* v_nextId_831_; uint8_t v_closed_832_; lean_object* v_pos_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_845_; 
v___x_822_ = lean_st_ref_take(v___y_820_);
v_producers_823_ = lean_ctor_get(v___x_822_, 0);
v_waiters_824_ = lean_ctor_get(v___x_822_, 1);
v_capacity_825_ = lean_ctor_get(v___x_822_, 2);
v_size_826_ = lean_ctor_get(v___x_822_, 3);
v_buffer_827_ = lean_ctor_get(v___x_822_, 4);
v_write_828_ = lean_ctor_get(v___x_822_, 5);
v_read_829_ = lean_ctor_get(v___x_822_, 6);
v_receivers_830_ = lean_ctor_get(v___x_822_, 7);
v_nextId_831_ = lean_ctor_get(v___x_822_, 8);
v_closed_832_ = lean_ctor_get_uint8(v___x_822_, sizeof(void*)*10);
v_pos_833_ = lean_ctor_get(v___x_822_, 9);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_845_ == 0)
{
v___x_835_ = v___x_822_;
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_pos_833_);
lean_inc(v_nextId_831_);
lean_inc(v_receivers_830_);
lean_inc(v_read_829_);
lean_inc(v_write_828_);
lean_inc(v_buffer_827_);
lean_inc(v_size_826_);
lean_inc(v_capacity_825_);
lean_inc(v_waiters_824_);
lean_inc(v_producers_823_);
lean_dec(v___x_822_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
lean_inc(v_pos_833_);
lean_inc(v_nextId_831_);
v___x_837_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_nextId_831_, v_pos_833_, v_receivers_830_);
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_add(v_nextId_831_, v___x_838_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 8, v___x_839_);
lean_ctor_set(v___x_835_, 7, v___x_837_);
v___x_841_ = v___x_835_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_producers_823_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_waiters_824_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v_capacity_825_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v_size_826_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v_buffer_827_);
lean_ctor_set(v_reuseFailAlloc_844_, 5, v_write_828_);
lean_ctor_set(v_reuseFailAlloc_844_, 6, v_read_829_);
lean_ctor_set(v_reuseFailAlloc_844_, 7, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_844_, 8, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_844_, 9, v_pos_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_844_, sizeof(void*)*10, v_closed_832_);
v___x_841_ = v_reuseFailAlloc_844_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_st_ref_set(v___y_820_, v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v_nextId_831_);
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0___boxed(lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(v___y_846_);
lean_dec(v___y_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(lean_object* v_bd_850_){
_start:
{
lean_object* v___f_852_; lean_object* v___x_853_; 
v___f_852_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___closed__0));
lean_inc_ref(v_bd_850_);
v___x_853_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_bd_850_, v___f_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_862_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_bd_850_);
lean_ctor_set(v___x_858_, 1, v_a_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v_bd_850_);
v_a_863_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_853_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_853_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___boxed(lean_object* v_bd_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(lean_object* v_00_u03b1_874_, lean_object* v_bd_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___boxed(lean_object* v_00_u03b1_878_, lean_object* v_bd_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(v_00_u03b1_878_, v_bd_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0(lean_object* v_00_u03b2_882_, lean_object* v_k_883_, lean_object* v_v_884_, lean_object* v_t_885_, lean_object* v_hl_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_883_, v_v_884_, v_t_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(lean_object* v_toApplicative_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_size_890_; lean_object* v_toPure_891_; lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_size_890_ = lean_ctor_get(v_a_889_, 3);
v_toPure_891_ = lean_ctor_get(v_toApplicative_888_, 1);
lean_inc(v_toPure_891_);
lean_dec_ref(v_toApplicative_888_);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_nat_dec_eq(v_size_890_, v___x_892_);
v___x_894_ = lean_box(v___x_893_);
v___x_895_ = lean_apply_2(v_toPure_891_, lean_box(0), v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed(lean_object* v_toApplicative_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(v_toApplicative_896_, v_a_897_);
lean_dec_ref(v_a_897_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_toApplicative_902_; lean_object* v_toBind_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_toApplicative_902_ = lean_ctor_get(v_inst_899_, 0);
lean_inc_ref(v_toApplicative_902_);
v_toBind_903_ = lean_ctor_get(v_inst_899_, 1);
lean_inc(v_toBind_903_);
lean_dec_ref(v_inst_899_);
v___f_904_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_904_, 0, v_toApplicative_902_);
lean_inc(v_a_901_);
v___x_905_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_905_, 0, lean_box(0));
lean_closure_set(v___x_905_, 1, lean_box(0));
lean_closure_set(v___x_905_, 2, v_a_901_);
v___x_906_ = lean_apply_2(v_inst_900_, lean_box(0), v___x_905_);
v___x_907_ = lean_apply_4(v_toBind_903_, lean_box(0), lean_box(0), v___x_906_, v___f_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___boxed(lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_908_, v_inst_909_, v_a_910_);
lean_dec(v_a_910_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(lean_object* v_m_912_, lean_object* v_00_u03b1_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_914_, v_inst_915_, v_a_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___boxed(lean_object* v_m_918_, lean_object* v_00_u03b1_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(v_m_918_, v_00_u03b1_919_, v_inst_920_, v_inst_921_, v_a_922_);
lean_dec(v_a_922_);
return v_res_923_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(lean_object* v_a_924_){
_start:
{
lean_object* v___x_926_; lean_object* v_capacity_927_; lean_object* v_size_928_; uint8_t v___x_929_; 
v___x_926_ = lean_st_ref_get(v_a_924_);
v_capacity_927_ = lean_ctor_get(v___x_926_, 2);
lean_inc(v_capacity_927_);
v_size_928_ = lean_ctor_get(v___x_926_, 3);
lean_inc(v_size_928_);
lean_dec(v___x_926_);
v___x_929_ = lean_nat_dec_le(v_capacity_927_, v_size_928_);
lean_dec(v_size_928_);
lean_dec(v_capacity_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg___boxed(lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
uint8_t v_res_932_; lean_object* v_r_933_; 
v_res_932_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_930_);
lean_dec(v_a_930_);
v_r_933_ = lean_box(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(lean_object* v_00_u03b1_934_, lean_object* v_a_935_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___boxed(lean_object* v_00_u03b1_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(v_00_u03b1_938_, v_a_939_);
lean_dec(v_a_939_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(lean_object* v_value_943_, lean_object* v_st_944_){
_start:
{
lean_object* v_producers_946_; lean_object* v_waiters_947_; lean_object* v_capacity_948_; lean_object* v_size_949_; lean_object* v_buffer_950_; lean_object* v_write_951_; lean_object* v_read_952_; lean_object* v_receivers_953_; lean_object* v_nextId_954_; uint8_t v_closed_955_; lean_object* v_pos_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_976_; 
v_producers_946_ = lean_ctor_get(v_st_944_, 0);
v_waiters_947_ = lean_ctor_get(v_st_944_, 1);
v_capacity_948_ = lean_ctor_get(v_st_944_, 2);
v_size_949_ = lean_ctor_get(v_st_944_, 3);
v_buffer_950_ = lean_ctor_get(v_st_944_, 4);
v_write_951_ = lean_ctor_get(v_st_944_, 5);
v_read_952_ = lean_ctor_get(v_st_944_, 6);
v_receivers_953_ = lean_ctor_get(v_st_944_, 7);
v_nextId_954_ = lean_ctor_get(v_st_944_, 8);
v_closed_955_ = lean_ctor_get_uint8(v_st_944_, sizeof(void*)*10);
v_pos_956_ = lean_ctor_get(v_st_944_, 9);
v_isSharedCheck_976_ = !lean_is_exclusive(v_st_944_);
if (v_isSharedCheck_976_ == 0)
{
v___x_958_ = v_st_944_;
v_isShared_959_ = v_isSharedCheck_976_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_pos_956_);
lean_inc(v_nextId_954_);
lean_inc(v_receivers_953_);
lean_inc(v_read_952_);
lean_inc(v_write_951_);
lean_inc(v_buffer_950_);
lean_inc(v_size_949_);
lean_inc(v_capacity_948_);
lean_inc(v_waiters_947_);
lean_inc(v_producers_946_);
lean_dec(v_st_944_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_976_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_tailRef_960_; lean_object* v___x_961_; lean_object* v___y_963_; 
v_tailRef_960_ = lean_array_fget_borrowed(v_buffer_950_, v_write_951_);
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v_value_943_);
if (lean_obj_tag(v_receivers_953_) == 0)
{
lean_object* v_size_974_; 
v_size_974_ = lean_ctor_get(v_receivers_953_, 0);
lean_inc(v_size_974_);
v___y_963_ = v_size_974_;
goto v___jp_962_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = lean_unsigned_to_nat(0u);
v___y_963_ = v___x_975_;
goto v___jp_962_;
}
v___jp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
lean_inc(v_pos_956_);
v___x_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_964_, 0, v___x_961_);
lean_ctor_set(v___x_964_, 1, v_pos_956_);
lean_ctor_set(v___x_964_, 2, v___y_963_);
v___x_965_ = lean_st_ref_set(v_tailRef_960_, v___x_964_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_write_951_, v___x_966_);
lean_dec(v_write_951_);
v___x_968_ = lean_nat_mod(v___x_967_, v_capacity_948_);
lean_dec(v___x_967_);
v___x_969_ = lean_nat_add(v_size_949_, v___x_966_);
lean_dec(v_size_949_);
v___x_970_ = lean_nat_add(v_pos_956_, v___x_966_);
lean_dec(v_pos_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 9, v___x_970_);
lean_ctor_set(v___x_958_, 5, v___x_968_);
lean_ctor_set(v___x_958_, 3, v___x_969_);
v___x_972_ = v___x_958_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_producers_946_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_waiters_947_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_capacity_948_);
lean_ctor_set(v_reuseFailAlloc_973_, 3, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_973_, 4, v_buffer_950_);
lean_ctor_set(v_reuseFailAlloc_973_, 5, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_973_, 6, v_read_952_);
lean_ctor_set(v_reuseFailAlloc_973_, 7, v_receivers_953_);
lean_ctor_set(v_reuseFailAlloc_973_, 8, v_nextId_954_);
lean_ctor_set(v_reuseFailAlloc_973_, 9, v___x_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*10, v_closed_955_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg___boxed(lean_object* v_value_977_, lean_object* v_st_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_977_, v_st_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(lean_object* v_00_u03b1_981_, lean_object* v_value_982_, lean_object* v_st_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_982_, v_st_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___boxed(lean_object* v_00_u03b1_986_, lean_object* v_value_987_, lean_object* v_st_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(v_00_u03b1_986_, v_value_987_, v_st_988_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(lean_object* v_st_991_){
_start:
{
lean_object* v_producers_992_; lean_object* v_waiters_993_; lean_object* v_capacity_994_; lean_object* v_size_995_; lean_object* v_buffer_996_; lean_object* v_write_997_; lean_object* v_read_998_; lean_object* v_receivers_999_; lean_object* v_nextId_1000_; uint8_t v_closed_1001_; lean_object* v_pos_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1013_; 
v_producers_992_ = lean_ctor_get(v_st_991_, 0);
v_waiters_993_ = lean_ctor_get(v_st_991_, 1);
v_capacity_994_ = lean_ctor_get(v_st_991_, 2);
v_size_995_ = lean_ctor_get(v_st_991_, 3);
v_buffer_996_ = lean_ctor_get(v_st_991_, 4);
v_write_997_ = lean_ctor_get(v_st_991_, 5);
v_read_998_ = lean_ctor_get(v_st_991_, 6);
v_receivers_999_ = lean_ctor_get(v_st_991_, 7);
v_nextId_1000_ = lean_ctor_get(v_st_991_, 8);
v_closed_1001_ = lean_ctor_get_uint8(v_st_991_, sizeof(void*)*10);
v_pos_1002_ = lean_ctor_get(v_st_991_, 9);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_st_991_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1004_ = v_st_991_;
v_isShared_1005_ = v_isSharedCheck_1013_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_pos_1002_);
lean_inc(v_nextId_1000_);
lean_inc(v_receivers_999_);
lean_inc(v_read_998_);
lean_inc(v_write_997_);
lean_inc(v_buffer_996_);
lean_inc(v_size_995_);
lean_inc(v_capacity_994_);
lean_inc(v_waiters_993_);
lean_inc(v_producers_992_);
lean_dec(v_st_991_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1013_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v_size_1007_; lean_object* v___x_1008_; lean_object* v_read_1009_; lean_object* v___x_1011_; 
v___x_1006_ = lean_unsigned_to_nat(1u);
v_size_1007_ = lean_nat_sub(v_size_995_, v___x_1006_);
lean_dec(v_size_995_);
v___x_1008_ = lean_nat_add(v_read_998_, v___x_1006_);
lean_dec(v_read_998_);
v_read_1009_ = lean_nat_mod(v___x_1008_, v_capacity_994_);
lean_dec(v___x_1008_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 6, v_read_1009_);
lean_ctor_set(v___x_1004_, 3, v_size_1007_);
v___x_1011_ = v___x_1004_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_producers_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_waiters_993_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_capacity_994_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_size_1007_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_buffer_996_);
lean_ctor_set(v_reuseFailAlloc_1012_, 5, v_write_997_);
lean_ctor_set(v_reuseFailAlloc_1012_, 6, v_read_1009_);
lean_ctor_set(v_reuseFailAlloc_1012_, 7, v_receivers_999_);
lean_ctor_set(v_reuseFailAlloc_1012_, 8, v_nextId_1000_);
lean_ctor_set(v_reuseFailAlloc_1012_, 9, v_pos_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1012_, sizeof(void*)*10, v_closed_1001_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue(lean_object* v_00_u03b1_1014_, lean_object* v_st_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_st_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(lean_object* v_toApplicative_1017_, lean_object* v_place_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_capacity_1020_; lean_object* v_buffer_1021_; lean_object* v_toPure_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_capacity_1020_ = lean_ctor_get(v_a_1019_, 2);
v_buffer_1021_ = lean_ctor_get(v_a_1019_, 4);
v_toPure_1022_ = lean_ctor_get(v_toApplicative_1017_, 1);
lean_inc(v_toPure_1022_);
lean_dec_ref(v_toApplicative_1017_);
v___x_1023_ = lean_nat_mod(v_place_1018_, v_capacity_1020_);
v___x_1024_ = lean_array_fget_borrowed(v_buffer_1021_, v___x_1023_);
lean_dec(v___x_1023_);
lean_inc(v___x_1024_);
v___x_1025_ = lean_apply_2(v_toPure_1022_, lean_box(0), v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed(lean_object* v_toApplicative_1026_, lean_object* v_place_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(v_toApplicative_1026_, v_place_1027_, v_a_1028_);
lean_dec_ref(v_a_1028_);
lean_dec(v_place_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(lean_object* v_inst_1030_, lean_object* v_inst_1031_, lean_object* v_place_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_toApplicative_1034_; lean_object* v_toBind_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_toApplicative_1034_ = lean_ctor_get(v_inst_1030_, 0);
lean_inc_ref(v_toApplicative_1034_);
v_toBind_1035_ = lean_ctor_get(v_inst_1030_, 1);
lean_inc(v_toBind_1035_);
lean_dec_ref(v_inst_1030_);
v___f_1036_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1036_, 0, v_toApplicative_1034_);
lean_closure_set(v___f_1036_, 1, v_place_1032_);
lean_inc(v_a_1033_);
v___x_1037_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1037_, 0, lean_box(0));
lean_closure_set(v___x_1037_, 1, lean_box(0));
lean_closure_set(v___x_1037_, 2, v_a_1033_);
v___x_1038_ = lean_apply_2(v_inst_1031_, lean_box(0), v___x_1037_);
v___x_1039_ = lean_apply_4(v_toBind_1035_, lean_box(0), lean_box(0), v___x_1038_, v___f_1036_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___boxed(lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_place_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1040_, v_inst_1041_, v_place_1042_, v_a_1043_);
lean_dec(v_a_1043_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(lean_object* v_m_1045_, lean_object* v_00_u03b1_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_place_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1047_, v_inst_1048_, v_place_1049_, v_a_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___boxed(lean_object* v_m_1052_, lean_object* v_00_u03b1_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_place_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(v_m_1052_, v_00_u03b1_1053_, v_inst_1054_, v_inst_1055_, v_place_1056_, v_a_1057_);
lean_dec(v_a_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(lean_object* v_as_1059_, size_t v_sz_1060_, size_t v_i_1061_, lean_object* v_b_1062_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_usize_dec_lt(v_i_1061_, v_sz_1060_);
if (v___x_1064_ == 0)
{
return v_b_1062_;
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; 
v_a_1065_ = lean_array_uget_borrowed(v_as_1059_, v_i_1061_);
v___x_1066_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1065_, v___x_1064_);
v___x_1067_ = lean_box(0);
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_add(v_i_1061_, v___x_1068_);
v_i_1061_ = v___x_1069_;
v_b_1062_ = v___x_1067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg___boxed(lean_object* v_as_1071_, lean_object* v_sz_1072_, lean_object* v_i_1073_, lean_object* v_b_1074_, lean_object* v___y_1075_){
_start:
{
size_t v_sz_boxed_1076_; size_t v_i_boxed_1077_; lean_object* v_res_1078_; 
v_sz_boxed_1076_ = lean_unbox_usize(v_sz_1072_);
lean_dec(v_sz_1072_);
v_i_boxed_1077_ = lean_unbox_usize(v_i_1073_);
lean_dec(v_i_1073_);
v_res_1078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1071_, v_sz_boxed_1076_, v_i_boxed_1077_, v_b_1074_);
lean_dec_ref(v_as_1071_);
return v_res_1078_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Std_Queue_empty(lean_box(0));
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(lean_object* v_v_1080_, lean_object* v_a_1081_){
_start:
{
uint8_t v___x_1083_; 
v___x_1083_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_1081_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_producers_1086_; lean_object* v_waiters_1087_; lean_object* v_capacity_1088_; lean_object* v_size_1089_; lean_object* v_buffer_1090_; lean_object* v_write_1091_; lean_object* v_read_1092_; lean_object* v_receivers_1093_; lean_object* v_nextId_1094_; uint8_t v_closed_1095_; lean_object* v_pos_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1115_; 
v___x_1084_ = lean_st_ref_get(v_a_1081_);
v___x_1085_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_v_1080_, v___x_1084_);
v_producers_1086_ = lean_ctor_get(v___x_1085_, 0);
v_waiters_1087_ = lean_ctor_get(v___x_1085_, 1);
v_capacity_1088_ = lean_ctor_get(v___x_1085_, 2);
v_size_1089_ = lean_ctor_get(v___x_1085_, 3);
v_buffer_1090_ = lean_ctor_get(v___x_1085_, 4);
v_write_1091_ = lean_ctor_get(v___x_1085_, 5);
v_read_1092_ = lean_ctor_get(v___x_1085_, 6);
v_receivers_1093_ = lean_ctor_get(v___x_1085_, 7);
v_nextId_1094_ = lean_ctor_get(v___x_1085_, 8);
v_closed_1095_ = lean_ctor_get_uint8(v___x_1085_, sizeof(void*)*10);
v_pos_1096_ = lean_ctor_get(v___x_1085_, 9);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1098_ = v___x_1085_;
v_isShared_1099_ = v_isSharedCheck_1115_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_pos_1096_);
lean_inc(v_nextId_1094_);
lean_inc(v_receivers_1093_);
lean_inc(v_read_1092_);
lean_inc(v_write_1091_);
lean_inc(v_buffer_1090_);
lean_inc(v_size_1089_);
lean_inc(v_capacity_1088_);
lean_inc(v_waiters_1087_);
lean_inc(v_producers_1086_);
lean_dec(v___x_1085_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1115_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1100_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0);
lean_inc(v_receivers_1093_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1100_);
v___x_1102_ = v___x_1098_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_producers_1086_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_capacity_1088_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_size_1089_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_buffer_1090_);
lean_ctor_set(v_reuseFailAlloc_1114_, 5, v_write_1091_);
lean_ctor_set(v_reuseFailAlloc_1114_, 6, v_read_1092_);
lean_ctor_set(v_reuseFailAlloc_1114_, 7, v_receivers_1093_);
lean_ctor_set(v_reuseFailAlloc_1114_, 8, v_nextId_1094_);
lean_ctor_set(v_reuseFailAlloc_1114_, 9, v_pos_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*10, v_closed_1095_);
v___x_1102_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; size_t v_sz_1106_; size_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___y_1110_; 
v___x_1103_ = lean_st_ref_set(v_a_1081_, v___x_1102_);
v___x_1104_ = l_Std_Queue_toArray___redArg(v_waiters_1087_);
v___x_1105_ = lean_box(0);
v_sz_1106_ = lean_array_size(v___x_1104_);
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v___x_1104_, v_sz_1106_, v___x_1107_, v___x_1105_);
lean_dec_ref(v___x_1104_);
if (lean_obj_tag(v_receivers_1093_) == 0)
{
lean_object* v_size_1112_; 
v_size_1112_ = lean_ctor_get(v_receivers_1093_, 0);
lean_inc(v_size_1112_);
lean_dec_ref(v_receivers_1093_);
v___y_1110_ = v_size_1112_;
goto v___jp_1109_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___y_1110_ = v___x_1113_;
goto v___jp_1109_;
}
v___jp_1109_:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___y_1110_);
return v___x_1111_;
}
}
}
}
else
{
lean_object* v___x_1116_; 
lean_dec(v_v_1080_);
v___x_1116_ = lean_box(0);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1117_, v_a_1118_);
lean_dec(v_a_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(lean_object* v_00_u03b1_1121_, lean_object* v_v_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1122_, v_a_1123_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_1126_, lean_object* v_v_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(v_00_u03b1_1126_, v_v_1127_, v_a_1128_);
lean_dec(v_a_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(lean_object* v_00_u03b1_1131_, lean_object* v_as_1132_, size_t v_sz_1133_, size_t v_i_1134_, lean_object* v_b_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1132_, v_sz_1133_, v_i_1134_, v_b_1135_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_as_1140_, lean_object* v_sz_1141_, lean_object* v_i_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
size_t v_sz_boxed_1146_; size_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_sz_boxed_1146_ = lean_unbox_usize(v_sz_1141_);
lean_dec(v_sz_1141_);
v_i_boxed_1147_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(v_00_u03b1_1139_, v_as_1140_, v_sz_boxed_1146_, v_i_boxed_1147_, v_b_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v_as_1140_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(lean_object* v_mutex_1149_, lean_object* v_k_1150_){
_start:
{
lean_object* v_ref_1152_; lean_object* v_mutex_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_ref_1152_ = lean_ctor_get(v_mutex_1149_, 0);
lean_inc(v_ref_1152_);
v_mutex_1153_ = lean_ctor_get(v_mutex_1149_, 1);
lean_inc(v_mutex_1153_);
lean_dec_ref(v_mutex_1149_);
v___x_1154_ = lean_io_basemutex_lock(v_mutex_1153_);
v___x_1155_ = lean_apply_2(v_k_1150_, v_ref_1152_, lean_box(0));
v___x_1156_ = lean_io_basemutex_unlock(v_mutex_1153_);
lean_dec(v_mutex_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg___boxed(lean_object* v_mutex_1157_, lean_object* v_k_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1157_, v_k_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(lean_object* v_00_u03b1_1161_, lean_object* v_00_u03b2_1162_, lean_object* v_mutex_1163_, lean_object* v_k_1164_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1163_, v_k_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_1167_, lean_object* v_00_u03b2_1168_, lean_object* v_mutex_1169_, lean_object* v_k_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(v_00_u03b1_1167_, v_00_u03b2_1168_, v_mutex_1169_, v_k_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(lean_object* v_v_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; uint8_t v_closed_1179_; 
v___x_1178_ = lean_st_ref_get(v___y_1176_);
v_closed_1179_ = lean_ctor_get_uint8(v___x_1178_, sizeof(void*)*10);
lean_dec(v___x_1178_);
if (v_closed_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v_receivers_1181_; 
v___x_1180_ = lean_st_ref_get(v___y_1176_);
v_receivers_1181_ = lean_ctor_get(v___x_1180_, 7);
lean_inc(v_receivers_1181_);
lean_dec(v___x_1180_);
if (lean_obj_tag(v_receivers_1181_) == 0)
{
lean_object* v___x_1182_; 
lean_dec_ref(v_receivers_1181_);
v___x_1182_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1175_, v___y_1176_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; 
lean_dec(v_v_1175_);
v___x_1183_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0));
return v___x_1183_;
}
}
else
{
lean_object* v___x_1184_; 
lean_dec(v_v_1175_);
v___x_1184_ = lean_box(0);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(v_v_1185_, v___y_1186_);
lean_dec(v___y_1186_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(lean_object* v_ch_1189_, lean_object* v_v_1190_){
_start:
{
lean_object* v___f_1192_; lean_object* v___x_1193_; 
v___f_1192_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1192_, 0, v_v_1190_);
v___x_1193_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1189_, v___f_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___boxed(lean_object* v_ch_1194_, lean_object* v_v_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1194_, v_v_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(lean_object* v_00_u03b1_1198_, lean_object* v_ch_1199_, lean_object* v_v_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1199_, v_v_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_ch_1204_, lean_object* v_v_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(v_00_u03b1_1203_, v_ch_1204_, v_v_1205_);
return v_res_1207_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0));
v___x_1211_ = lean_task_pure(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2));
v___x_1216_ = lean_task_pure(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(lean_object* v_v_1217_, lean_object* v___f_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; uint8_t v_closed_1222_; 
v___x_1221_ = lean_st_ref_get(v___y_1219_);
v_closed_1222_ = lean_ctor_get_uint8(v___x_1221_, sizeof(void*)*10);
lean_dec(v___x_1221_);
if (v_closed_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v_receivers_1224_; 
v___x_1223_ = lean_st_ref_get(v___y_1219_);
v_receivers_1224_ = lean_ctor_get(v___x_1223_, 7);
lean_inc(v_receivers_1224_);
lean_dec(v___x_1223_);
if (lean_obj_tag(v_receivers_1224_) == 0)
{
lean_object* v___x_1225_; 
lean_dec_ref(v_receivers_1224_);
v___x_1225_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1217_, v___y_1219_);
if (lean_obj_tag(v___x_1225_) == 1)
{
lean_object* v_val_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v___f_1218_);
v_val_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_val_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_val_1226_);
v___x_1231_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_task_pure(v___x_1231_);
return v___x_1232_;
}
}
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_producers_1237_; lean_object* v_waiters_1238_; lean_object* v_capacity_1239_; lean_object* v_size_1240_; lean_object* v_buffer_1241_; lean_object* v_write_1242_; lean_object* v_read_1243_; lean_object* v_receivers_1244_; lean_object* v_nextId_1245_; uint8_t v_closed_1246_; lean_object* v_pos_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v___x_1225_);
v___x_1235_ = lean_io_promise_new();
v___x_1236_ = lean_st_ref_take(v___y_1219_);
v_producers_1237_ = lean_ctor_get(v___x_1236_, 0);
v_waiters_1238_ = lean_ctor_get(v___x_1236_, 1);
v_capacity_1239_ = lean_ctor_get(v___x_1236_, 2);
v_size_1240_ = lean_ctor_get(v___x_1236_, 3);
v_buffer_1241_ = lean_ctor_get(v___x_1236_, 4);
v_write_1242_ = lean_ctor_get(v___x_1236_, 5);
v_read_1243_ = lean_ctor_get(v___x_1236_, 6);
v_receivers_1244_ = lean_ctor_get(v___x_1236_, 7);
v_nextId_1245_ = lean_ctor_get(v___x_1236_, 8);
v_closed_1246_ = lean_ctor_get_uint8(v___x_1236_, sizeof(void*)*10);
v_pos_1247_ = lean_ctor_get(v___x_1236_, 9);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1249_ = v___x_1236_;
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_pos_1247_);
lean_inc(v_nextId_1245_);
lean_inc(v_receivers_1244_);
lean_inc(v_read_1243_);
lean_inc(v_write_1242_);
lean_inc(v_buffer_1241_);
lean_inc(v_size_1240_);
lean_inc(v_capacity_1239_);
lean_inc(v_waiters_1238_);
lean_inc(v_producers_1237_);
lean_dec(v___x_1236_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
lean_inc(v___x_1235_);
v___x_1251_ = l_Std_Queue_enqueue___redArg(v___x_1235_, v_producers_1237_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_waiters_1238_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_capacity_1239_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_size_1240_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_buffer_1241_);
lean_ctor_set(v_reuseFailAlloc_1258_, 5, v_write_1242_);
lean_ctor_set(v_reuseFailAlloc_1258_, 6, v_read_1243_);
lean_ctor_set(v_reuseFailAlloc_1258_, 7, v_receivers_1244_);
lean_ctor_set(v_reuseFailAlloc_1258_, 8, v_nextId_1245_);
lean_ctor_set(v_reuseFailAlloc_1258_, 9, v_pos_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1258_, sizeof(void*)*10, v_closed_1246_);
v___x_1253_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1254_ = lean_st_ref_set(v___y_1219_, v___x_1253_);
v___x_1255_ = lean_io_promise_result_opt(v___x_1235_);
lean_dec(v___x_1235_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_io_bind_task(v___x_1255_, v___f_1218_, v___x_1256_, v_closed_1222_);
return v___x_1257_;
}
}
}
}
else
{
lean_object* v___x_1260_; 
lean_dec_ref(v___f_1218_);
lean_dec(v_v_1217_);
v___x_1260_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1);
return v___x_1260_;
}
}
else
{
lean_object* v___x_1261_; 
lean_dec_ref(v___f_1218_);
lean_dec(v_v_1217_);
v___x_1261_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_1262_, lean_object* v___f_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(v_v_1262_, v___f_1263_, v___y_1264_);
lean_dec(v___y_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(lean_object* v_ch_1267_, lean_object* v_v_1268_, lean_object* v_res_1269_){
_start:
{
if (lean_obj_tag(v_res_1269_) == 0)
{
lean_dec(v_v_1268_);
lean_dec_ref(v_ch_1267_);
goto v___jp_1271_;
}
else
{
lean_object* v_val_1273_; uint8_t v___x_1274_; 
v_val_1273_ = lean_ctor_get(v_res_1269_, 0);
v___x_1274_ = lean_unbox(v_val_1273_);
if (v___x_1274_ == 0)
{
lean_dec(v_v_1268_);
lean_dec_ref(v_ch_1267_);
goto v___jp_1271_;
}
else
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1267_, v_v_1268_);
return v___x_1275_;
}
}
v___jp_1271_:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_1276_, lean_object* v_v_1277_, lean_object* v_res_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(v_ch_1276_, v_v_1277_, v_res_1278_);
lean_dec(v_res_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(lean_object* v_ch_1281_, lean_object* v_v_1282_){
_start:
{
lean_object* v___f_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; 
lean_inc(v_v_1282_);
lean_inc_ref(v_ch_1281_);
v___f_1284_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1284_, 0, v_ch_1281_);
lean_closure_set(v___f_1284_, 1, v_v_1282_);
v___f_1285_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1285_, 0, v_v_1282_);
lean_closure_set(v___f_1285_, 1, v___f_1284_);
v___x_1286_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1281_, v___f_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___boxed(lean_object* v_ch_1287_, lean_object* v_v_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1287_, v_v_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send(lean_object* v_00_u03b1_1291_, lean_object* v_ch_1292_, lean_object* v_v_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1292_, v_v_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___boxed(lean_object* v_00_u03b1_1296_, lean_object* v_ch_1297_, lean_object* v_v_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send(v_00_u03b1_1296_, v_ch_1297_, v_v_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(lean_object* v_mutex_1301_, lean_object* v_k_1302_){
_start:
{
lean_object* v_ref_1304_; lean_object* v_mutex_1305_; lean_object* v___x_1306_; lean_object* v_r_1307_; 
v_ref_1304_ = lean_ctor_get(v_mutex_1301_, 0);
lean_inc(v_ref_1304_);
v_mutex_1305_ = lean_ctor_get(v_mutex_1301_, 1);
lean_inc(v_mutex_1305_);
lean_dec_ref(v_mutex_1301_);
v___x_1306_ = lean_io_basemutex_lock(v_mutex_1305_);
v_r_1307_ = lean_apply_2(v_k_1302_, v_ref_1304_, lean_box(0));
if (lean_obj_tag(v_r_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_a_1308_ = lean_ctor_get(v_r_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_r_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v_r_1307_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v_r_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_io_basemutex_unlock(v_mutex_1305_);
lean_dec(v_mutex_1305_);
if (v_isShared_1311_ == 0)
{
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1308_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1325_; 
v_a_1317_ = lean_ctor_get(v_r_1307_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_r_1307_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1319_ = v_r_1307_;
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v_r_1307_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1325_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_io_basemutex_unlock(v_mutex_1305_);
lean_dec(v_mutex_1305_);
if (v_isShared_1320_ == 0)
{
v___x_1323_ = v___x_1319_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1317_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object* v_mutex_1326_, lean_object* v_k_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_mutex_1326_, v_k_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object* v_00_u03b1_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_mutex_1332_, lean_object* v_k_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_mutex_1332_, v_k_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_1336_, lean_object* v_00_u03b2_1337_, lean_object* v_mutex_1338_, lean_object* v_k_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(v_00_u03b1_1336_, v_00_u03b2_1337_, v_mutex_1338_, v_k_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(uint8_t v___x_1342_, lean_object* v_as_1343_, size_t v_sz_1344_, size_t v_i_1345_, lean_object* v_b_1346_){
_start:
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_usize_dec_lt(v_i_1345_, v_sz_1344_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_b_1346_);
return v___x_1349_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; size_t v___x_1353_; size_t v___x_1354_; 
v_a_1350_ = lean_array_uget_borrowed(v_as_1343_, v_i_1345_);
v___x_1351_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1350_, v___x_1342_);
v___x_1352_ = lean_box(0);
v___x_1353_ = ((size_t)1ULL);
v___x_1354_ = lean_usize_add(v_i_1345_, v___x_1353_);
v_i_1345_ = v___x_1354_;
v_b_1346_ = v___x_1352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_1356_, lean_object* v_as_1357_, lean_object* v_sz_1358_, lean_object* v_i_1359_, lean_object* v_b_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v___x_1416__boxed_1362_; size_t v_sz_boxed_1363_; size_t v_i_boxed_1364_; lean_object* v_res_1365_; 
v___x_1416__boxed_1362_ = lean_unbox(v___x_1356_);
v_sz_boxed_1363_ = lean_unbox_usize(v_sz_1358_);
lean_dec(v_sz_1358_);
v_i_boxed_1364_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1416__boxed_1362_, v_as_1357_, v_sz_boxed_1363_, v_i_boxed_1364_, v_b_1360_);
lean_dec_ref(v_as_1357_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; uint8_t v_closed_1369_; 
v___x_1368_ = lean_st_ref_get(v___y_1366_);
v_closed_1369_ = lean_ctor_get_uint8(v___x_1368_, sizeof(void*)*10);
if (v_closed_1369_ == 0)
{
lean_object* v_producers_1370_; lean_object* v_waiters_1371_; lean_object* v_capacity_1372_; lean_object* v_size_1373_; lean_object* v_buffer_1374_; lean_object* v_write_1375_; lean_object* v_read_1376_; lean_object* v_receivers_1377_; lean_object* v_nextId_1378_; lean_object* v_pos_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1402_; 
v_producers_1370_ = lean_ctor_get(v___x_1368_, 0);
v_waiters_1371_ = lean_ctor_get(v___x_1368_, 1);
v_capacity_1372_ = lean_ctor_get(v___x_1368_, 2);
v_size_1373_ = lean_ctor_get(v___x_1368_, 3);
v_buffer_1374_ = lean_ctor_get(v___x_1368_, 4);
v_write_1375_ = lean_ctor_get(v___x_1368_, 5);
v_read_1376_ = lean_ctor_get(v___x_1368_, 6);
v_receivers_1377_ = lean_ctor_get(v___x_1368_, 7);
v_nextId_1378_ = lean_ctor_get(v___x_1368_, 8);
v_pos_1379_ = lean_ctor_get(v___x_1368_, 9);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1381_ = v___x_1368_;
v_isShared_1382_ = v_isSharedCheck_1402_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_pos_1379_);
lean_inc(v_nextId_1378_);
lean_inc(v_receivers_1377_);
lean_inc(v_read_1376_);
lean_inc(v_write_1375_);
lean_inc(v_buffer_1374_);
lean_inc(v_size_1373_);
lean_inc(v_capacity_1372_);
lean_inc(v_waiters_1371_);
lean_inc(v_producers_1370_);
lean_dec(v___x_1368_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1402_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; size_t v_sz_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1383_ = l_Std_Queue_toArray___redArg(v_waiters_1371_);
v___x_1384_ = lean_box(0);
v_sz_1385_ = lean_array_size(v___x_1383_);
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v_closed_1369_, v___x_1383_, v_sz_1385_, v___x_1386_, v___x_1384_);
lean_dec_ref(v___x_1383_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1387_, 0);
lean_dec(v_unused_1401_);
v___x_1389_ = v___x_1387_;
v_isShared_1390_ = v_isSharedCheck_1400_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v___x_1387_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1400_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1394_; 
v___x_1391_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0);
v___x_1392_ = 1;
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1391_);
v___x_1394_ = v___x_1381_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_producers_1370_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_capacity_1372_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_size_1373_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_buffer_1374_);
lean_ctor_set(v_reuseFailAlloc_1399_, 5, v_write_1375_);
lean_ctor_set(v_reuseFailAlloc_1399_, 6, v_read_1376_);
lean_ctor_set(v_reuseFailAlloc_1399_, 7, v_receivers_1377_);
lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_nextId_1378_);
lean_ctor_set(v_reuseFailAlloc_1399_, 9, v_pos_1379_);
v___x_1394_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*10, v___x_1392_);
v___x_1395_ = lean_st_ref_set(v___y_1366_, v___x_1394_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1384_);
v___x_1397_ = v___x_1389_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1384_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_del_object(v___x_1381_);
lean_dec(v_pos_1379_);
lean_dec(v_nextId_1378_);
lean_dec(v_receivers_1377_);
lean_dec(v_read_1376_);
lean_dec(v_write_1375_);
lean_dec_ref(v_buffer_1374_);
lean_dec(v_size_1373_);
lean_dec(v_capacity_1372_);
lean_dec_ref(v_producers_1370_);
return v___x_1387_;
}
}
}
else
{
uint8_t v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v___x_1368_);
v___x_1403_ = 1;
v___x_1404_ = lean_box(v___x_1403_);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(v___y_1406_);
lean_dec(v___y_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(lean_object* v_ch_1410_){
_start:
{
lean_object* v___f_1412_; lean_object* v___x_1413_; 
v___f_1412_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0));
v___x_1413_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_ch_1410_, v___f_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___boxed(lean_object* v_ch_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_object* v_00_u03b1_1417_, lean_object* v_ch_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_ch_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close(v_00_u03b1_1421_, v_ch_1422_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_object* v_00_u03b1_1425_, uint8_t v___x_1426_, lean_object* v_as_1427_, size_t v_sz_1428_, size_t v_i_1429_, lean_object* v_b_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1426_, v_as_1427_, v_sz_1428_, v_i_1429_, v_b_1430_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_1434_, lean_object* v___x_1435_, lean_object* v_as_1436_, lean_object* v_sz_1437_, lean_object* v_i_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v___x_1512__boxed_1442_; size_t v_sz_boxed_1443_; size_t v_i_boxed_1444_; lean_object* v_res_1445_; 
v___x_1512__boxed_1442_ = lean_unbox(v___x_1435_);
v_sz_boxed_1443_ = lean_unbox_usize(v_sz_1437_);
lean_dec(v_sz_1437_);
v_i_boxed_1444_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1434_, v___x_1512__boxed_1442_, v_as_1436_, v_sz_boxed_1443_, v_i_boxed_1444_, v_b_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v_as_1436_);
return v_res_1445_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; uint8_t v_closed_1449_; 
v___x_1448_ = lean_st_ref_get(v___y_1446_);
v_closed_1449_ = lean_ctor_get_uint8(v___x_1448_, sizeof(void*)*10);
lean_dec(v___x_1448_);
return v_closed_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
uint8_t v_res_1452_; lean_object* v_r_1453_; 
v_res_1452_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(v___y_1450_);
lean_dec(v___y_1450_);
v_r_1453_ = lean_box(v_res_1452_);
return v_r_1453_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object* v_ch_1455_){
_start:
{
lean_object* v___f_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___f_1457_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0));
v___x_1458_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1455_, v___f_1457_);
v___x_1459_ = lean_unbox(v___x_1458_);
lean_dec(v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___boxed(lean_object* v_ch_1460_, lean_object* v_a_1461_){
_start:
{
uint8_t v_res_1462_; lean_object* v_r_1463_; 
v_res_1462_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1460_);
v_r_1463_ = lean_box(v_res_1462_);
return v_r_1463_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_object* v_00_u03b1_1464_, lean_object* v_ch_1465_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_ch_1469_, lean_object* v_a_1470_){
_start:
{
uint8_t v_res_1471_; lean_object* v_r_1472_; 
v_res_1471_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(v_00_u03b1_1468_, v_ch_1469_);
v_r_1472_ = lean_box(v_res_1471_);
return v_r_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object* v_next_1473_, lean_object* v_slot_1474_){
_start:
{
lean_object* v_value_1475_; lean_object* v_pos_1476_; lean_object* v_remaining_1477_; uint8_t v___x_1478_; 
v_value_1475_ = lean_ctor_get(v_slot_1474_, 0);
v_pos_1476_ = lean_ctor_get(v_slot_1474_, 1);
v_remaining_1477_ = lean_ctor_get(v_slot_1474_, 2);
v___x_1478_ = lean_nat_dec_eq(v_next_1473_, v_pos_1476_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_box(v___x_1478_);
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_slot_1474_);
return v___x_1482_;
}
else
{
lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1503_; 
lean_inc(v_remaining_1477_);
lean_inc(v_pos_1476_);
lean_inc(v_value_1475_);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_slot_1474_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; 
v_unused_1504_ = lean_ctor_get(v_slot_1474_, 2);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_slot_1474_, 1);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_slot_1474_, 0);
lean_dec(v_unused_1506_);
v___x_1484_ = v_slot_1474_;
v_isShared_1485_ = v_isSharedCheck_1503_;
goto v_resetjp_1483_;
}
else
{
lean_dec(v_slot_1474_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1503_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_dec_eq(v_remaining_1477_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1488_ = lean_box(v___x_1487_);
lean_inc(v_value_1475_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_value_1475_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_nat_sub(v_remaining_1477_, v___x_1486_);
lean_dec(v_remaining_1477_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 2, v___x_1490_);
v___x_1492_ = v___x_1484_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_value_1475_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_pos_1476_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1489_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
return v___x_1493_;
}
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_dec(v_remaining_1477_);
v___x_1495_ = lean_box(v___x_1478_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_value_1475_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_unsigned_to_nat(0u);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 2, v___x_1498_);
lean_ctor_set(v___x_1484_, 0, v___x_1497_);
v___x_1500_ = v___x_1484_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_pos_1476_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1496_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
return v___x_1501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object* v_next_1507_, lean_object* v_slot_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(v_next_1507_, v_slot_1508_);
lean_dec(v_next_1507_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object* v_inst_1510_, lean_object* v_slot_1511_, lean_object* v_next_1512_){
_start:
{
lean_object* v___f_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___f_1513_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1513_, 0, v_next_1512_);
v___x_1514_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1514_, 0, lean_box(0));
lean_closure_set(v___x_1514_, 1, lean_box(0));
lean_closure_set(v___x_1514_, 2, lean_box(0));
lean_closure_set(v___x_1514_, 3, v_slot_1511_);
lean_closure_set(v___x_1514_, 4, v___f_1513_);
v___x_1515_ = lean_apply_2(v_inst_1510_, lean_box(0), v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object* v_m_1516_, lean_object* v_00_u03b1_1517_, lean_object* v_inst_1518_, lean_object* v_inst_1519_, lean_object* v_slot_1520_, lean_object* v_next_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1519_, v_slot_1520_, v_next_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object* v_m_1524_, lean_object* v_00_u03b1_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_slot_1528_, lean_object* v_next_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(v_m_1524_, v_00_u03b1_1525_, v_inst_1526_, v_inst_1527_, v_slot_1528_, v_next_1529_, v_a_1530_);
lean_dec(v_a_1530_);
lean_dec_ref(v_inst_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object* v_toApplicative_1532_, lean_object* v_fst_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_toPure_1535_; lean_object* v___x_1536_; 
v_toPure_1535_ = lean_ctor_get(v_toApplicative_1532_, 1);
lean_inc(v_toPure_1535_);
lean_dec_ref(v_toApplicative_1532_);
v___x_1536_ = lean_apply_2(v_toPure_1535_, lean_box(0), v_fst_1533_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object* v_inst_1537_, lean_object* v_toBind_1538_, lean_object* v___f_1539_, lean_object* v_____r_1540_, lean_object* v_st_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_inc(v___y_1542_);
v___x_1543_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1543_, 0, lean_box(0));
lean_closure_set(v___x_1543_, 1, lean_box(0));
lean_closure_set(v___x_1543_, 2, v___y_1542_);
lean_closure_set(v___x_1543_, 3, v_st_1541_);
v___x_1544_ = lean_apply_2(v_inst_1537_, lean_box(0), v___x_1543_);
v___x_1545_ = lean_apply_4(v_toBind_1538_, lean_box(0), lean_box(0), v___x_1544_, v___f_1539_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed(lean_object* v_inst_1546_, lean_object* v_toBind_1547_, lean_object* v___f_1548_, lean_object* v_____r_1549_, lean_object* v_st_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1546_, v_toBind_1547_, v___f_1548_, v_____r_1549_, v_st_1550_, v___y_1551_);
lean_dec(v___y_1551_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object* v_snd_1553_, lean_object* v_waiters_1554_, lean_object* v_capacity_1555_, lean_object* v_size_1556_, lean_object* v_buffer_1557_, lean_object* v_write_1558_, lean_object* v_read_1559_, lean_object* v_receivers_1560_, lean_object* v_nextId_1561_, uint8_t v_closed_1562_, lean_object* v_pos_1563_, lean_object* v___f_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1567_, 0, v_snd_1553_);
lean_ctor_set(v___x_1567_, 1, v_waiters_1554_);
lean_ctor_set(v___x_1567_, 2, v_capacity_1555_);
lean_ctor_set(v___x_1567_, 3, v_size_1556_);
lean_ctor_set(v___x_1567_, 4, v_buffer_1557_);
lean_ctor_set(v___x_1567_, 5, v_write_1558_);
lean_ctor_set(v___x_1567_, 6, v_read_1559_);
lean_ctor_set(v___x_1567_, 7, v_receivers_1560_);
lean_ctor_set(v___x_1567_, 8, v_nextId_1561_);
lean_ctor_set(v___x_1567_, 9, v_pos_1563_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*10, v_closed_1562_);
v___x_1568_ = lean_box(0);
lean_inc(v_a_1565_);
v___x_1569_ = lean_apply_3(v___f_1564_, v___x_1568_, v___x_1567_, v_a_1565_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object* v_snd_1570_, lean_object* v_waiters_1571_, lean_object* v_capacity_1572_, lean_object* v_size_1573_, lean_object* v_buffer_1574_, lean_object* v_write_1575_, lean_object* v_read_1576_, lean_object* v_receivers_1577_, lean_object* v_nextId_1578_, lean_object* v_closed_1579_, lean_object* v_pos_1580_, lean_object* v___f_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
uint8_t v_closed_boxed_1584_; lean_object* v_res_1585_; 
v_closed_boxed_1584_ = lean_unbox(v_closed_1579_);
v_res_1585_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1570_, v_waiters_1571_, v_capacity_1572_, v_size_1573_, v_buffer_1574_, v_write_1575_, v_read_1576_, v_receivers_1577_, v_nextId_1578_, v_closed_boxed_1584_, v_pos_1580_, v___f_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object* v_toApplicative_1586_, lean_object* v_inst_1587_, lean_object* v_toBind_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, uint8_t v___x_1591_, lean_object* v_inst_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_fst_1594_; 
v_fst_1594_ = lean_ctor_get(v_a_1593_, 0);
lean_inc(v_fst_1594_);
if (lean_obj_tag(v_fst_1594_) == 1)
{
lean_object* v_snd_1595_; lean_object* v___f_1596_; lean_object* v___f_1597_; uint8_t v___x_1598_; 
v_snd_1595_ = lean_ctor_get(v_a_1593_, 1);
lean_inc(v_snd_1595_);
lean_dec_ref(v_a_1593_);
v___f_1596_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1596_, 0, v_toApplicative_1586_);
lean_closure_set(v___f_1596_, 1, v_fst_1594_);
lean_inc_ref(v___f_1596_);
lean_inc(v_toBind_1588_);
lean_inc(v_inst_1587_);
v___f_1597_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1597_, 0, v_inst_1587_);
lean_closure_set(v___f_1597_, 1, v_toBind_1588_);
lean_closure_set(v___f_1597_, 2, v___f_1596_);
v___x_1598_ = lean_unbox(v_snd_1595_);
lean_dec(v_snd_1595_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v___f_1597_);
lean_dec(v_inst_1592_);
v___x_1599_ = lean_box(0);
v___x_1600_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1587_, v_toBind_1588_, v___f_1596_, v___x_1599_, v_a_1589_, v_a_1590_);
return v___x_1600_;
}
else
{
lean_object* v___x_1601_; lean_object* v_producers_1602_; lean_object* v_waiters_1603_; lean_object* v_capacity_1604_; lean_object* v_size_1605_; lean_object* v_buffer_1606_; lean_object* v_write_1607_; lean_object* v_read_1608_; lean_object* v_receivers_1609_; lean_object* v_nextId_1610_; uint8_t v_closed_1611_; lean_object* v_pos_1612_; lean_object* v___x_1613_; 
v___x_1601_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_1589_);
v_producers_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_ref(v_producers_1602_);
v_waiters_1603_ = lean_ctor_get(v___x_1601_, 1);
lean_inc_ref(v_waiters_1603_);
v_capacity_1604_ = lean_ctor_get(v___x_1601_, 2);
lean_inc(v_capacity_1604_);
v_size_1605_ = lean_ctor_get(v___x_1601_, 3);
lean_inc(v_size_1605_);
v_buffer_1606_ = lean_ctor_get(v___x_1601_, 4);
lean_inc_ref(v_buffer_1606_);
v_write_1607_ = lean_ctor_get(v___x_1601_, 5);
lean_inc(v_write_1607_);
v_read_1608_ = lean_ctor_get(v___x_1601_, 6);
lean_inc(v_read_1608_);
v_receivers_1609_ = lean_ctor_get(v___x_1601_, 7);
lean_inc(v_receivers_1609_);
v_nextId_1610_ = lean_ctor_get(v___x_1601_, 8);
lean_inc(v_nextId_1610_);
v_closed_1611_ = lean_ctor_get_uint8(v___x_1601_, sizeof(void*)*10);
v_pos_1612_ = lean_ctor_get(v___x_1601_, 9);
lean_inc(v_pos_1612_);
v___x_1613_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1602_);
if (lean_obj_tag(v___x_1613_) == 1)
{
lean_object* v_val_1614_; lean_object* v_fst_1615_; lean_object* v_snd_1616_; lean_object* v___x_1617_; lean_object* v___f_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v___x_1601_);
lean_dec_ref(v___f_1596_);
lean_dec(v_inst_1587_);
v_val_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_val_1614_);
lean_dec_ref(v___x_1613_);
v_fst_1615_ = lean_ctor_get(v_val_1614_, 0);
lean_inc(v_fst_1615_);
v_snd_1616_ = lean_ctor_get(v_val_1614_, 1);
lean_inc(v_snd_1616_);
lean_dec(v_val_1614_);
v___x_1617_ = lean_box(v_closed_1611_);
lean_inc(v_a_1590_);
v___f_1618_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1618_, 0, v_snd_1616_);
lean_closure_set(v___f_1618_, 1, v_waiters_1603_);
lean_closure_set(v___f_1618_, 2, v_capacity_1604_);
lean_closure_set(v___f_1618_, 3, v_size_1605_);
lean_closure_set(v___f_1618_, 4, v_buffer_1606_);
lean_closure_set(v___f_1618_, 5, v_write_1607_);
lean_closure_set(v___f_1618_, 6, v_read_1608_);
lean_closure_set(v___f_1618_, 7, v_receivers_1609_);
lean_closure_set(v___f_1618_, 8, v_nextId_1610_);
lean_closure_set(v___f_1618_, 9, v___x_1617_);
lean_closure_set(v___f_1618_, 10, v_pos_1612_);
lean_closure_set(v___f_1618_, 11, v___f_1597_);
lean_closure_set(v___f_1618_, 12, v_a_1590_);
v___x_1619_ = lean_box(v___x_1591_);
v___x_1620_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1620_, 0, lean_box(0));
lean_closure_set(v___x_1620_, 1, v___x_1619_);
lean_closure_set(v___x_1620_, 2, v_fst_1615_);
v___x_1621_ = lean_apply_2(v_inst_1592_, lean_box(0), v___x_1620_);
v___x_1622_ = lean_apply_4(v_toBind_1588_, lean_box(0), lean_box(0), v___x_1621_, v___f_1618_);
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec(v___x_1613_);
lean_dec(v_pos_1612_);
lean_dec(v_nextId_1610_);
lean_dec(v_receivers_1609_);
lean_dec(v_read_1608_);
lean_dec(v_write_1607_);
lean_dec_ref(v_buffer_1606_);
lean_dec(v_size_1605_);
lean_dec(v_capacity_1604_);
lean_dec_ref(v_waiters_1603_);
lean_dec_ref(v___f_1597_);
lean_dec(v_inst_1592_);
v___x_1623_ = lean_box(0);
v___x_1624_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1587_, v_toBind_1588_, v___f_1596_, v___x_1623_, v___x_1601_, v_a_1590_);
return v___x_1624_;
}
}
}
else
{
lean_object* v_toPure_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_fst_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_inst_1592_);
lean_dec_ref(v_a_1589_);
lean_dec(v_toBind_1588_);
lean_dec(v_inst_1587_);
v_toPure_1625_ = lean_ctor_get(v_toApplicative_1586_, 1);
lean_inc(v_toPure_1625_);
lean_dec_ref(v_toApplicative_1586_);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_apply_2(v_toPure_1625_, lean_box(0), v___x_1626_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object* v_toApplicative_1628_, lean_object* v_inst_1629_, lean_object* v_toBind_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v___x_1633_, lean_object* v_inst_1634_, lean_object* v_a_1635_){
_start:
{
uint8_t v___x_1067__boxed_1636_; lean_object* v_res_1637_; 
v___x_1067__boxed_1636_ = lean_unbox(v___x_1633_);
v_res_1637_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1628_, v_inst_1629_, v_toBind_1630_, v_a_1631_, v_a_1632_, v___x_1067__boxed_1636_, v_inst_1634_, v_a_1635_);
lean_dec(v_a_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object* v_inst_1638_, lean_object* v_next_1639_, lean_object* v_toBind_1640_, lean_object* v___f_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1638_, v_a_1642_, v_next_1639_);
v___x_1644_ = lean_apply_4(v_toBind_1640_, lean_box(0), lean_box(0), v___x_1643_, v___f_1641_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object* v_a_1645_, lean_object* v_toApplicative_1646_, lean_object* v_inst_1647_, lean_object* v_toBind_1648_, lean_object* v_a_1649_, lean_object* v_inst_1650_, lean_object* v_next_1651_, lean_object* v_inst_1652_, uint8_t v_a_1653_){
_start:
{
if (v_a_1653_ == 0)
{
lean_object* v_capacity_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___f_1657_; lean_object* v___f_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_capacity_1654_ = lean_ctor_get(v_a_1645_, 2);
lean_inc(v_capacity_1654_);
v___x_1655_ = 1;
v___x_1656_ = lean_box(v___x_1655_);
lean_inc(v_a_1649_);
lean_inc_n(v_toBind_1648_, 2);
lean_inc_n(v_inst_1647_, 2);
v___f_1657_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1657_, 0, v_toApplicative_1646_);
lean_closure_set(v___f_1657_, 1, v_inst_1647_);
lean_closure_set(v___f_1657_, 2, v_toBind_1648_);
lean_closure_set(v___f_1657_, 3, v_a_1645_);
lean_closure_set(v___f_1657_, 4, v_a_1649_);
lean_closure_set(v___f_1657_, 5, v___x_1656_);
lean_closure_set(v___f_1657_, 6, v_inst_1650_);
lean_inc(v_next_1651_);
v___f_1658_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1658_, 0, v_inst_1647_);
lean_closure_set(v___f_1658_, 1, v_next_1651_);
lean_closure_set(v___f_1658_, 2, v_toBind_1648_);
lean_closure_set(v___f_1658_, 3, v___f_1657_);
v___x_1659_ = lean_nat_mod(v_next_1651_, v_capacity_1654_);
lean_dec(v_capacity_1654_);
lean_dec(v_next_1651_);
v___x_1660_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1652_, v_inst_1647_, v___x_1659_, v_a_1649_);
v___x_1661_ = lean_apply_4(v_toBind_1648_, lean_box(0), lean_box(0), v___x_1660_, v___f_1658_);
return v___x_1661_;
}
else
{
lean_object* v_toPure_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
lean_dec_ref(v_inst_1652_);
lean_dec(v_next_1651_);
lean_dec(v_inst_1650_);
lean_dec(v_toBind_1648_);
lean_dec(v_inst_1647_);
lean_dec_ref(v_a_1645_);
v_toPure_1662_ = lean_ctor_get(v_toApplicative_1646_, 1);
lean_inc(v_toPure_1662_);
lean_dec_ref(v_toApplicative_1646_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_apply_2(v_toPure_1662_, lean_box(0), v___x_1663_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object* v_a_1665_, lean_object* v_toApplicative_1666_, lean_object* v_inst_1667_, lean_object* v_toBind_1668_, lean_object* v_a_1669_, lean_object* v_inst_1670_, lean_object* v_next_1671_, lean_object* v_inst_1672_, lean_object* v_a_1673_){
_start:
{
uint8_t v_a_boxed_1674_; lean_object* v_res_1675_; 
v_a_boxed_1674_ = lean_unbox(v_a_1673_);
v_res_1675_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1665_, v_toApplicative_1666_, v_inst_1667_, v_toBind_1668_, v_a_1669_, v_inst_1670_, v_next_1671_, v_inst_1672_, v_a_boxed_1674_);
lean_dec(v_a_1669_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object* v_toApplicative_1676_, lean_object* v_inst_1677_, lean_object* v_toBind_1678_, lean_object* v_a_1679_, lean_object* v_inst_1680_, lean_object* v_next_1681_, lean_object* v_inst_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___f_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_inc_ref(v_inst_1682_);
lean_inc(v_a_1679_);
lean_inc(v_toBind_1678_);
lean_inc(v_inst_1677_);
v___f_1684_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_1684_, 0, v_a_1683_);
lean_closure_set(v___f_1684_, 1, v_toApplicative_1676_);
lean_closure_set(v___f_1684_, 2, v_inst_1677_);
lean_closure_set(v___f_1684_, 3, v_toBind_1678_);
lean_closure_set(v___f_1684_, 4, v_a_1679_);
lean_closure_set(v___f_1684_, 5, v_inst_1680_);
lean_closure_set(v___f_1684_, 6, v_next_1681_);
lean_closure_set(v___f_1684_, 7, v_inst_1682_);
v___x_1685_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_1682_, v_inst_1677_, v_a_1679_);
v___x_1686_ = lean_apply_4(v_toBind_1678_, lean_box(0), lean_box(0), v___x_1685_, v___f_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed(lean_object* v_toApplicative_1687_, lean_object* v_inst_1688_, lean_object* v_toBind_1689_, lean_object* v_a_1690_, lean_object* v_inst_1691_, lean_object* v_next_1692_, lean_object* v_inst_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(v_toApplicative_1687_, v_inst_1688_, v_toBind_1689_, v_a_1690_, v_inst_1691_, v_next_1692_, v_inst_1693_, v_a_1694_);
lean_dec(v_a_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object* v_inst_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_next_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_toApplicative_1701_; lean_object* v_toBind_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_toApplicative_1701_ = lean_ctor_get(v_inst_1696_, 0);
lean_inc_ref(v_toApplicative_1701_);
v_toBind_1702_ = lean_ctor_get(v_inst_1696_, 1);
lean_inc_n(v_toBind_1702_, 2);
lean_inc_n(v_a_1700_, 2);
lean_inc(v_inst_1697_);
v___f_1703_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_1703_, 0, v_toApplicative_1701_);
lean_closure_set(v___f_1703_, 1, v_inst_1697_);
lean_closure_set(v___f_1703_, 2, v_toBind_1702_);
lean_closure_set(v___f_1703_, 3, v_a_1700_);
lean_closure_set(v___f_1703_, 4, v_inst_1698_);
lean_closure_set(v___f_1703_, 5, v_next_1699_);
lean_closure_set(v___f_1703_, 6, v_inst_1696_);
v___x_1704_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1704_, 0, lean_box(0));
lean_closure_set(v___x_1704_, 1, lean_box(0));
lean_closure_set(v___x_1704_, 2, v_a_1700_);
v___x_1705_ = lean_apply_2(v_inst_1697_, lean_box(0), v___x_1704_);
v___x_1706_ = lean_apply_4(v_toBind_1702_, lean_box(0), lean_box(0), v___x_1705_, v___f_1703_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___boxed(lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_next_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1707_, v_inst_1708_, v_inst_1709_, v_next_1710_, v_a_1711_);
lean_dec(v_a_1711_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object* v_m_1713_, lean_object* v_00_u03b1_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_next_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1715_, v_inst_1716_, v_inst_1717_, v_next_1718_, v_a_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___boxed(lean_object* v_m_1721_, lean_object* v_00_u03b1_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_next_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(v_m_1721_, v_00_u03b1_1722_, v_inst_1723_, v_inst_1724_, v_inst_1725_, v_next_1726_, v_a_1727_);
lean_dec(v_a_1727_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_1729_, lean_object* v_k_1730_){
_start:
{
if (lean_obj_tag(v_t_1729_) == 0)
{
lean_object* v_k_1731_; lean_object* v_v_1732_; lean_object* v_l_1733_; lean_object* v_r_1734_; uint8_t v___x_1735_; 
v_k_1731_ = lean_ctor_get(v_t_1729_, 1);
v_v_1732_ = lean_ctor_get(v_t_1729_, 2);
v_l_1733_ = lean_ctor_get(v_t_1729_, 3);
v_r_1734_ = lean_ctor_get(v_t_1729_, 4);
v___x_1735_ = lean_nat_dec_lt(v_k_1730_, v_k_1731_);
if (v___x_1735_ == 0)
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_nat_dec_eq(v_k_1730_, v_k_1731_);
if (v___x_1736_ == 0)
{
v_t_1729_ = v_r_1734_;
goto _start;
}
else
{
lean_object* v___x_1738_; 
lean_inc(v_v_1732_);
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_v_1732_);
return v___x_1738_;
}
}
else
{
v_t_1729_ = v_l_1733_;
goto _start;
}
}
else
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_box(0);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_1741_, lean_object* v_k_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_1741_, v_k_1742_);
lean_dec(v_k_1742_);
lean_dec(v_t_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_1744_, lean_object* v_t_1745_){
_start:
{
if (lean_obj_tag(v_t_1745_) == 0)
{
lean_object* v_k_1746_; lean_object* v_v_1747_; lean_object* v_l_1748_; lean_object* v_r_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_2404_; 
v_k_1746_ = lean_ctor_get(v_t_1745_, 1);
v_v_1747_ = lean_ctor_get(v_t_1745_, 2);
v_l_1748_ = lean_ctor_get(v_t_1745_, 3);
v_r_1749_ = lean_ctor_get(v_t_1745_, 4);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_t_1745_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; 
v_unused_2405_ = lean_ctor_get(v_t_1745_, 0);
lean_dec(v_unused_2405_);
v___x_1751_ = v_t_1745_;
v_isShared_1752_ = v_isSharedCheck_2404_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_r_1749_);
lean_inc(v_l_1748_);
lean_inc(v_v_1747_);
lean_inc(v_k_1746_);
lean_dec(v_t_1745_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_2404_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_nat_dec_lt(v_k_1744_, v_k_1746_);
if (v___x_1753_ == 0)
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_nat_dec_eq(v_k_1744_, v_k_1746_);
if (v___x_1754_ == 0)
{
lean_object* v_impl_1755_; lean_object* v___x_1756_; 
v_impl_1755_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1744_, v_r_1749_);
v___x_1756_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1755_) == 0)
{
if (lean_obj_tag(v_l_1748_) == 0)
{
lean_object* v_size_1757_; lean_object* v_size_1758_; lean_object* v_k_1759_; lean_object* v_v_1760_; lean_object* v_l_1761_; lean_object* v_r_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v_size_1757_ = lean_ctor_get(v_impl_1755_, 0);
lean_inc(v_size_1757_);
v_size_1758_ = lean_ctor_get(v_l_1748_, 0);
v_k_1759_ = lean_ctor_get(v_l_1748_, 1);
v_v_1760_ = lean_ctor_get(v_l_1748_, 2);
v_l_1761_ = lean_ctor_get(v_l_1748_, 3);
v_r_1762_ = lean_ctor_get(v_l_1748_, 4);
lean_inc(v_r_1762_);
v___x_1763_ = lean_unsigned_to_nat(3u);
v___x_1764_ = lean_nat_mul(v___x_1763_, v_size_1757_);
v___x_1765_ = lean_nat_dec_lt(v___x_1764_, v_size_1758_);
lean_dec(v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
lean_dec(v_r_1762_);
v___x_1766_ = lean_nat_add(v___x_1756_, v_size_1758_);
v___x_1767_ = lean_nat_add(v___x_1766_, v_size_1757_);
lean_dec(v_size_1757_);
lean_dec(v___x_1766_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_impl_1755_);
lean_ctor_set(v___x_1751_, 0, v___x_1767_);
v___x_1769_ = v___x_1751_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_l_1748_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_impl_1755_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
else
{
lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1836_; 
lean_inc(v_l_1761_);
lean_inc(v_v_1760_);
lean_inc(v_k_1759_);
lean_inc(v_size_1758_);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_l_1748_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; lean_object* v_unused_1838_; lean_object* v_unused_1839_; lean_object* v_unused_1840_; lean_object* v_unused_1841_; 
v_unused_1837_ = lean_ctor_get(v_l_1748_, 4);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_l_1748_, 3);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_l_1748_, 2);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_l_1748_, 1);
lean_dec(v_unused_1840_);
v_unused_1841_ = lean_ctor_get(v_l_1748_, 0);
lean_dec(v_unused_1841_);
v___x_1772_ = v_l_1748_;
v_isShared_1773_ = v_isSharedCheck_1836_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v_l_1748_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1836_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_size_1774_; lean_object* v_size_1775_; lean_object* v_k_1776_; lean_object* v_v_1777_; lean_object* v_l_1778_; lean_object* v_r_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_size_1774_ = lean_ctor_get(v_l_1761_, 0);
v_size_1775_ = lean_ctor_get(v_r_1762_, 0);
v_k_1776_ = lean_ctor_get(v_r_1762_, 1);
v_v_1777_ = lean_ctor_get(v_r_1762_, 2);
v_l_1778_ = lean_ctor_get(v_r_1762_, 3);
v_r_1779_ = lean_ctor_get(v_r_1762_, 4);
v___x_1780_ = lean_unsigned_to_nat(2u);
v___x_1781_ = lean_nat_mul(v___x_1780_, v_size_1774_);
v___x_1782_ = lean_nat_dec_lt(v_size_1775_, v___x_1781_);
lean_dec(v___x_1781_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1811_; 
lean_inc(v_r_1779_);
lean_inc(v_l_1778_);
lean_inc(v_v_1777_);
lean_inc(v_k_1776_);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_r_1762_);
if (v_isSharedCheck_1811_ == 0)
{
lean_object* v_unused_1812_; lean_object* v_unused_1813_; lean_object* v_unused_1814_; lean_object* v_unused_1815_; lean_object* v_unused_1816_; 
v_unused_1812_ = lean_ctor_get(v_r_1762_, 4);
lean_dec(v_unused_1812_);
v_unused_1813_ = lean_ctor_get(v_r_1762_, 3);
lean_dec(v_unused_1813_);
v_unused_1814_ = lean_ctor_get(v_r_1762_, 2);
lean_dec(v_unused_1814_);
v_unused_1815_ = lean_ctor_get(v_r_1762_, 1);
lean_dec(v_unused_1815_);
v_unused_1816_ = lean_ctor_get(v_r_1762_, 0);
lean_dec(v_unused_1816_);
v___x_1784_ = v_r_1762_;
v_isShared_1785_ = v_isSharedCheck_1811_;
goto v_resetjp_1783_;
}
else
{
lean_dec(v_r_1762_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1811_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___x_1799_; lean_object* v___y_1801_; 
v___x_1786_ = lean_nat_add(v___x_1756_, v_size_1758_);
lean_dec(v_size_1758_);
v___x_1787_ = lean_nat_add(v___x_1786_, v_size_1757_);
lean_dec(v___x_1786_);
v___x_1799_ = lean_nat_add(v___x_1756_, v_size_1774_);
if (lean_obj_tag(v_l_1778_) == 0)
{
lean_object* v_size_1809_; 
v_size_1809_ = lean_ctor_get(v_l_1778_, 0);
lean_inc(v_size_1809_);
v___y_1801_ = v_size_1809_;
goto v___jp_1800_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_unsigned_to_nat(0u);
v___y_1801_ = v___x_1810_;
goto v___jp_1800_;
}
v___jp_1788_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = lean_nat_add(v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec(v___y_1790_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 4, v_impl_1755_);
lean_ctor_set(v___x_1784_, 3, v_r_1779_);
lean_ctor_set(v___x_1784_, 2, v_v_1747_);
lean_ctor_set(v___x_1784_, 1, v_k_1746_);
lean_ctor_set(v___x_1784_, 0, v___x_1792_);
v___x_1794_ = v___x_1784_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_r_1779_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v_impl_1755_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 4, v___x_1794_);
lean_ctor_set(v___x_1772_, 3, v___y_1789_);
lean_ctor_set(v___x_1772_, 2, v_v_1777_);
lean_ctor_set(v___x_1772_, 1, v_k_1776_);
lean_ctor_set(v___x_1772_, 0, v___x_1787_);
v___x_1796_ = v___x_1772_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1787_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_k_1776_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_v_1777_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v___y_1789_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
v___jp_1800_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_nat_add(v___x_1799_, v___y_1801_);
lean_dec(v___y_1801_);
lean_dec(v___x_1799_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_l_1778_);
lean_ctor_set(v___x_1751_, 3, v_l_1761_);
lean_ctor_set(v___x_1751_, 2, v_v_1760_);
lean_ctor_set(v___x_1751_, 1, v_k_1759_);
lean_ctor_set(v___x_1751_, 0, v___x_1802_);
v___x_1804_ = v___x_1751_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_k_1759_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_v_1760_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_l_1761_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_l_1778_);
v___x_1804_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_nat_add(v___x_1756_, v_size_1757_);
lean_dec(v_size_1757_);
if (lean_obj_tag(v_r_1779_) == 0)
{
lean_object* v_size_1806_; 
v_size_1806_ = lean_ctor_get(v_r_1779_, 0);
lean_inc(v_size_1806_);
v___y_1789_ = v___x_1804_;
v___y_1790_ = v___x_1805_;
v___y_1791_ = v_size_1806_;
goto v___jp_1788_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___y_1789_ = v___x_1804_;
v___y_1790_ = v___x_1805_;
v___y_1791_ = v___x_1807_;
goto v___jp_1788_;
}
}
}
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_del_object(v___x_1751_);
v___x_1817_ = lean_nat_add(v___x_1756_, v_size_1758_);
lean_dec(v_size_1758_);
v___x_1818_ = lean_nat_add(v___x_1817_, v_size_1757_);
lean_dec(v___x_1817_);
v___x_1819_ = lean_nat_add(v___x_1756_, v_size_1757_);
lean_dec(v_size_1757_);
v___x_1820_ = lean_nat_add(v___x_1819_, v_size_1775_);
lean_dec(v___x_1819_);
lean_inc_ref(v_impl_1755_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 4, v_impl_1755_);
lean_ctor_set(v___x_1772_, 3, v_r_1762_);
lean_ctor_set(v___x_1772_, 2, v_v_1747_);
lean_ctor_set(v___x_1772_, 1, v_k_1746_);
lean_ctor_set(v___x_1772_, 0, v___x_1820_);
v___x_1822_ = v___x_1772_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1835_, 3, v_r_1762_);
lean_ctor_set(v_reuseFailAlloc_1835_, 4, v_impl_1755_);
v___x_1822_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_isSharedCheck_1829_ = !lean_is_exclusive(v_impl_1755_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; lean_object* v_unused_1831_; lean_object* v_unused_1832_; lean_object* v_unused_1833_; lean_object* v_unused_1834_; 
v_unused_1830_ = lean_ctor_get(v_impl_1755_, 4);
lean_dec(v_unused_1830_);
v_unused_1831_ = lean_ctor_get(v_impl_1755_, 3);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_impl_1755_, 2);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_impl_1755_, 1);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_impl_1755_, 0);
lean_dec(v_unused_1834_);
v___x_1824_ = v_impl_1755_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_dec(v_impl_1755_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 4, v___x_1822_);
lean_ctor_set(v___x_1824_, 3, v_l_1761_);
lean_ctor_set(v___x_1824_, 2, v_v_1760_);
lean_ctor_set(v___x_1824_, 1, v_k_1759_);
lean_ctor_set(v___x_1824_, 0, v___x_1818_);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_k_1759_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_v_1760_);
lean_ctor_set(v_reuseFailAlloc_1828_, 3, v_l_1761_);
lean_ctor_set(v_reuseFailAlloc_1828_, 4, v___x_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v_size_1842_ = lean_ctor_get(v_impl_1755_, 0);
lean_inc(v_size_1842_);
v___x_1843_ = lean_nat_add(v___x_1756_, v_size_1842_);
lean_dec(v_size_1842_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_impl_1755_);
lean_ctor_set(v___x_1751_, 0, v___x_1843_);
v___x_1845_ = v___x_1751_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_l_1748_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_impl_1755_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
if (lean_obj_tag(v_l_1748_) == 0)
{
lean_object* v_l_1847_; 
v_l_1847_ = lean_ctor_get(v_l_1748_, 3);
if (lean_obj_tag(v_l_1847_) == 0)
{
lean_object* v_r_1848_; 
lean_inc_ref(v_l_1847_);
v_r_1848_ = lean_ctor_get(v_l_1748_, 4);
lean_inc(v_r_1848_);
if (lean_obj_tag(v_r_1848_) == 0)
{
lean_object* v_size_1849_; lean_object* v_k_1850_; lean_object* v_v_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1864_; 
v_size_1849_ = lean_ctor_get(v_l_1748_, 0);
v_k_1850_ = lean_ctor_get(v_l_1748_, 1);
v_v_1851_ = lean_ctor_get(v_l_1748_, 2);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_l_1748_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; lean_object* v_unused_1866_; 
v_unused_1865_ = lean_ctor_get(v_l_1748_, 4);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_l_1748_, 3);
lean_dec(v_unused_1866_);
v___x_1853_ = v_l_1748_;
v_isShared_1854_ = v_isSharedCheck_1864_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_v_1851_);
lean_inc(v_k_1850_);
lean_inc(v_size_1849_);
lean_dec(v_l_1748_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1864_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_size_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v_size_1855_ = lean_ctor_get(v_r_1848_, 0);
v___x_1856_ = lean_nat_add(v___x_1756_, v_size_1849_);
lean_dec(v_size_1849_);
v___x_1857_ = lean_nat_add(v___x_1756_, v_size_1855_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 4, v_impl_1755_);
lean_ctor_set(v___x_1853_, 3, v_r_1848_);
lean_ctor_set(v___x_1853_, 2, v_v_1747_);
lean_ctor_set(v___x_1853_, 1, v_k_1746_);
lean_ctor_set(v___x_1853_, 0, v___x_1857_);
v___x_1859_ = v___x_1853_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v_r_1848_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v_impl_1755_);
v___x_1859_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v___x_1859_);
lean_ctor_set(v___x_1751_, 3, v_l_1847_);
lean_ctor_set(v___x_1751_, 2, v_v_1851_);
lean_ctor_set(v___x_1751_, 1, v_k_1850_);
lean_ctor_set(v___x_1751_, 0, v___x_1856_);
v___x_1861_ = v___x_1751_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_k_1850_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_v_1851_);
lean_ctor_set(v_reuseFailAlloc_1862_, 3, v_l_1847_);
lean_ctor_set(v_reuseFailAlloc_1862_, 4, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_object* v_k_1867_; lean_object* v_v_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1879_; 
v_k_1867_ = lean_ctor_get(v_l_1748_, 1);
v_v_1868_ = lean_ctor_get(v_l_1748_, 2);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_l_1748_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; lean_object* v_unused_1881_; lean_object* v_unused_1882_; 
v_unused_1880_ = lean_ctor_get(v_l_1748_, 4);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_l_1748_, 3);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_l_1748_, 0);
lean_dec(v_unused_1882_);
v___x_1870_ = v_l_1748_;
v_isShared_1871_ = v_isSharedCheck_1879_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_v_1868_);
lean_inc(v_k_1867_);
lean_dec(v_l_1748_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1879_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = lean_unsigned_to_nat(3u);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 3, v_r_1848_);
lean_ctor_set(v___x_1870_, 2, v_v_1747_);
lean_ctor_set(v___x_1870_, 1, v_k_1746_);
lean_ctor_set(v___x_1870_, 0, v___x_1756_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1878_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1878_, 3, v_r_1848_);
lean_ctor_set(v_reuseFailAlloc_1878_, 4, v_r_1848_);
v___x_1874_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v___x_1874_);
lean_ctor_set(v___x_1751_, 3, v_l_1847_);
lean_ctor_set(v___x_1751_, 2, v_v_1868_);
lean_ctor_set(v___x_1751_, 1, v_k_1867_);
lean_ctor_set(v___x_1751_, 0, v___x_1872_);
v___x_1876_ = v___x_1751_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_1877_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_1877_, 3, v_l_1847_);
lean_ctor_set(v_reuseFailAlloc_1877_, 4, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
else
{
lean_object* v_r_1883_; 
v_r_1883_ = lean_ctor_get(v_l_1748_, 4);
lean_inc(v_r_1883_);
if (lean_obj_tag(v_r_1883_) == 0)
{
lean_object* v_k_1884_; lean_object* v_v_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1908_; 
lean_inc(v_l_1847_);
v_k_1884_ = lean_ctor_get(v_l_1748_, 1);
v_v_1885_ = lean_ctor_get(v_l_1748_, 2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_l_1748_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; lean_object* v_unused_1910_; lean_object* v_unused_1911_; 
v_unused_1909_ = lean_ctor_get(v_l_1748_, 4);
lean_dec(v_unused_1909_);
v_unused_1910_ = lean_ctor_get(v_l_1748_, 3);
lean_dec(v_unused_1910_);
v_unused_1911_ = lean_ctor_get(v_l_1748_, 0);
lean_dec(v_unused_1911_);
v___x_1887_ = v_l_1748_;
v_isShared_1888_ = v_isSharedCheck_1908_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_v_1885_);
lean_inc(v_k_1884_);
lean_dec(v_l_1748_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1908_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_k_1889_; lean_object* v_v_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1904_; 
v_k_1889_ = lean_ctor_get(v_r_1883_, 1);
v_v_1890_ = lean_ctor_get(v_r_1883_, 2);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_r_1883_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; 
v_unused_1905_ = lean_ctor_get(v_r_1883_, 4);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_r_1883_, 3);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_r_1883_, 0);
lean_dec(v_unused_1907_);
v___x_1892_ = v_r_1883_;
v_isShared_1893_ = v_isSharedCheck_1904_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_v_1890_);
lean_inc(v_k_1889_);
lean_dec(v_r_1883_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1904_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_unsigned_to_nat(3u);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 4, v_l_1847_);
lean_ctor_set(v___x_1892_, 3, v_l_1847_);
lean_ctor_set(v___x_1892_, 2, v_v_1885_);
lean_ctor_set(v___x_1892_, 1, v_k_1884_);
lean_ctor_set(v___x_1892_, 0, v___x_1756_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_k_1884_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_v_1885_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_l_1847_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_l_1847_);
v___x_1896_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 4, v_l_1847_);
lean_ctor_set(v___x_1887_, 2, v_v_1747_);
lean_ctor_set(v___x_1887_, 1, v_k_1746_);
lean_ctor_set(v___x_1887_, 0, v___x_1756_);
v___x_1898_ = v___x_1887_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_l_1847_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_l_1847_);
v___x_1898_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v___x_1898_);
lean_ctor_set(v___x_1751_, 3, v___x_1896_);
lean_ctor_set(v___x_1751_, 2, v_v_1890_);
lean_ctor_set(v___x_1751_, 1, v_k_1889_);
lean_ctor_set(v___x_1751_, 0, v___x_1894_);
v___x_1900_ = v___x_1751_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_k_1889_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_v_1890_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v___x_1898_);
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
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = lean_unsigned_to_nat(2u);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_r_1883_);
lean_ctor_set(v___x_1751_, 0, v___x_1912_);
v___x_1914_ = v___x_1751_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_l_1748_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_r_1883_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v___x_1917_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_l_1748_);
lean_ctor_set(v___x_1751_, 0, v___x_1756_);
v___x_1917_ = v___x_1751_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_l_1748_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_l_1748_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_del_object(v___x_1751_);
lean_dec(v_v_1747_);
lean_dec(v_k_1746_);
if (lean_obj_tag(v_l_1748_) == 0)
{
if (lean_obj_tag(v_r_1749_) == 0)
{
lean_object* v_size_1919_; lean_object* v_k_1920_; lean_object* v_v_1921_; lean_object* v_l_1922_; lean_object* v_r_1923_; lean_object* v_size_1924_; lean_object* v_k_1925_; lean_object* v_v_1926_; lean_object* v_l_1927_; lean_object* v_r_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v_size_1919_ = lean_ctor_get(v_l_1748_, 0);
v_k_1920_ = lean_ctor_get(v_l_1748_, 1);
v_v_1921_ = lean_ctor_get(v_l_1748_, 2);
v_l_1922_ = lean_ctor_get(v_l_1748_, 3);
v_r_1923_ = lean_ctor_get(v_l_1748_, 4);
lean_inc(v_r_1923_);
v_size_1924_ = lean_ctor_get(v_r_1749_, 0);
v_k_1925_ = lean_ctor_get(v_r_1749_, 1);
v_v_1926_ = lean_ctor_get(v_r_1749_, 2);
v_l_1927_ = lean_ctor_get(v_r_1749_, 3);
lean_inc(v_l_1927_);
v_r_1928_ = lean_ctor_get(v_r_1749_, 4);
v___x_1929_ = lean_unsigned_to_nat(1u);
v___x_1930_ = lean_nat_dec_lt(v_size_1919_, v_size_1924_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_2066_; 
lean_inc(v_l_1922_);
lean_inc(v_v_1921_);
lean_inc(v_k_1920_);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_l_1748_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; lean_object* v_unused_2068_; lean_object* v_unused_2069_; lean_object* v_unused_2070_; lean_object* v_unused_2071_; 
v_unused_2067_ = lean_ctor_get(v_l_1748_, 4);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_l_1748_, 3);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_l_1748_, 2);
lean_dec(v_unused_2069_);
v_unused_2070_ = lean_ctor_get(v_l_1748_, 1);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_l_1748_, 0);
lean_dec(v_unused_2071_);
v___x_1932_ = v_l_1748_;
v_isShared_1933_ = v_isSharedCheck_2066_;
goto v_resetjp_1931_;
}
else
{
lean_dec(v_l_1748_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_2066_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v_tree_1935_; 
v___x_1934_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1920_, v_v_1921_, v_l_1922_, v_r_1923_);
v_tree_1935_ = lean_ctor_get(v___x_1934_, 2);
lean_inc(v_tree_1935_);
if (lean_obj_tag(v_tree_1935_) == 0)
{
lean_object* v_k_1936_; lean_object* v_v_1937_; lean_object* v_size_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v_k_1936_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_k_1936_);
v_v_1937_ = lean_ctor_get(v___x_1934_, 1);
lean_inc(v_v_1937_);
lean_dec_ref(v___x_1934_);
v_size_1938_ = lean_ctor_get(v_tree_1935_, 0);
v___x_1939_ = lean_unsigned_to_nat(3u);
v___x_1940_ = lean_nat_mul(v___x_1939_, v_size_1938_);
v___x_1941_ = lean_nat_dec_lt(v___x_1940_, v_size_1924_);
lean_dec(v___x_1940_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_dec(v_l_1927_);
v___x_1942_ = lean_nat_add(v___x_1929_, v_size_1938_);
v___x_1943_ = lean_nat_add(v___x_1942_, v_size_1924_);
lean_dec(v___x_1942_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v_r_1749_);
lean_ctor_set(v___x_1932_, 3, v_tree_1935_);
lean_ctor_set(v___x_1932_, 2, v_v_1937_);
lean_ctor_set(v___x_1932_, 1, v_k_1936_);
lean_ctor_set(v___x_1932_, 0, v___x_1943_);
v___x_1945_ = v___x_1932_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_k_1936_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_v_1937_);
lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_tree_1935_);
lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_r_1749_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
else
{
lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_2001_; 
lean_inc(v_r_1928_);
lean_inc(v_v_1926_);
lean_inc(v_k_1925_);
lean_inc(v_size_1924_);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_r_1749_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; lean_object* v_unused_2003_; lean_object* v_unused_2004_; lean_object* v_unused_2005_; lean_object* v_unused_2006_; 
v_unused_2002_ = lean_ctor_get(v_r_1749_, 4);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_r_1749_, 3);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_r_1749_, 2);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_r_1749_, 1);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_r_1749_, 0);
lean_dec(v_unused_2006_);
v___x_1948_ = v_r_1749_;
v_isShared_1949_ = v_isSharedCheck_2001_;
goto v_resetjp_1947_;
}
else
{
lean_dec(v_r_1749_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_2001_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_size_1950_; lean_object* v_k_1951_; lean_object* v_v_1952_; lean_object* v_l_1953_; lean_object* v_r_1954_; lean_object* v_size_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_size_1950_ = lean_ctor_get(v_l_1927_, 0);
v_k_1951_ = lean_ctor_get(v_l_1927_, 1);
v_v_1952_ = lean_ctor_get(v_l_1927_, 2);
v_l_1953_ = lean_ctor_get(v_l_1927_, 3);
v_r_1954_ = lean_ctor_get(v_l_1927_, 4);
v_size_1955_ = lean_ctor_get(v_r_1928_, 0);
v___x_1956_ = lean_unsigned_to_nat(2u);
v___x_1957_ = lean_nat_mul(v___x_1956_, v_size_1955_);
v___x_1958_ = lean_nat_dec_lt(v_size_1950_, v___x_1957_);
lean_dec(v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1986_; 
lean_inc(v_r_1954_);
lean_inc(v_l_1953_);
lean_inc(v_v_1952_);
lean_inc(v_k_1951_);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_l_1927_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; lean_object* v_unused_1989_; lean_object* v_unused_1990_; lean_object* v_unused_1991_; 
v_unused_1987_ = lean_ctor_get(v_l_1927_, 4);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_l_1927_, 3);
lean_dec(v_unused_1988_);
v_unused_1989_ = lean_ctor_get(v_l_1927_, 2);
lean_dec(v_unused_1989_);
v_unused_1990_ = lean_ctor_get(v_l_1927_, 1);
lean_dec(v_unused_1990_);
v_unused_1991_ = lean_ctor_get(v_l_1927_, 0);
lean_dec(v_unused_1991_);
v___x_1960_ = v_l_1927_;
v_isShared_1961_ = v_isSharedCheck_1986_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v_l_1927_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1986_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1976_; 
v___x_1962_ = lean_nat_add(v___x_1929_, v_size_1938_);
v___x_1963_ = lean_nat_add(v___x_1962_, v_size_1924_);
lean_dec(v_size_1924_);
if (lean_obj_tag(v_l_1953_) == 0)
{
lean_object* v_size_1984_; 
v_size_1984_ = lean_ctor_get(v_l_1953_, 0);
lean_inc(v_size_1984_);
v___y_1976_ = v_size_1984_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_unsigned_to_nat(0u);
v___y_1976_ = v___x_1985_;
goto v___jp_1975_;
}
v___jp_1964_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_nat_add(v___y_1965_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec(v___y_1965_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 4, v_r_1928_);
lean_ctor_set(v___x_1960_, 3, v_r_1954_);
lean_ctor_set(v___x_1960_, 2, v_v_1926_);
lean_ctor_set(v___x_1960_, 1, v_k_1925_);
lean_ctor_set(v___x_1960_, 0, v___x_1968_);
v___x_1970_ = v___x_1960_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_k_1925_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_v_1926_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_r_1954_);
lean_ctor_set(v_reuseFailAlloc_1974_, 4, v_r_1928_);
v___x_1970_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 4, v___x_1970_);
lean_ctor_set(v___x_1948_, 3, v___y_1966_);
lean_ctor_set(v___x_1948_, 2, v_v_1952_);
lean_ctor_set(v___x_1948_, 1, v_k_1951_);
lean_ctor_set(v___x_1948_, 0, v___x_1963_);
v___x_1972_ = v___x_1948_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_k_1951_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_v_1952_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v___y_1966_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
v___jp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_nat_add(v___x_1962_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec(v___x_1962_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v_l_1953_);
lean_ctor_set(v___x_1932_, 3, v_tree_1935_);
lean_ctor_set(v___x_1932_, 2, v_v_1937_);
lean_ctor_set(v___x_1932_, 1, v_k_1936_);
lean_ctor_set(v___x_1932_, 0, v___x_1977_);
v___x_1979_ = v___x_1932_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_k_1936_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_v_1937_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_tree_1935_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v_l_1953_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_nat_add(v___x_1929_, v_size_1955_);
if (lean_obj_tag(v_r_1954_) == 0)
{
lean_object* v_size_1981_; 
v_size_1981_ = lean_ctor_get(v_r_1954_, 0);
lean_inc(v_size_1981_);
v___y_1965_ = v___x_1980_;
v___y_1966_ = v___x_1979_;
v___y_1967_ = v_size_1981_;
goto v___jp_1964_;
}
else
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v___y_1965_ = v___x_1980_;
v___y_1966_ = v___x_1979_;
v___y_1967_ = v___x_1982_;
goto v___jp_1964_;
}
}
}
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1992_ = lean_nat_add(v___x_1929_, v_size_1938_);
v___x_1993_ = lean_nat_add(v___x_1992_, v_size_1924_);
lean_dec(v_size_1924_);
v___x_1994_ = lean_nat_add(v___x_1992_, v_size_1950_);
lean_dec(v___x_1992_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 4, v_l_1927_);
lean_ctor_set(v___x_1948_, 3, v_tree_1935_);
lean_ctor_set(v___x_1948_, 2, v_v_1937_);
lean_ctor_set(v___x_1948_, 1, v_k_1936_);
lean_ctor_set(v___x_1948_, 0, v___x_1994_);
v___x_1996_ = v___x_1948_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_k_1936_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_v_1937_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_tree_1935_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_l_1927_);
v___x_1996_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1998_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v_r_1928_);
lean_ctor_set(v___x_1932_, 3, v___x_1996_);
lean_ctor_set(v___x_1932_, 2, v_v_1926_);
lean_ctor_set(v___x_1932_, 1, v_k_1925_);
lean_ctor_set(v___x_1932_, 0, v___x_1993_);
v___x_1998_ = v___x_1932_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_k_1925_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_v_1926_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_r_1928_);
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
}
}
else
{
lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2060_; 
lean_inc(v_r_1928_);
lean_inc(v_v_1926_);
lean_inc(v_k_1925_);
lean_inc(v_size_1924_);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_r_1749_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; lean_object* v_unused_2062_; lean_object* v_unused_2063_; lean_object* v_unused_2064_; lean_object* v_unused_2065_; 
v_unused_2061_ = lean_ctor_get(v_r_1749_, 4);
lean_dec(v_unused_2061_);
v_unused_2062_ = lean_ctor_get(v_r_1749_, 3);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v_r_1749_, 2);
lean_dec(v_unused_2063_);
v_unused_2064_ = lean_ctor_get(v_r_1749_, 1);
lean_dec(v_unused_2064_);
v_unused_2065_ = lean_ctor_get(v_r_1749_, 0);
lean_dec(v_unused_2065_);
v___x_2008_ = v_r_1749_;
v_isShared_2009_ = v_isSharedCheck_2060_;
goto v_resetjp_2007_;
}
else
{
lean_dec(v_r_1749_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2060_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
if (lean_obj_tag(v_l_1927_) == 0)
{
if (lean_obj_tag(v_r_1928_) == 0)
{
lean_object* v_k_2010_; lean_object* v_v_2011_; lean_object* v_size_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v_k_2010_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_k_2010_);
v_v_2011_ = lean_ctor_get(v___x_1934_, 1);
lean_inc(v_v_2011_);
lean_dec_ref(v___x_1934_);
v_size_2012_ = lean_ctor_get(v_l_1927_, 0);
v___x_2013_ = lean_nat_add(v___x_1929_, v_size_1924_);
lean_dec(v_size_1924_);
v___x_2014_ = lean_nat_add(v___x_1929_, v_size_2012_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v_l_1927_);
lean_ctor_set(v___x_2008_, 3, v_tree_1935_);
lean_ctor_set(v___x_2008_, 2, v_v_2011_);
lean_ctor_set(v___x_2008_, 1, v_k_2010_);
lean_ctor_set(v___x_2008_, 0, v___x_2014_);
v___x_2016_ = v___x_2008_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_k_2010_);
lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_v_2011_);
lean_ctor_set(v_reuseFailAlloc_2020_, 3, v_tree_1935_);
lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_l_1927_);
v___x_2016_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2018_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v_r_1928_);
lean_ctor_set(v___x_1932_, 3, v___x_2016_);
lean_ctor_set(v___x_1932_, 2, v_v_1926_);
lean_ctor_set(v___x_1932_, 1, v_k_1925_);
lean_ctor_set(v___x_1932_, 0, v___x_2013_);
v___x_2018_ = v___x_1932_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_k_1925_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_v_1926_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v___x_2016_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_r_1928_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_object* v_k_2021_; lean_object* v_v_2022_; lean_object* v_k_2023_; lean_object* v_v_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_size_1924_);
v_k_2021_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_k_2021_);
v_v_2022_ = lean_ctor_get(v___x_1934_, 1);
lean_inc(v_v_2022_);
lean_dec_ref(v___x_1934_);
v_k_2023_ = lean_ctor_get(v_l_1927_, 1);
v_v_2024_ = lean_ctor_get(v_l_1927_, 2);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_l_1927_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; lean_object* v_unused_2040_; lean_object* v_unused_2041_; 
v_unused_2039_ = lean_ctor_get(v_l_1927_, 4);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_l_1927_, 3);
lean_dec(v_unused_2040_);
v_unused_2041_ = lean_ctor_get(v_l_1927_, 0);
lean_dec(v_unused_2041_);
v___x_2026_ = v_l_1927_;
v_isShared_2027_ = v_isSharedCheck_2038_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_v_2024_);
lean_inc(v_k_2023_);
lean_dec(v_l_1927_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2038_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_unsigned_to_nat(3u);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 4, v_r_1928_);
lean_ctor_set(v___x_2026_, 3, v_r_1928_);
lean_ctor_set(v___x_2026_, 2, v_v_2022_);
lean_ctor_set(v___x_2026_, 1, v_k_2021_);
lean_ctor_set(v___x_2026_, 0, v___x_1929_);
v___x_2030_ = v___x_2026_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v_k_2021_);
lean_ctor_set(v_reuseFailAlloc_2037_, 2, v_v_2022_);
lean_ctor_set(v_reuseFailAlloc_2037_, 3, v_r_1928_);
lean_ctor_set(v_reuseFailAlloc_2037_, 4, v_r_1928_);
v___x_2030_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 3, v_r_1928_);
lean_ctor_set(v___x_2008_, 0, v___x_1929_);
v___x_2032_ = v___x_2008_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_k_1925_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_v_1926_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_r_1928_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_r_1928_);
v___x_2032_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2034_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v___x_2032_);
lean_ctor_set(v___x_1932_, 3, v___x_2030_);
lean_ctor_set(v___x_1932_, 2, v_v_2024_);
lean_ctor_set(v___x_1932_, 1, v_k_2023_);
lean_ctor_set(v___x_1932_, 0, v___x_2028_);
v___x_2034_ = v___x_1932_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_k_2023_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_v_2024_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2035_, 4, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1928_) == 0)
{
lean_object* v_k_2042_; lean_object* v_v_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
lean_dec(v_size_1924_);
v_k_2042_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_k_2042_);
v_v_2043_ = lean_ctor_get(v___x_1934_, 1);
lean_inc(v_v_2043_);
lean_dec_ref(v___x_1934_);
v___x_2044_ = lean_unsigned_to_nat(3u);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 4, v_l_1927_);
lean_ctor_set(v___x_2008_, 2, v_v_2043_);
lean_ctor_set(v___x_2008_, 1, v_k_2042_);
lean_ctor_set(v___x_2008_, 0, v___x_1929_);
v___x_2046_ = v___x_2008_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_k_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_v_2043_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_l_1927_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_l_1927_);
v___x_2046_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2048_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v_r_1928_);
lean_ctor_set(v___x_1932_, 3, v___x_2046_);
lean_ctor_set(v___x_1932_, 2, v_v_1926_);
lean_ctor_set(v___x_1932_, 1, v_k_1925_);
lean_ctor_set(v___x_1932_, 0, v___x_2044_);
v___x_2048_ = v___x_1932_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_k_1925_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_v_1926_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_r_1928_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v_k_2051_; lean_object* v_v_2052_; lean_object* v___x_2054_; 
v_k_2051_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_k_2051_);
v_v_2052_ = lean_ctor_get(v___x_1934_, 1);
lean_inc(v_v_2052_);
lean_dec_ref(v___x_1934_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 3, v_r_1928_);
v___x_2054_ = v___x_2008_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_size_1924_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_k_1925_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_v_1926_);
lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_r_1928_);
lean_ctor_set(v_reuseFailAlloc_2059_, 4, v_r_1928_);
v___x_2054_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = lean_unsigned_to_nat(2u);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v___x_2054_);
lean_ctor_set(v___x_1932_, 3, v_r_1928_);
lean_ctor_set(v___x_1932_, 2, v_v_2052_);
lean_ctor_set(v___x_1932_, 1, v_k_2051_);
lean_ctor_set(v___x_1932_, 0, v___x_2055_);
v___x_2057_ = v___x_1932_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_k_2051_);
lean_ctor_set(v_reuseFailAlloc_2058_, 2, v_v_2052_);
lean_ctor_set(v_reuseFailAlloc_2058_, 3, v_r_1928_);
lean_ctor_set(v_reuseFailAlloc_2058_, 4, v___x_2054_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
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
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2224_; 
lean_inc(v_r_1928_);
lean_inc(v_v_1926_);
lean_inc(v_k_1925_);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_r_1749_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2225_ = lean_ctor_get(v_r_1749_, 4);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_r_1749_, 3);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_r_1749_, 2);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v_r_1749_, 1);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_r_1749_, 0);
lean_dec(v_unused_2229_);
v___x_2073_ = v_r_1749_;
v_isShared_2074_ = v_isSharedCheck_2224_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v_r_1749_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2224_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v_tree_2076_; 
v___x_2075_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1925_, v_v_1926_, v_l_1927_, v_r_1928_);
v_tree_2076_ = lean_ctor_get(v___x_2075_, 2);
lean_inc(v_tree_2076_);
if (lean_obj_tag(v_tree_2076_) == 0)
{
lean_object* v_k_2077_; lean_object* v_v_2078_; lean_object* v_size_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v_k_2077_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_k_2077_);
v_v_2078_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_v_2078_);
lean_dec_ref(v___x_2075_);
v_size_2079_ = lean_ctor_get(v_tree_2076_, 0);
v___x_2080_ = lean_unsigned_to_nat(3u);
v___x_2081_ = lean_nat_mul(v___x_2080_, v_size_2079_);
v___x_2082_ = lean_nat_dec_lt(v___x_2081_, v_size_1919_);
lean_dec(v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec(v_r_1923_);
v___x_2083_ = lean_nat_add(v___x_1929_, v_size_1919_);
v___x_2084_ = lean_nat_add(v___x_2083_, v_size_2079_);
lean_dec(v___x_2083_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_tree_2076_);
lean_ctor_set(v___x_2073_, 3, v_l_1748_);
lean_ctor_set(v___x_2073_, 2, v_v_2078_);
lean_ctor_set(v___x_2073_, 1, v_k_2077_);
lean_ctor_set(v___x_2073_, 0, v___x_2084_);
v___x_2086_ = v___x_2073_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_l_1748_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_tree_2076_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
else
{
lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2153_; 
lean_inc(v_l_1922_);
lean_inc(v_v_1921_);
lean_inc(v_k_1920_);
lean_inc(v_size_1919_);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_l_1748_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; lean_object* v_unused_2158_; 
v_unused_2154_ = lean_ctor_get(v_l_1748_, 4);
lean_dec(v_unused_2154_);
v_unused_2155_ = lean_ctor_get(v_l_1748_, 3);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_l_1748_, 2);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_l_1748_, 1);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_l_1748_, 0);
lean_dec(v_unused_2158_);
v___x_2089_ = v_l_1748_;
v_isShared_2090_ = v_isSharedCheck_2153_;
goto v_resetjp_2088_;
}
else
{
lean_dec(v_l_1748_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2153_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_size_2091_; lean_object* v_size_2092_; lean_object* v_k_2093_; lean_object* v_v_2094_; lean_object* v_l_2095_; lean_object* v_r_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_size_2091_ = lean_ctor_get(v_l_1922_, 0);
v_size_2092_ = lean_ctor_get(v_r_1923_, 0);
v_k_2093_ = lean_ctor_get(v_r_1923_, 1);
v_v_2094_ = lean_ctor_get(v_r_1923_, 2);
v_l_2095_ = lean_ctor_get(v_r_1923_, 3);
v_r_2096_ = lean_ctor_get(v_r_1923_, 4);
v___x_2097_ = lean_unsigned_to_nat(2u);
v___x_2098_ = lean_nat_mul(v___x_2097_, v_size_2091_);
v___x_2099_ = lean_nat_dec_lt(v_size_2092_, v___x_2098_);
lean_dec(v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2137_; 
lean_inc(v_r_2096_);
lean_inc(v_l_2095_);
lean_inc(v_v_2094_);
lean_inc(v_k_2093_);
lean_del_object(v___x_2089_);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_r_1923_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; lean_object* v_unused_2139_; lean_object* v_unused_2140_; lean_object* v_unused_2141_; lean_object* v_unused_2142_; 
v_unused_2138_ = lean_ctor_get(v_r_1923_, 4);
lean_dec(v_unused_2138_);
v_unused_2139_ = lean_ctor_get(v_r_1923_, 3);
lean_dec(v_unused_2139_);
v_unused_2140_ = lean_ctor_get(v_r_1923_, 2);
lean_dec(v_unused_2140_);
v_unused_2141_ = lean_ctor_get(v_r_1923_, 1);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_r_1923_, 0);
lean_dec(v_unused_2142_);
v___x_2101_ = v_r_1923_;
v_isShared_2102_ = v_isSharedCheck_2137_;
goto v_resetjp_2100_;
}
else
{
lean_dec(v_r_1923_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2137_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___x_2125_; lean_object* v___y_2127_; 
v___x_2103_ = lean_nat_add(v___x_1929_, v_size_1919_);
lean_dec(v_size_1919_);
v___x_2104_ = lean_nat_add(v___x_2103_, v_size_2079_);
lean_dec(v___x_2103_);
v___x_2125_ = lean_nat_add(v___x_1929_, v_size_2091_);
if (lean_obj_tag(v_l_2095_) == 0)
{
lean_object* v_size_2135_; 
v_size_2135_ = lean_ctor_get(v_l_2095_, 0);
lean_inc(v_size_2135_);
v___y_2127_ = v_size_2135_;
goto v___jp_2126_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_unsigned_to_nat(0u);
v___y_2127_ = v___x_2136_;
goto v___jp_2126_;
}
v___jp_2105_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_nat_add(v___y_2106_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec(v___y_2106_);
lean_inc_ref(v_tree_2076_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 4, v_tree_2076_);
lean_ctor_set(v___x_2101_, 3, v_r_2096_);
lean_ctor_set(v___x_2101_, 2, v_v_2078_);
lean_ctor_set(v___x_2101_, 1, v_k_2077_);
lean_ctor_set(v___x_2101_, 0, v___x_2109_);
v___x_2111_ = v___x_2101_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_r_2096_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_tree_2076_);
v___x_2111_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_isSharedCheck_2118_ = !lean_is_exclusive(v_tree_2076_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; lean_object* v_unused_2120_; lean_object* v_unused_2121_; lean_object* v_unused_2122_; lean_object* v_unused_2123_; 
v_unused_2119_ = lean_ctor_get(v_tree_2076_, 4);
lean_dec(v_unused_2119_);
v_unused_2120_ = lean_ctor_get(v_tree_2076_, 3);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_tree_2076_, 2);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_tree_2076_, 1);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_tree_2076_, 0);
lean_dec(v_unused_2123_);
v___x_2113_ = v_tree_2076_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_dec(v_tree_2076_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 4, v___x_2111_);
lean_ctor_set(v___x_2113_, 3, v___y_2107_);
lean_ctor_set(v___x_2113_, 2, v_v_2094_);
lean_ctor_set(v___x_2113_, 1, v_k_2093_);
lean_ctor_set(v___x_2113_, 0, v___x_2104_);
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_k_2093_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_v_2094_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v___y_2107_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v___x_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
v___jp_2126_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_nat_add(v___x_2125_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec(v___x_2125_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_l_2095_);
lean_ctor_set(v___x_2073_, 3, v_l_1922_);
lean_ctor_set(v___x_2073_, 2, v_v_1921_);
lean_ctor_set(v___x_2073_, 1, v_k_1920_);
lean_ctor_set(v___x_2073_, 0, v___x_2128_);
v___x_2130_ = v___x_2073_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_k_1920_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_v_1921_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_l_1922_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_l_2095_);
v___x_2130_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_nat_add(v___x_1929_, v_size_2079_);
if (lean_obj_tag(v_r_2096_) == 0)
{
lean_object* v_size_2132_; 
v_size_2132_ = lean_ctor_get(v_r_2096_, 0);
lean_inc(v_size_2132_);
v___y_2106_ = v___x_2131_;
v___y_2107_ = v___x_2130_;
v___y_2108_ = v_size_2132_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_unsigned_to_nat(0u);
v___y_2106_ = v___x_2131_;
v___y_2107_ = v___x_2130_;
v___y_2108_ = v___x_2133_;
goto v___jp_2105_;
}
}
}
}
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2143_ = lean_nat_add(v___x_1929_, v_size_1919_);
lean_dec(v_size_1919_);
v___x_2144_ = lean_nat_add(v___x_2143_, v_size_2079_);
lean_dec(v___x_2143_);
v___x_2145_ = lean_nat_add(v___x_1929_, v_size_2079_);
v___x_2146_ = lean_nat_add(v___x_2145_, v_size_2092_);
lean_dec(v___x_2145_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_tree_2076_);
lean_ctor_set(v___x_2073_, 3, v_r_1923_);
lean_ctor_set(v___x_2073_, 2, v_v_2078_);
lean_ctor_set(v___x_2073_, 1, v_k_2077_);
lean_ctor_set(v___x_2073_, 0, v___x_2146_);
v___x_2148_ = v___x_2073_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_r_1923_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_tree_2076_);
v___x_2148_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v___x_2148_);
lean_ctor_set(v___x_2089_, 0, v___x_2144_);
v___x_2150_ = v___x_2089_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_k_1920_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_v_1921_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v_l_1922_);
lean_ctor_set(v_reuseFailAlloc_2151_, 4, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1922_) == 0)
{
lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2182_; 
lean_inc_ref(v_l_1922_);
lean_inc(v_v_1921_);
lean_inc(v_k_1920_);
lean_inc(v_size_1919_);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_l_1748_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; lean_object* v_unused_2187_; 
v_unused_2183_ = lean_ctor_get(v_l_1748_, 4);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_l_1748_, 3);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_l_1748_, 2);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_l_1748_, 1);
lean_dec(v_unused_2186_);
v_unused_2187_ = lean_ctor_get(v_l_1748_, 0);
lean_dec(v_unused_2187_);
v___x_2160_ = v_l_1748_;
v_isShared_2161_ = v_isSharedCheck_2182_;
goto v_resetjp_2159_;
}
else
{
lean_dec(v_l_1748_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2182_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
if (lean_obj_tag(v_r_1923_) == 0)
{
lean_object* v_k_2162_; lean_object* v_v_2163_; lean_object* v_size_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v_k_2162_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_k_2162_);
v_v_2163_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_v_2163_);
lean_dec_ref(v___x_2075_);
v_size_2164_ = lean_ctor_get(v_r_1923_, 0);
v___x_2165_ = lean_nat_add(v___x_1929_, v_size_1919_);
lean_dec(v_size_1919_);
v___x_2166_ = lean_nat_add(v___x_1929_, v_size_2164_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_tree_2076_);
lean_ctor_set(v___x_2073_, 3, v_r_1923_);
lean_ctor_set(v___x_2073_, 2, v_v_2163_);
lean_ctor_set(v___x_2073_, 1, v_k_2162_);
lean_ctor_set(v___x_2073_, 0, v___x_2166_);
v___x_2168_ = v___x_2073_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2162_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2163_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_r_1923_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_tree_2076_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 4, v___x_2168_);
lean_ctor_set(v___x_2160_, 0, v___x_2165_);
v___x_2170_ = v___x_2160_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_1920_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_1921_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_l_1922_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
else
{
lean_object* v_k_2173_; lean_object* v_v_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec(v_size_1919_);
v_k_2173_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_k_2173_);
v_v_2174_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_v_2174_);
lean_dec_ref(v___x_2075_);
v___x_2175_ = lean_unsigned_to_nat(3u);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_r_1923_);
lean_ctor_set(v___x_2073_, 3, v_r_1923_);
lean_ctor_set(v___x_2073_, 2, v_v_2174_);
lean_ctor_set(v___x_2073_, 1, v_k_2173_);
lean_ctor_set(v___x_2073_, 0, v___x_1929_);
v___x_2177_ = v___x_2073_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2173_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2174_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_r_1923_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_r_1923_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 4, v___x_2177_);
lean_ctor_set(v___x_2160_, 0, v___x_2175_);
v___x_2179_ = v___x_2160_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_1920_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_1921_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_l_1922_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1923_) == 0)
{
lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2212_; 
lean_inc(v_l_1922_);
lean_inc(v_v_1921_);
lean_inc(v_k_1920_);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_l_1748_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; lean_object* v_unused_2216_; lean_object* v_unused_2217_; 
v_unused_2213_ = lean_ctor_get(v_l_1748_, 4);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_l_1748_, 3);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_l_1748_, 2);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_l_1748_, 1);
lean_dec(v_unused_2216_);
v_unused_2217_ = lean_ctor_get(v_l_1748_, 0);
lean_dec(v_unused_2217_);
v___x_2189_ = v_l_1748_;
v_isShared_2190_ = v_isSharedCheck_2212_;
goto v_resetjp_2188_;
}
else
{
lean_dec(v_l_1748_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2212_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_k_2191_; lean_object* v_v_2192_; lean_object* v_k_2193_; lean_object* v_v_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2208_; 
v_k_2191_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_k_2191_);
v_v_2192_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_v_2192_);
lean_dec_ref(v___x_2075_);
v_k_2193_ = lean_ctor_get(v_r_1923_, 1);
v_v_2194_ = lean_ctor_get(v_r_1923_, 2);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_r_1923_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; lean_object* v_unused_2211_; 
v_unused_2209_ = lean_ctor_get(v_r_1923_, 4);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_r_1923_, 3);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_r_1923_, 0);
lean_dec(v_unused_2211_);
v___x_2196_ = v_r_1923_;
v_isShared_2197_ = v_isSharedCheck_2208_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_v_2194_);
lean_inc(v_k_2193_);
lean_dec(v_r_1923_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2208_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(3u);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 4, v_l_1922_);
lean_ctor_set(v___x_2196_, 3, v_l_1922_);
lean_ctor_set(v___x_2196_, 2, v_v_1921_);
lean_ctor_set(v___x_2196_, 1, v_k_1920_);
lean_ctor_set(v___x_2196_, 0, v___x_1929_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_k_1920_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_v_1921_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v_l_1922_);
lean_ctor_set(v_reuseFailAlloc_2207_, 4, v_l_1922_);
v___x_2200_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2202_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_l_1922_);
lean_ctor_set(v___x_2073_, 3, v_l_1922_);
lean_ctor_set(v___x_2073_, 2, v_v_2192_);
lean_ctor_set(v___x_2073_, 1, v_k_2191_);
lean_ctor_set(v___x_2073_, 0, v___x_1929_);
v___x_2202_ = v___x_2073_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_k_2191_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_v_2192_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v_l_1922_);
lean_ctor_set(v_reuseFailAlloc_2206_, 4, v_l_1922_);
v___x_2202_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2204_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 4, v___x_2202_);
lean_ctor_set(v___x_2189_, 3, v___x_2200_);
lean_ctor_set(v___x_2189_, 2, v_v_2194_);
lean_ctor_set(v___x_2189_, 1, v_k_2193_);
lean_ctor_set(v___x_2189_, 0, v___x_2198_);
v___x_2204_ = v___x_2189_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_k_2193_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_v_2194_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
}
else
{
lean_object* v_k_2218_; lean_object* v_v_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v_k_2218_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_k_2218_);
v_v_2219_ = lean_ctor_get(v___x_2075_, 1);
lean_inc(v_v_2219_);
lean_dec_ref(v___x_2075_);
v___x_2220_ = lean_unsigned_to_nat(2u);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_r_1923_);
lean_ctor_set(v___x_2073_, 3, v_l_1748_);
lean_ctor_set(v___x_2073_, 2, v_v_2219_);
lean_ctor_set(v___x_2073_, 1, v_k_2218_);
lean_ctor_set(v___x_2073_, 0, v___x_2220_);
v___x_2222_ = v___x_2073_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2218_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2219_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_l_1748_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_r_1923_);
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
}
else
{
return v_l_1748_;
}
}
else
{
return v_r_1749_;
}
}
}
else
{
lean_object* v_impl_2230_; lean_object* v___x_2231_; 
v_impl_2230_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1744_, v_l_1748_);
v___x_2231_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2230_) == 0)
{
if (lean_obj_tag(v_r_1749_) == 0)
{
lean_object* v_size_2232_; lean_object* v_size_2233_; lean_object* v_k_2234_; lean_object* v_v_2235_; lean_object* v_l_2236_; lean_object* v_r_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v_size_2232_ = lean_ctor_get(v_impl_2230_, 0);
lean_inc(v_size_2232_);
v_size_2233_ = lean_ctor_get(v_r_1749_, 0);
v_k_2234_ = lean_ctor_get(v_r_1749_, 1);
v_v_2235_ = lean_ctor_get(v_r_1749_, 2);
v_l_2236_ = lean_ctor_get(v_r_1749_, 3);
lean_inc(v_l_2236_);
v_r_2237_ = lean_ctor_get(v_r_1749_, 4);
v___x_2238_ = lean_unsigned_to_nat(3u);
v___x_2239_ = lean_nat_mul(v___x_2238_, v_size_2232_);
v___x_2240_ = lean_nat_dec_lt(v___x_2239_, v_size_2233_);
lean_dec(v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
lean_dec(v_l_2236_);
v___x_2241_ = lean_nat_add(v___x_2231_, v_size_2232_);
lean_dec(v_size_2232_);
v___x_2242_ = lean_nat_add(v___x_2241_, v_size_2233_);
lean_dec(v___x_2241_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 3, v_impl_2230_);
lean_ctor_set(v___x_1751_, 0, v___x_2242_);
v___x_2244_ = v___x_1751_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2245_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2245_, 3, v_impl_2230_);
lean_ctor_set(v_reuseFailAlloc_2245_, 4, v_r_1749_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
else
{
lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2309_; 
lean_inc(v_r_2237_);
lean_inc(v_v_2235_);
lean_inc(v_k_2234_);
lean_inc(v_size_2233_);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_r_1749_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; lean_object* v_unused_2311_; lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; 
v_unused_2310_ = lean_ctor_get(v_r_1749_, 4);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_r_1749_, 3);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_r_1749_, 2);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_r_1749_, 1);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_r_1749_, 0);
lean_dec(v_unused_2314_);
v___x_2247_ = v_r_1749_;
v_isShared_2248_ = v_isSharedCheck_2309_;
goto v_resetjp_2246_;
}
else
{
lean_dec(v_r_1749_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2309_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_size_2249_; lean_object* v_k_2250_; lean_object* v_v_2251_; lean_object* v_l_2252_; lean_object* v_r_2253_; lean_object* v_size_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v_size_2249_ = lean_ctor_get(v_l_2236_, 0);
v_k_2250_ = lean_ctor_get(v_l_2236_, 1);
v_v_2251_ = lean_ctor_get(v_l_2236_, 2);
v_l_2252_ = lean_ctor_get(v_l_2236_, 3);
v_r_2253_ = lean_ctor_get(v_l_2236_, 4);
v_size_2254_ = lean_ctor_get(v_r_2237_, 0);
v___x_2255_ = lean_unsigned_to_nat(2u);
v___x_2256_ = lean_nat_mul(v___x_2255_, v_size_2254_);
v___x_2257_ = lean_nat_dec_lt(v_size_2249_, v___x_2256_);
lean_dec(v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2285_; 
lean_inc(v_r_2253_);
lean_inc(v_l_2252_);
lean_inc(v_v_2251_);
lean_inc(v_k_2250_);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_l_2236_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; lean_object* v_unused_2287_; lean_object* v_unused_2288_; lean_object* v_unused_2289_; lean_object* v_unused_2290_; 
v_unused_2286_ = lean_ctor_get(v_l_2236_, 4);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_l_2236_, 3);
lean_dec(v_unused_2287_);
v_unused_2288_ = lean_ctor_get(v_l_2236_, 2);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_l_2236_, 1);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_l_2236_, 0);
lean_dec(v_unused_2290_);
v___x_2259_ = v_l_2236_;
v_isShared_2260_ = v_isSharedCheck_2285_;
goto v_resetjp_2258_;
}
else
{
lean_dec(v_l_2236_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2285_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2275_; 
v___x_2261_ = lean_nat_add(v___x_2231_, v_size_2232_);
lean_dec(v_size_2232_);
v___x_2262_ = lean_nat_add(v___x_2261_, v_size_2233_);
lean_dec(v_size_2233_);
if (lean_obj_tag(v_l_2252_) == 0)
{
lean_object* v_size_2283_; 
v_size_2283_ = lean_ctor_get(v_l_2252_, 0);
lean_inc(v_size_2283_);
v___y_2275_ = v_size_2283_;
goto v___jp_2274_;
}
else
{
lean_object* v___x_2284_; 
v___x_2284_ = lean_unsigned_to_nat(0u);
v___y_2275_ = v___x_2284_;
goto v___jp_2274_;
}
v___jp_2263_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = lean_nat_add(v___y_2264_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec(v___y_2264_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 4, v_r_2237_);
lean_ctor_set(v___x_2259_, 3, v_r_2253_);
lean_ctor_set(v___x_2259_, 2, v_v_2235_);
lean_ctor_set(v___x_2259_, 1, v_k_2234_);
lean_ctor_set(v___x_2259_, 0, v___x_2267_);
v___x_2269_ = v___x_2259_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_k_2234_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_v_2235_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v_r_2253_);
lean_ctor_set(v_reuseFailAlloc_2273_, 4, v_r_2237_);
v___x_2269_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 4, v___x_2269_);
lean_ctor_set(v___x_2247_, 3, v___y_2265_);
lean_ctor_set(v___x_2247_, 2, v_v_2251_);
lean_ctor_set(v___x_2247_, 1, v_k_2250_);
lean_ctor_set(v___x_2247_, 0, v___x_2262_);
v___x_2271_ = v___x_2247_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_k_2250_);
lean_ctor_set(v_reuseFailAlloc_2272_, 2, v_v_2251_);
lean_ctor_set(v_reuseFailAlloc_2272_, 3, v___y_2265_);
lean_ctor_set(v_reuseFailAlloc_2272_, 4, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
v___jp_2274_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = lean_nat_add(v___x_2261_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec(v___x_2261_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_l_2252_);
lean_ctor_set(v___x_1751_, 3, v_impl_2230_);
lean_ctor_set(v___x_1751_, 0, v___x_2276_);
v___x_2278_ = v___x_1751_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_impl_2230_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_l_2252_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_nat_add(v___x_2231_, v_size_2254_);
if (lean_obj_tag(v_r_2253_) == 0)
{
lean_object* v_size_2280_; 
v_size_2280_ = lean_ctor_get(v_r_2253_, 0);
lean_inc(v_size_2280_);
v___y_2264_ = v___x_2279_;
v___y_2265_ = v___x_2278_;
v___y_2266_ = v_size_2280_;
goto v___jp_2263_;
}
else
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_unsigned_to_nat(0u);
v___y_2264_ = v___x_2279_;
v___y_2265_ = v___x_2278_;
v___y_2266_ = v___x_2281_;
goto v___jp_2263_;
}
}
}
}
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
lean_del_object(v___x_1751_);
v___x_2291_ = lean_nat_add(v___x_2231_, v_size_2232_);
lean_dec(v_size_2232_);
v___x_2292_ = lean_nat_add(v___x_2291_, v_size_2233_);
lean_dec(v_size_2233_);
v___x_2293_ = lean_nat_add(v___x_2291_, v_size_2249_);
lean_dec(v___x_2291_);
lean_inc_ref(v_impl_2230_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 4, v_l_2236_);
lean_ctor_set(v___x_2247_, 3, v_impl_2230_);
lean_ctor_set(v___x_2247_, 2, v_v_1747_);
lean_ctor_set(v___x_2247_, 1, v_k_1746_);
lean_ctor_set(v___x_2247_, 0, v___x_2293_);
v___x_2295_ = v___x_2247_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_impl_2230_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_l_2236_);
v___x_2295_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
v_isSharedCheck_2302_ = !lean_is_exclusive(v_impl_2230_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; lean_object* v_unused_2304_; lean_object* v_unused_2305_; lean_object* v_unused_2306_; lean_object* v_unused_2307_; 
v_unused_2303_ = lean_ctor_get(v_impl_2230_, 4);
lean_dec(v_unused_2303_);
v_unused_2304_ = lean_ctor_get(v_impl_2230_, 3);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_impl_2230_, 2);
lean_dec(v_unused_2305_);
v_unused_2306_ = lean_ctor_get(v_impl_2230_, 1);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_impl_2230_, 0);
lean_dec(v_unused_2307_);
v___x_2297_ = v_impl_2230_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_dec(v_impl_2230_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 4, v_r_2237_);
lean_ctor_set(v___x_2297_, 3, v___x_2295_);
lean_ctor_set(v___x_2297_, 2, v_v_2235_);
lean_ctor_set(v___x_2297_, 1, v_k_2234_);
lean_ctor_set(v___x_2297_, 0, v___x_2292_);
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_k_2234_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_v_2235_);
lean_ctor_set(v_reuseFailAlloc_2301_, 3, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2301_, 4, v_r_2237_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v_size_2315_ = lean_ctor_get(v_impl_2230_, 0);
lean_inc(v_size_2315_);
v___x_2316_ = lean_nat_add(v___x_2231_, v_size_2315_);
lean_dec(v_size_2315_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 3, v_impl_2230_);
lean_ctor_set(v___x_1751_, 0, v___x_2316_);
v___x_2318_ = v___x_1751_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_impl_2230_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_r_1749_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
if (lean_obj_tag(v_r_1749_) == 0)
{
lean_object* v_l_2320_; 
v_l_2320_ = lean_ctor_get(v_r_1749_, 3);
lean_inc(v_l_2320_);
if (lean_obj_tag(v_l_2320_) == 0)
{
lean_object* v_r_2321_; 
v_r_2321_ = lean_ctor_get(v_r_1749_, 4);
lean_inc(v_r_2321_);
if (lean_obj_tag(v_r_2321_) == 0)
{
lean_object* v_size_2322_; lean_object* v_k_2323_; lean_object* v_v_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2337_; 
v_size_2322_ = lean_ctor_get(v_r_1749_, 0);
v_k_2323_ = lean_ctor_get(v_r_1749_, 1);
v_v_2324_ = lean_ctor_get(v_r_1749_, 2);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_r_1749_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; lean_object* v_unused_2339_; 
v_unused_2338_ = lean_ctor_get(v_r_1749_, 4);
lean_dec(v_unused_2338_);
v_unused_2339_ = lean_ctor_get(v_r_1749_, 3);
lean_dec(v_unused_2339_);
v___x_2326_ = v_r_1749_;
v_isShared_2327_ = v_isSharedCheck_2337_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_v_2324_);
lean_inc(v_k_2323_);
lean_inc(v_size_2322_);
lean_dec(v_r_1749_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2337_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_size_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
v_size_2328_ = lean_ctor_get(v_l_2320_, 0);
v___x_2329_ = lean_nat_add(v___x_2231_, v_size_2322_);
lean_dec(v_size_2322_);
v___x_2330_ = lean_nat_add(v___x_2231_, v_size_2328_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 4, v_l_2320_);
lean_ctor_set(v___x_2326_, 3, v_impl_2230_);
lean_ctor_set(v___x_2326_, 2, v_v_1747_);
lean_ctor_set(v___x_2326_, 1, v_k_1746_);
lean_ctor_set(v___x_2326_, 0, v___x_2330_);
v___x_2332_ = v___x_2326_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2336_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2336_, 3, v_impl_2230_);
lean_ctor_set(v_reuseFailAlloc_2336_, 4, v_l_2320_);
v___x_2332_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_r_2321_);
lean_ctor_set(v___x_1751_, 3, v___x_2332_);
lean_ctor_set(v___x_1751_, 2, v_v_2324_);
lean_ctor_set(v___x_1751_, 1, v_k_2323_);
lean_ctor_set(v___x_1751_, 0, v___x_2329_);
v___x_2334_ = v___x_1751_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2323_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2324_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_r_2321_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
else
{
lean_object* v_k_2340_; lean_object* v_v_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2364_; 
v_k_2340_ = lean_ctor_get(v_r_1749_, 1);
v_v_2341_ = lean_ctor_get(v_r_1749_, 2);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_r_1749_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; lean_object* v_unused_2366_; lean_object* v_unused_2367_; 
v_unused_2365_ = lean_ctor_get(v_r_1749_, 4);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_r_1749_, 3);
lean_dec(v_unused_2366_);
v_unused_2367_ = lean_ctor_get(v_r_1749_, 0);
lean_dec(v_unused_2367_);
v___x_2343_ = v_r_1749_;
v_isShared_2344_ = v_isSharedCheck_2364_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_v_2341_);
lean_inc(v_k_2340_);
lean_dec(v_r_1749_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2364_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_k_2345_; lean_object* v_v_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2360_; 
v_k_2345_ = lean_ctor_get(v_l_2320_, 1);
v_v_2346_ = lean_ctor_get(v_l_2320_, 2);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_l_2320_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; lean_object* v_unused_2362_; lean_object* v_unused_2363_; 
v_unused_2361_ = lean_ctor_get(v_l_2320_, 4);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_l_2320_, 3);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_l_2320_, 0);
lean_dec(v_unused_2363_);
v___x_2348_ = v_l_2320_;
v_isShared_2349_ = v_isSharedCheck_2360_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_v_2346_);
lean_inc(v_k_2345_);
lean_dec(v_l_2320_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2360_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2350_ = lean_unsigned_to_nat(3u);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 4, v_r_2321_);
lean_ctor_set(v___x_2348_, 3, v_r_2321_);
lean_ctor_set(v___x_2348_, 2, v_v_1747_);
lean_ctor_set(v___x_2348_, 1, v_k_1746_);
lean_ctor_set(v___x_2348_, 0, v___x_2231_);
v___x_2352_ = v___x_2348_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_r_2321_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_r_2321_);
v___x_2352_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 3, v_r_2321_);
lean_ctor_set(v___x_2343_, 0, v___x_2231_);
v___x_2354_ = v___x_2343_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2340_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2341_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_r_2321_);
lean_ctor_set(v_reuseFailAlloc_2358_, 4, v_r_2321_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v___x_2354_);
lean_ctor_set(v___x_1751_, 3, v___x_2352_);
lean_ctor_set(v___x_1751_, 2, v_v_2346_);
lean_ctor_set(v___x_1751_, 1, v_k_2345_);
lean_ctor_set(v___x_1751_, 0, v___x_2350_);
v___x_2356_ = v___x_1751_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_k_2345_);
lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_v_2346_);
lean_ctor_set(v_reuseFailAlloc_2357_, 3, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2357_, 4, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2368_; 
v_r_2368_ = lean_ctor_get(v_r_1749_, 4);
lean_inc(v_r_2368_);
if (lean_obj_tag(v_r_2368_) == 0)
{
lean_object* v_k_2369_; lean_object* v_v_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2381_; 
v_k_2369_ = lean_ctor_get(v_r_1749_, 1);
v_v_2370_ = lean_ctor_get(v_r_1749_, 2);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_r_1749_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; lean_object* v_unused_2383_; lean_object* v_unused_2384_; 
v_unused_2382_ = lean_ctor_get(v_r_1749_, 4);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_r_1749_, 3);
lean_dec(v_unused_2383_);
v_unused_2384_ = lean_ctor_get(v_r_1749_, 0);
lean_dec(v_unused_2384_);
v___x_2372_ = v_r_1749_;
v_isShared_2373_ = v_isSharedCheck_2381_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_v_2370_);
lean_inc(v_k_2369_);
lean_dec(v_r_1749_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2381_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = lean_unsigned_to_nat(3u);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 4, v_l_2320_);
lean_ctor_set(v___x_2372_, 2, v_v_1747_);
lean_ctor_set(v___x_2372_, 1, v_k_1746_);
lean_ctor_set(v___x_2372_, 0, v___x_2231_);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2380_, 3, v_l_2320_);
lean_ctor_set(v_reuseFailAlloc_2380_, 4, v_l_2320_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_r_2368_);
lean_ctor_set(v___x_1751_, 3, v___x_2376_);
lean_ctor_set(v___x_1751_, 2, v_v_2370_);
lean_ctor_set(v___x_1751_, 1, v_k_2369_);
lean_ctor_set(v___x_1751_, 0, v___x_2374_);
v___x_2378_ = v___x_1751_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_k_2369_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_v_2370_);
lean_ctor_set(v_reuseFailAlloc_2379_, 3, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2379_, 4, v_r_2368_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_size_2385_; lean_object* v_k_2386_; lean_object* v_v_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2398_; 
v_size_2385_ = lean_ctor_get(v_r_1749_, 0);
v_k_2386_ = lean_ctor_get(v_r_1749_, 1);
v_v_2387_ = lean_ctor_get(v_r_1749_, 2);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_r_1749_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; lean_object* v_unused_2400_; 
v_unused_2399_ = lean_ctor_get(v_r_1749_, 4);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_r_1749_, 3);
lean_dec(v_unused_2400_);
v___x_2389_ = v_r_1749_;
v_isShared_2390_ = v_isSharedCheck_2398_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_v_2387_);
lean_inc(v_k_2386_);
lean_inc(v_size_2385_);
lean_dec(v_r_1749_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2398_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 3, v_r_2368_);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_size_2385_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_2386_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_2387_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_r_2368_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_r_2368_);
v___x_2392_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = lean_unsigned_to_nat(2u);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v___x_2392_);
lean_ctor_set(v___x_1751_, 3, v_r_2368_);
lean_ctor_set(v___x_1751_, 0, v___x_2393_);
v___x_2395_ = v___x_1751_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2396_, 3, v_r_2368_);
lean_ctor_set(v_reuseFailAlloc_2396_, 4, v___x_2392_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
}
else
{
lean_object* v___x_2402_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 3, v_r_1749_);
lean_ctor_set(v___x_1751_, 0, v___x_2231_);
v___x_2402_ = v___x_1751_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_k_1746_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_v_1747_);
lean_ctor_set(v_reuseFailAlloc_2403_, 3, v_r_1749_);
lean_ctor_set(v_reuseFailAlloc_2403_, 4, v_r_1749_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
}
else
{
return v_t_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2406_, lean_object* v_t_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2406_, v_t_2407_);
lean_dec(v_k_2406_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v_capacity_2413_; lean_object* v_buffer_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2412_ = lean_st_ref_get(v_a_2410_);
v_capacity_2413_ = lean_ctor_get(v___x_2412_, 2);
lean_inc(v_capacity_2413_);
v_buffer_2414_ = lean_ctor_get(v___x_2412_, 4);
lean_inc_ref(v_buffer_2414_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_nat_mod(v_place_2409_, v_capacity_2413_);
lean_dec(v_capacity_2413_);
v___x_2416_ = lean_array_fget(v_buffer_2414_, v___x_2415_);
lean_dec(v___x_2415_);
lean_dec_ref(v_buffer_2414_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_2418_, lean_object* v_a_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec(v_place_2418_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v_size_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2424_ = lean_st_ref_get(v_a_2422_);
v_size_2425_ = lean_ctor_get(v___x_2424_, 3);
lean_inc(v_size_2425_);
lean_dec(v___x_2424_);
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = lean_nat_dec_eq(v_size_2425_, v___x_2426_);
lean_dec(v_size_2425_);
v___x_2428_ = lean_box(v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2430_);
lean_dec(v_a_2430_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_2433_, lean_object* v_next_2434_){
_start:
{
lean_object* v___x_2436_; lean_object* v_fst_2438_; lean_object* v_snd_2439_; lean_object* v_value_2442_; lean_object* v_pos_2443_; lean_object* v_remaining_2444_; uint8_t v___x_2445_; 
v___x_2436_ = lean_st_ref_take(v_slot_2433_);
v_value_2442_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_value_2442_);
v_pos_2443_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_pos_2443_);
v_remaining_2444_ = lean_ctor_get(v___x_2436_, 2);
lean_inc(v_remaining_2444_);
v___x_2445_ = lean_nat_dec_eq(v_next_2434_, v_pos_2443_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_dec(v_remaining_2444_);
lean_dec(v_pos_2443_);
lean_dec(v_value_2442_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_box(v___x_2445_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v_fst_2438_ = v___x_2448_;
v_snd_2439_ = v___x_2436_;
goto v___jp_2437_;
}
else
{
lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2467_; 
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; lean_object* v_unused_2469_; lean_object* v_unused_2470_; 
v_unused_2468_ = lean_ctor_get(v___x_2436_, 2);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v___x_2436_, 1);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v___x_2436_, 0);
lean_dec(v_unused_2470_);
v___x_2450_ = v___x_2436_;
v_isShared_2451_ = v_isSharedCheck_2467_;
goto v_resetjp_2449_;
}
else
{
lean_dec(v___x_2436_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2467_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2452_ = lean_unsigned_to_nat(1u);
v___x_2453_ = lean_nat_dec_eq(v_remaining_2444_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2454_ = lean_box(v___x_2453_);
lean_inc(v_value_2442_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_value_2442_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = lean_nat_sub(v_remaining_2444_, v___x_2452_);
lean_dec(v_remaining_2444_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 2, v___x_2456_);
v___x_2458_ = v___x_2450_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_value_2442_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_pos_2443_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
v_fst_2438_ = v___x_2455_;
v_snd_2439_ = v___x_2458_;
goto v___jp_2437_;
}
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_dec(v_remaining_2444_);
v___x_2460_ = lean_box(v___x_2445_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_value_2442_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_box(0);
v___x_2463_ = lean_unsigned_to_nat(0u);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 2, v___x_2463_);
lean_ctor_set(v___x_2450_, 0, v___x_2462_);
v___x_2465_ = v___x_2450_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_pos_2443_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
v_fst_2438_ = v___x_2461_;
v_snd_2439_ = v___x_2465_;
goto v___jp_2437_;
}
}
}
}
v___jp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = lean_st_ref_set(v_slot_2433_, v_snd_2439_);
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_fst_2438_);
return v___x_2441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_2471_, lean_object* v_next_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2471_, v_next_2472_);
lean_dec(v_next_2472_);
lean_dec(v_slot_2471_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2551_; 
v___x_2478_ = lean_st_ref_get(v_a_2476_);
v___x_2479_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2476_);
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2551_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2551_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_unbox(v_a_2480_);
lean_dec(v_a_2480_);
if (v___x_2484_ == 0)
{
lean_object* v_capacity_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2546_; 
lean_del_object(v___x_2482_);
v_capacity_2485_ = lean_ctor_get(v___x_2478_, 2);
lean_inc(v_capacity_2485_);
v___x_2486_ = lean_nat_mod(v_next_2475_, v_capacity_2485_);
lean_dec(v_capacity_2485_);
v___x_2487_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_2486_, v_a_2476_);
lean_dec(v___x_2486_);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2546_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2546_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2545_; 
v___x_2492_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_2488_, v_next_2475_);
lean_dec(v_a_2488_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2545_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2545_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_fst_2497_; lean_object* v_snd_2498_; lean_object* v_st_2500_; lean_object* v___y_2501_; 
v_fst_2497_ = lean_ctor_get(v_a_2493_, 0);
lean_inc(v_fst_2497_);
v_snd_2498_ = lean_ctor_get(v_a_2493_, 1);
lean_inc(v_snd_2498_);
lean_dec(v_a_2493_);
if (lean_obj_tag(v_fst_2497_) == 1)
{
uint8_t v___x_2506_; 
lean_del_object(v___x_2490_);
v___x_2506_ = lean_unbox(v_snd_2498_);
if (v___x_2506_ == 0)
{
lean_dec(v_snd_2498_);
v_st_2500_ = v___x_2478_;
v___y_2501_ = v_a_2476_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2507_; lean_object* v_producers_2508_; lean_object* v_waiters_2509_; lean_object* v_capacity_2510_; lean_object* v_size_2511_; lean_object* v_buffer_2512_; lean_object* v_write_2513_; lean_object* v_read_2514_; lean_object* v_receivers_2515_; lean_object* v_nextId_2516_; uint8_t v_closed_2517_; lean_object* v_pos_2518_; lean_object* v___x_2519_; 
v___x_2507_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_2478_);
v_producers_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc_ref(v_producers_2508_);
v_waiters_2509_ = lean_ctor_get(v___x_2507_, 1);
lean_inc_ref(v_waiters_2509_);
v_capacity_2510_ = lean_ctor_get(v___x_2507_, 2);
lean_inc(v_capacity_2510_);
v_size_2511_ = lean_ctor_get(v___x_2507_, 3);
lean_inc(v_size_2511_);
v_buffer_2512_ = lean_ctor_get(v___x_2507_, 4);
lean_inc_ref(v_buffer_2512_);
v_write_2513_ = lean_ctor_get(v___x_2507_, 5);
lean_inc(v_write_2513_);
v_read_2514_ = lean_ctor_get(v___x_2507_, 6);
lean_inc(v_read_2514_);
v_receivers_2515_ = lean_ctor_get(v___x_2507_, 7);
lean_inc(v_receivers_2515_);
v_nextId_2516_ = lean_ctor_get(v___x_2507_, 8);
lean_inc(v_nextId_2516_);
v_closed_2517_ = lean_ctor_get_uint8(v___x_2507_, sizeof(void*)*10);
v_pos_2518_ = lean_ctor_get(v___x_2507_, 9);
lean_inc(v_pos_2518_);
v___x_2519_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2508_);
if (lean_obj_tag(v___x_2519_) == 1)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2530_; 
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; lean_object* v_unused_2532_; lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2531_ = lean_ctor_get(v___x_2507_, 9);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v___x_2507_, 8);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v___x_2507_, 7);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v___x_2507_, 6);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v___x_2507_, 5);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v___x_2507_, 4);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v___x_2507_, 3);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v___x_2507_, 2);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v___x_2507_, 1);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v___x_2507_, 0);
lean_dec(v_unused_2540_);
v___x_2521_ = v___x_2507_;
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v___x_2507_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2530_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v_val_2523_; lean_object* v_fst_2524_; lean_object* v_snd_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v_val_2523_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_val_2523_);
lean_dec_ref(v___x_2519_);
v_fst_2524_ = lean_ctor_get(v_val_2523_, 0);
lean_inc(v_fst_2524_);
v_snd_2525_ = lean_ctor_get(v_val_2523_, 1);
lean_inc(v_snd_2525_);
lean_dec(v_val_2523_);
v___x_2526_ = lean_io_promise_resolve(v_snd_2498_, v_fst_2524_);
lean_dec(v_fst_2524_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v_snd_2525_);
v___x_2528_ = v___x_2521_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_snd_2525_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_waiters_2509_);
lean_ctor_set(v_reuseFailAlloc_2529_, 2, v_capacity_2510_);
lean_ctor_set(v_reuseFailAlloc_2529_, 3, v_size_2511_);
lean_ctor_set(v_reuseFailAlloc_2529_, 4, v_buffer_2512_);
lean_ctor_set(v_reuseFailAlloc_2529_, 5, v_write_2513_);
lean_ctor_set(v_reuseFailAlloc_2529_, 6, v_read_2514_);
lean_ctor_set(v_reuseFailAlloc_2529_, 7, v_receivers_2515_);
lean_ctor_set(v_reuseFailAlloc_2529_, 8, v_nextId_2516_);
lean_ctor_set(v_reuseFailAlloc_2529_, 9, v_pos_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2529_, sizeof(void*)*10, v_closed_2517_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
v_st_2500_ = v___x_2528_;
v___y_2501_ = v_a_2476_;
goto v___jp_2499_;
}
}
}
else
{
lean_dec(v___x_2519_);
lean_dec(v_pos_2518_);
lean_dec(v_nextId_2516_);
lean_dec(v_receivers_2515_);
lean_dec(v_read_2514_);
lean_dec(v_write_2513_);
lean_dec_ref(v_buffer_2512_);
lean_dec(v_size_2511_);
lean_dec(v_capacity_2510_);
lean_dec_ref(v_waiters_2509_);
lean_dec(v_snd_2498_);
v_st_2500_ = v___x_2507_;
v___y_2501_ = v_a_2476_;
goto v___jp_2499_;
}
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_dec(v_snd_2498_);
lean_dec(v_fst_2497_);
lean_del_object(v___x_2495_);
lean_dec(v___x_2478_);
v___x_2541_ = lean_box(0);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v___x_2541_);
v___x_2543_ = v___x_2490_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
v___jp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = lean_st_ref_set(v___y_2501_, v_st_2500_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v_fst_2497_);
v___x_2504_ = v___x_2495_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_fst_2497_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_dec(v___x_2478_);
v___x_2547_ = lean_box(0);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2547_);
v___x_2549_ = v___x_2482_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_2552_, lean_object* v_a_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec(v_next_2552_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_b_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2597_; 
v_fst_2559_ = lean_ctor_get(v_b_2556_, 0);
v_snd_2560_ = lean_ctor_get(v_b_2556_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_b_2556_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2562_ = v_b_2556_;
v_isShared_2563_ = v_isSharedCheck_2597_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snd_2560_);
lean_inc(v_fst_2559_);
lean_dec(v_b_2556_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2597_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v_size_2569_; lean_object* v_pos_2570_; uint8_t v___x_2571_; 
v_size_2569_ = lean_ctor_get(v_fst_2559_, 3);
v_pos_2570_ = lean_ctor_get(v_fst_2559_, 9);
v___x_2571_ = lean_nat_dec_lt(v_snd_2560_, v_pos_2570_);
if (v___x_2571_ == 0)
{
goto v___jp_2564_;
}
else
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = lean_nat_dec_lt(v___x_2572_, v_size_2569_);
if (v___x_2573_ == 0)
{
goto v___jp_2564_;
}
else
{
lean_object* v___x_2574_; 
lean_del_object(v___x_2562_);
v___x_2574_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_2560_, v___y_2557_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2588_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2588_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2588_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
if (lean_obj_tag(v_a_2575_) == 1)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec_ref(v_a_2575_);
lean_del_object(v___x_2577_);
lean_dec(v_fst_2559_);
v___x_2579_ = lean_st_ref_get(v___y_2557_);
v___x_2580_ = lean_unsigned_to_nat(1u);
v___x_2581_ = lean_nat_add(v_snd_2560_, v___x_2580_);
lean_dec(v_snd_2560_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2579_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v_b_2556_ = v___x_2582_;
goto _start;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_dec(v_a_2575_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_fst_2559_);
lean_ctor_set(v___x_2584_, 1, v_snd_2560_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2584_);
v___x_2586_ = v___x_2577_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec(v_snd_2560_);
lean_dec(v_fst_2559_);
v_a_2589_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2574_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2574_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
v___jp_2564_:
{
lean_object* v___x_2566_; 
if (v_isShared_2563_ == 0)
{
v___x_2566_ = v___x_2562_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_fst_2559_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_snd_2560_);
v___x_2566_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_b_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_b_2598_, v___y_2599_);
lean_dec(v___y_2599_);
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
lean_dec_ref(v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2610_);
lean_ctor_set(v___x_2614_, 1, v_val_2613_);
v___x_2615_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2614_, v___y_2608_);
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
v___x_2638_ = lean_st_ref_set(v___y_2608_, v___x_2637_);
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
lean_dec_ref(v_a_2666_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2758_, lean_object* v_b_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_b_2759_, v___y_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2763_, v_b_2764_, v___y_2765_);
lean_dec(v___y_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2768_, lean_object* v_k_2769_, lean_object* v_t_2770_, lean_object* v_h_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2769_, v_t_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2773_, lean_object* v_k_2774_, lean_object* v_t_2775_, lean_object* v_h_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2773_, v_k_2774_, v_t_2775_, v_h_2776_);
lean_dec(v_k_2774_);
return v_res_2777_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2778_, lean_object* v_y_2779_){
_start:
{
uint8_t v___x_2780_; 
v___x_2780_ = lean_nat_dec_lt(v_x_2778_, v_y_2779_);
if (v___x_2780_ == 0)
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_nat_dec_eq(v_x_2778_, v_y_2779_);
if (v___x_2781_ == 0)
{
uint8_t v___x_2782_; 
v___x_2782_ = 2;
return v___x_2782_;
}
else
{
uint8_t v___x_2783_; 
v___x_2783_ = 1;
return v___x_2783_;
}
}
else
{
uint8_t v___x_2784_; 
v___x_2784_ = 0;
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2785_, lean_object* v_y_2786_){
_start:
{
uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2785_, v_y_2786_);
lean_dec(v_y_2786_);
lean_dec(v_x_2785_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_unsigned_to_nat(1u);
v___x_2791_ = lean_nat_add(v_x_2789_, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2792_);
lean_dec(v_x_2792_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2794_, lean_object* v_receiverId_2795_, lean_object* v___f_2796_, lean_object* v_receivers_2797_, lean_object* v_s_2798_){
_start:
{
lean_object* v_producers_2799_; lean_object* v_waiters_2800_; lean_object* v_capacity_2801_; lean_object* v_size_2802_; lean_object* v_buffer_2803_; lean_object* v_write_2804_; lean_object* v_read_2805_; lean_object* v_nextId_2806_; uint8_t v_closed_2807_; lean_object* v_pos_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2818_; 
v_producers_2799_ = lean_ctor_get(v_s_2798_, 0);
v_waiters_2800_ = lean_ctor_get(v_s_2798_, 1);
v_capacity_2801_ = lean_ctor_get(v_s_2798_, 2);
v_size_2802_ = lean_ctor_get(v_s_2798_, 3);
v_buffer_2803_ = lean_ctor_get(v_s_2798_, 4);
v_write_2804_ = lean_ctor_get(v_s_2798_, 5);
v_read_2805_ = lean_ctor_get(v_s_2798_, 6);
v_nextId_2806_ = lean_ctor_get(v_s_2798_, 8);
v_closed_2807_ = lean_ctor_get_uint8(v_s_2798_, sizeof(void*)*10);
v_pos_2808_ = lean_ctor_get(v_s_2798_, 9);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_s_2798_);
if (v_isSharedCheck_2818_ == 0)
{
lean_object* v_unused_2819_; 
v_unused_2819_ = lean_ctor_get(v_s_2798_, 7);
lean_dec(v_unused_2819_);
v___x_2810_ = v_s_2798_;
v_isShared_2811_ = v_isSharedCheck_2818_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_pos_2808_);
lean_inc(v_nextId_2806_);
lean_inc(v_read_2805_);
lean_inc(v_write_2804_);
lean_inc(v_buffer_2803_);
lean_inc(v_size_2802_);
lean_inc(v_capacity_2801_);
lean_inc(v_waiters_2800_);
lean_inc(v_producers_2799_);
lean_dec(v_s_2798_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2818_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2812_ = lean_box(0);
v___x_2813_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2794_, v_receiverId_2795_, v___f_2796_, v_receivers_2797_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 7, v___x_2813_);
v___x_2815_ = v___x_2810_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_producers_2799_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_waiters_2800_);
lean_ctor_set(v_reuseFailAlloc_2817_, 2, v_capacity_2801_);
lean_ctor_set(v_reuseFailAlloc_2817_, 3, v_size_2802_);
lean_ctor_set(v_reuseFailAlloc_2817_, 4, v_buffer_2803_);
lean_ctor_set(v_reuseFailAlloc_2817_, 5, v_write_2804_);
lean_ctor_set(v_reuseFailAlloc_2817_, 6, v_read_2805_);
lean_ctor_set(v_reuseFailAlloc_2817_, 7, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2817_, 8, v_nextId_2806_);
lean_ctor_set(v_reuseFailAlloc_2817_, 9, v_pos_2808_);
lean_ctor_set_uint8(v_reuseFailAlloc_2817_, sizeof(void*)*10, v_closed_2807_);
v___x_2815_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; 
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2812_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
return v___x_2816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v_toPure_2823_; lean_object* v___x_2824_; 
v_toPure_2823_ = lean_ctor_get(v_toApplicative_2820_, 1);
lean_inc(v_toPure_2823_);
lean_dec_ref(v_toApplicative_2820_);
v___x_2824_ = lean_apply_2(v_toPure_2823_, lean_box(0), v_a_2821_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2825_, lean_object* v_a_2826_, lean_object* v___f_2827_, lean_object* v_inst_2828_, lean_object* v_toBind_2829_, lean_object* v_a_2830_){
_start:
{
if (lean_obj_tag(v_a_2830_) == 1)
{
lean_object* v___f_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___f_2831_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2831_, 0, v_toApplicative_2825_);
lean_closure_set(v___f_2831_, 1, v_a_2830_);
lean_inc(v_a_2826_);
v___x_2832_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2832_, 0, lean_box(0));
lean_closure_set(v___x_2832_, 1, lean_box(0));
lean_closure_set(v___x_2832_, 2, lean_box(0));
lean_closure_set(v___x_2832_, 3, v_a_2826_);
lean_closure_set(v___x_2832_, 4, v___f_2827_);
v___x_2833_ = lean_apply_2(v_inst_2828_, lean_box(0), v___x_2832_);
v___x_2834_ = lean_apply_4(v_toBind_2829_, lean_box(0), lean_box(0), v___x_2833_, v___f_2831_);
return v___x_2834_;
}
else
{
lean_object* v_toPure_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v_a_2830_);
lean_dec(v_toBind_2829_);
lean_dec(v_inst_2828_);
lean_dec_ref(v___f_2827_);
v_toPure_2835_ = lean_ctor_get(v_toApplicative_2825_, 1);
lean_inc(v_toPure_2835_);
lean_dec_ref(v_toApplicative_2825_);
v___x_2836_ = lean_box(0);
v___x_2837_ = lean_apply_2(v_toPure_2835_, lean_box(0), v___x_2836_);
return v___x_2837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_2838_, lean_object* v_a_2839_, lean_object* v___f_2840_, lean_object* v_inst_2841_, lean_object* v_toBind_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(v_toApplicative_2838_, v_a_2839_, v___f_2840_, v_inst_2841_, v_toBind_2842_, v_a_2843_);
lean_dec(v_a_2839_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2845_, lean_object* v_receiverId_2846_, lean_object* v___f_2847_, lean_object* v___f_2848_, lean_object* v_toApplicative_2849_, lean_object* v_a_2850_, lean_object* v_inst_2851_, lean_object* v_toBind_2852_, lean_object* v_inst_2853_, lean_object* v_inst_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v_receivers_2856_; lean_object* v___x_2857_; 
v_receivers_2856_ = lean_ctor_get(v_a_2855_, 7);
lean_inc_n(v_receivers_2856_, 2);
lean_dec_ref(v_a_2855_);
lean_inc(v_receiverId_2846_);
v___x_2857_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2845_, v_receivers_2856_, v_receiverId_2846_);
if (lean_obj_tag(v___x_2857_) == 1)
{
lean_object* v_val_2858_; lean_object* v___f_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_val_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_val_2858_);
lean_dec_ref(v___x_2857_);
v___f_2859_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2859_, 0, v___f_2847_);
lean_closure_set(v___f_2859_, 1, v_receiverId_2846_);
lean_closure_set(v___f_2859_, 2, v___f_2848_);
lean_closure_set(v___f_2859_, 3, v_receivers_2856_);
lean_inc(v_toBind_2852_);
lean_inc(v_inst_2851_);
lean_inc(v_a_2850_);
v___f_2860_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2860_, 0, v_toApplicative_2849_);
lean_closure_set(v___f_2860_, 1, v_a_2850_);
lean_closure_set(v___f_2860_, 2, v___f_2859_);
lean_closure_set(v___f_2860_, 3, v_inst_2851_);
lean_closure_set(v___f_2860_, 4, v_toBind_2852_);
v___x_2861_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2853_, v_inst_2851_, v_inst_2854_, v_val_2858_, v_a_2850_);
v___x_2862_ = lean_apply_4(v_toBind_2852_, lean_box(0), lean_box(0), v___x_2861_, v___f_2860_);
return v___x_2862_;
}
else
{
lean_object* v_toPure_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec(v___x_2857_);
lean_dec(v_receivers_2856_);
lean_dec(v_inst_2854_);
lean_dec_ref(v_inst_2853_);
lean_dec(v_toBind_2852_);
lean_dec(v_inst_2851_);
lean_dec_ref(v___f_2848_);
lean_dec_ref(v___f_2847_);
lean_dec(v_receiverId_2846_);
v_toPure_2863_ = lean_ctor_get(v_toApplicative_2849_, 1);
lean_inc(v_toPure_2863_);
lean_dec_ref(v_toApplicative_2849_);
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_apply_2(v_toPure_2863_, lean_box(0), v___x_2864_);
return v___x_2865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object* v___f_2866_, lean_object* v_receiverId_2867_, lean_object* v___f_2868_, lean_object* v___f_2869_, lean_object* v_toApplicative_2870_, lean_object* v_a_2871_, lean_object* v_inst_2872_, lean_object* v_toBind_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(v___f_2866_, v_receiverId_2867_, v___f_2868_, v___f_2869_, v_toApplicative_2870_, v_a_2871_, v_inst_2872_, v_toBind_2873_, v_inst_2874_, v_inst_2875_, v_a_2876_);
lean_dec(v_a_2871_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_2880_, lean_object* v_inst_2881_, lean_object* v_inst_2882_, lean_object* v_receiverId_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_toApplicative_2885_; lean_object* v_toBind_2886_; lean_object* v___f_2887_; lean_object* v___f_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_toApplicative_2885_ = lean_ctor_get(v_inst_2880_, 0);
lean_inc_ref(v_toApplicative_2885_);
v_toBind_2886_ = lean_ctor_get(v_inst_2880_, 1);
lean_inc_n(v_toBind_2886_, 2);
v___f_2887_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_2888_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_inst_2881_);
lean_inc_n(v_a_2884_, 2);
v___f_2889_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_2889_, 0, v___f_2887_);
lean_closure_set(v___f_2889_, 1, v_receiverId_2883_);
lean_closure_set(v___f_2889_, 2, v___f_2887_);
lean_closure_set(v___f_2889_, 3, v___f_2888_);
lean_closure_set(v___f_2889_, 4, v_toApplicative_2885_);
lean_closure_set(v___f_2889_, 5, v_a_2884_);
lean_closure_set(v___f_2889_, 6, v_inst_2881_);
lean_closure_set(v___f_2889_, 7, v_toBind_2886_);
lean_closure_set(v___f_2889_, 8, v_inst_2880_);
lean_closure_set(v___f_2889_, 9, v_inst_2882_);
v___x_2890_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2890_, 0, lean_box(0));
lean_closure_set(v___x_2890_, 1, lean_box(0));
lean_closure_set(v___x_2890_, 2, v_a_2884_);
v___x_2891_ = lean_apply_2(v_inst_2881_, lean_box(0), v___x_2890_);
v___x_2892_ = lean_apply_4(v_toBind_2886_, lean_box(0), lean_box(0), v___x_2891_, v___f_2889_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_receiverId_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2893_, v_inst_2894_, v_inst_2895_, v_receiverId_2896_, v_a_2897_);
lean_dec(v_a_2897_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_2899_, lean_object* v_00_u03b1_2900_, lean_object* v_inst_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_receiverId_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2901_, v_inst_2902_, v_inst_2903_, v_receiverId_2904_, v_a_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object* v_m_2907_, lean_object* v_00_u03b1_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_receiverId_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(v_m_2907_, v_00_u03b1_2908_, v_inst_2909_, v_inst_2910_, v_inst_2911_, v_receiverId_2912_, v_a_2913_);
lean_dec(v_a_2913_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_2915_, lean_object* v_t_2916_){
_start:
{
if (lean_obj_tag(v_t_2916_) == 0)
{
lean_object* v_size_2917_; lean_object* v_k_2918_; lean_object* v_v_2919_; lean_object* v_l_2920_; lean_object* v_r_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2940_; 
v_size_2917_ = lean_ctor_get(v_t_2916_, 0);
v_k_2918_ = lean_ctor_get(v_t_2916_, 1);
v_v_2919_ = lean_ctor_get(v_t_2916_, 2);
v_l_2920_ = lean_ctor_get(v_t_2916_, 3);
v_r_2921_ = lean_ctor_get(v_t_2916_, 4);
v_isSharedCheck_2940_ = !lean_is_exclusive(v_t_2916_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2923_ = v_t_2916_;
v_isShared_2924_ = v_isSharedCheck_2940_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_r_2921_);
lean_inc(v_l_2920_);
lean_inc(v_v_2919_);
lean_inc(v_k_2918_);
lean_inc(v_size_2917_);
lean_dec(v_t_2916_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2940_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
uint8_t v___x_2925_; 
v___x_2925_ = lean_nat_dec_lt(v_k_2915_, v_k_2918_);
if (v___x_2925_ == 0)
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_nat_dec_eq(v_k_2915_, v_k_2918_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2927_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2915_, v_r_2921_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 4, v___x_2927_);
v___x_2929_ = v___x_2923_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_size_2917_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2918_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2919_);
lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_l_2920_);
lean_ctor_set(v_reuseFailAlloc_2930_, 4, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
lean_dec(v_k_2918_);
v___x_2931_ = lean_unsigned_to_nat(1u);
v___x_2932_ = lean_nat_add(v_v_2919_, v___x_2931_);
lean_dec(v_v_2919_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 2, v___x_2932_);
lean_ctor_set(v___x_2923_, 1, v_k_2915_);
v___x_2934_ = v___x_2923_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_size_2917_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_k_2915_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v_l_2920_);
lean_ctor_set(v_reuseFailAlloc_2935_, 4, v_r_2921_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2915_, v_l_2920_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 3, v___x_2936_);
v___x_2938_ = v___x_2923_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_size_2917_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_k_2918_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_v_2919_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v___x_2936_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_r_2921_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
else
{
lean_dec(v_k_2915_);
return v_t_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_2941_, lean_object* v_next_2942_){
_start:
{
lean_object* v___x_2944_; lean_object* v_fst_2946_; lean_object* v_snd_2947_; lean_object* v_value_2949_; lean_object* v_pos_2950_; lean_object* v_remaining_2951_; uint8_t v___x_2952_; 
v___x_2944_ = lean_st_ref_take(v_slot_2941_);
v_value_2949_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_value_2949_);
v_pos_2950_ = lean_ctor_get(v___x_2944_, 1);
lean_inc(v_pos_2950_);
v_remaining_2951_ = lean_ctor_get(v___x_2944_, 2);
lean_inc(v_remaining_2951_);
v___x_2952_ = lean_nat_dec_eq(v_next_2942_, v_pos_2950_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec(v_remaining_2951_);
lean_dec(v_pos_2950_);
lean_dec(v_value_2949_);
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_box(v___x_2952_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v_fst_2946_ = v___x_2955_;
v_snd_2947_ = v___x_2944_;
goto v___jp_2945_;
}
else
{
lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2974_; 
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; lean_object* v_unused_2976_; lean_object* v_unused_2977_; 
v_unused_2975_ = lean_ctor_get(v___x_2944_, 2);
lean_dec(v_unused_2975_);
v_unused_2976_ = lean_ctor_get(v___x_2944_, 1);
lean_dec(v_unused_2976_);
v_unused_2977_ = lean_ctor_get(v___x_2944_, 0);
lean_dec(v_unused_2977_);
v___x_2957_ = v___x_2944_;
v_isShared_2958_ = v_isSharedCheck_2974_;
goto v_resetjp_2956_;
}
else
{
lean_dec(v___x_2944_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2974_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2959_ = lean_unsigned_to_nat(1u);
v___x_2960_ = lean_nat_dec_eq(v_remaining_2951_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2961_ = lean_box(v___x_2960_);
lean_inc(v_value_2949_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v_value_2949_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = lean_nat_sub(v_remaining_2951_, v___x_2959_);
lean_dec(v_remaining_2951_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 2, v___x_2963_);
v___x_2965_ = v___x_2957_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_value_2949_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_pos_2950_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
v_fst_2946_ = v___x_2962_;
v_snd_2947_ = v___x_2965_;
goto v___jp_2945_;
}
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
lean_dec(v_remaining_2951_);
v___x_2967_ = lean_box(v___x_2952_);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v_value_2949_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_unsigned_to_nat(0u);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 2, v___x_2970_);
lean_ctor_set(v___x_2957_, 0, v___x_2969_);
v___x_2972_ = v___x_2957_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_pos_2950_);
lean_ctor_set(v_reuseFailAlloc_2973_, 2, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
v_fst_2946_ = v___x_2968_;
v_snd_2947_ = v___x_2972_;
goto v___jp_2945_;
}
}
}
}
v___jp_2945_:
{
lean_object* v___x_2948_; 
v___x_2948_ = lean_st_ref_set(v_slot_2941_, v_snd_2947_);
return v_fst_2946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_2978_, lean_object* v_next_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_2978_, v_next_2979_);
lean_dec(v_next_2979_);
lean_dec(v_slot_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_2982_){
_start:
{
lean_object* v___x_2984_; lean_object* v_size_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2984_ = lean_st_ref_get(v_a_2982_);
v_size_2985_ = lean_ctor_get(v___x_2984_, 3);
lean_inc(v_size_2985_);
lean_dec(v___x_2984_);
v___x_2986_ = lean_unsigned_to_nat(0u);
v___x_2987_ = lean_nat_dec_eq(v_size_2985_, v___x_2986_);
lean_dec(v_size_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_2988_, lean_object* v___y_2989_){
_start:
{
uint8_t v_res_2990_; lean_object* v_r_2991_; 
v_res_2990_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_2988_);
lean_dec(v_a_2988_);
v_r_2991_ = lean_box(v_res_2990_);
return v_r_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v___x_2995_; lean_object* v_capacity_2996_; lean_object* v_buffer_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2995_ = lean_st_ref_get(v_a_2993_);
v_capacity_2996_ = lean_ctor_get(v___x_2995_, 2);
lean_inc(v_capacity_2996_);
v_buffer_2997_ = lean_ctor_get(v___x_2995_, 4);
lean_inc_ref(v_buffer_2997_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_nat_mod(v_place_2992_, v_capacity_2996_);
lean_dec(v_capacity_2996_);
v___x_2999_ = lean_array_fget(v_buffer_2997_, v___x_2998_);
lean_dec(v___x_2998_);
lean_dec_ref(v_buffer_2997_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_3000_, lean_object* v_a_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3000_, v_a_3001_);
lean_dec(v_a_3001_);
lean_dec(v_place_3000_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = lean_st_ref_get(v_a_3005_);
v___x_3008_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3005_);
if (v___x_3008_ == 0)
{
lean_object* v_capacity_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v_fst_3013_; lean_object* v_snd_3014_; lean_object* v_st_3016_; lean_object* v___y_3017_; 
v_capacity_3009_ = lean_ctor_get(v___x_3007_, 2);
lean_inc(v_capacity_3009_);
v___x_3010_ = lean_nat_mod(v_next_3004_, v_capacity_3009_);
lean_dec(v_capacity_3009_);
v___x_3011_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_3010_, v_a_3005_);
lean_dec(v___x_3010_);
v___x_3012_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_3011_, v_next_3004_);
lean_dec(v___x_3011_);
v_fst_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_fst_3013_);
v_snd_3014_ = lean_ctor_get(v___x_3012_, 1);
lean_inc(v_snd_3014_);
lean_dec_ref(v___x_3012_);
if (lean_obj_tag(v_fst_3013_) == 1)
{
uint8_t v___x_3019_; 
v___x_3019_ = lean_unbox(v_snd_3014_);
if (v___x_3019_ == 0)
{
lean_dec(v_snd_3014_);
v_st_3016_ = v___x_3007_;
v___y_3017_ = v_a_3005_;
goto v___jp_3015_;
}
else
{
lean_object* v___x_3020_; lean_object* v_producers_3021_; lean_object* v_waiters_3022_; lean_object* v_capacity_3023_; lean_object* v_size_3024_; lean_object* v_buffer_3025_; lean_object* v_write_3026_; lean_object* v_read_3027_; lean_object* v_receivers_3028_; lean_object* v_nextId_3029_; uint8_t v_closed_3030_; lean_object* v_pos_3031_; lean_object* v___x_3032_; 
v___x_3020_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_3007_);
v_producers_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc_ref(v_producers_3021_);
v_waiters_3022_ = lean_ctor_get(v___x_3020_, 1);
lean_inc_ref(v_waiters_3022_);
v_capacity_3023_ = lean_ctor_get(v___x_3020_, 2);
lean_inc(v_capacity_3023_);
v_size_3024_ = lean_ctor_get(v___x_3020_, 3);
lean_inc(v_size_3024_);
v_buffer_3025_ = lean_ctor_get(v___x_3020_, 4);
lean_inc_ref(v_buffer_3025_);
v_write_3026_ = lean_ctor_get(v___x_3020_, 5);
lean_inc(v_write_3026_);
v_read_3027_ = lean_ctor_get(v___x_3020_, 6);
lean_inc(v_read_3027_);
v_receivers_3028_ = lean_ctor_get(v___x_3020_, 7);
lean_inc(v_receivers_3028_);
v_nextId_3029_ = lean_ctor_get(v___x_3020_, 8);
lean_inc(v_nextId_3029_);
v_closed_3030_ = lean_ctor_get_uint8(v___x_3020_, sizeof(void*)*10);
v_pos_3031_ = lean_ctor_get(v___x_3020_, 9);
lean_inc(v_pos_3031_);
v___x_3032_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3021_);
if (lean_obj_tag(v___x_3032_) == 1)
{
lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3043_; 
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; lean_object* v_unused_3045_; lean_object* v_unused_3046_; lean_object* v_unused_3047_; lean_object* v_unused_3048_; lean_object* v_unused_3049_; lean_object* v_unused_3050_; lean_object* v_unused_3051_; lean_object* v_unused_3052_; lean_object* v_unused_3053_; 
v_unused_3044_ = lean_ctor_get(v___x_3020_, 9);
lean_dec(v_unused_3044_);
v_unused_3045_ = lean_ctor_get(v___x_3020_, 8);
lean_dec(v_unused_3045_);
v_unused_3046_ = lean_ctor_get(v___x_3020_, 7);
lean_dec(v_unused_3046_);
v_unused_3047_ = lean_ctor_get(v___x_3020_, 6);
lean_dec(v_unused_3047_);
v_unused_3048_ = lean_ctor_get(v___x_3020_, 5);
lean_dec(v_unused_3048_);
v_unused_3049_ = lean_ctor_get(v___x_3020_, 4);
lean_dec(v_unused_3049_);
v_unused_3050_ = lean_ctor_get(v___x_3020_, 3);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v___x_3020_, 2);
lean_dec(v_unused_3051_);
v_unused_3052_ = lean_ctor_get(v___x_3020_, 1);
lean_dec(v_unused_3052_);
v_unused_3053_ = lean_ctor_get(v___x_3020_, 0);
lean_dec(v_unused_3053_);
v___x_3034_ = v___x_3020_;
v_isShared_3035_ = v_isSharedCheck_3043_;
goto v_resetjp_3033_;
}
else
{
lean_dec(v___x_3020_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3043_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v_val_3036_; lean_object* v_fst_3037_; lean_object* v_snd_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v_val_3036_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_val_3036_);
lean_dec_ref(v___x_3032_);
v_fst_3037_ = lean_ctor_get(v_val_3036_, 0);
lean_inc(v_fst_3037_);
v_snd_3038_ = lean_ctor_get(v_val_3036_, 1);
lean_inc(v_snd_3038_);
lean_dec(v_val_3036_);
v___x_3039_ = lean_io_promise_resolve(v_snd_3014_, v_fst_3037_);
lean_dec(v_fst_3037_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v_snd_3038_);
v___x_3041_ = v___x_3034_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_snd_3038_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_waiters_3022_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_capacity_3023_);
lean_ctor_set(v_reuseFailAlloc_3042_, 3, v_size_3024_);
lean_ctor_set(v_reuseFailAlloc_3042_, 4, v_buffer_3025_);
lean_ctor_set(v_reuseFailAlloc_3042_, 5, v_write_3026_);
lean_ctor_set(v_reuseFailAlloc_3042_, 6, v_read_3027_);
lean_ctor_set(v_reuseFailAlloc_3042_, 7, v_receivers_3028_);
lean_ctor_set(v_reuseFailAlloc_3042_, 8, v_nextId_3029_);
lean_ctor_set(v_reuseFailAlloc_3042_, 9, v_pos_3031_);
lean_ctor_set_uint8(v_reuseFailAlloc_3042_, sizeof(void*)*10, v_closed_3030_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
v_st_3016_ = v___x_3041_;
v___y_3017_ = v_a_3005_;
goto v___jp_3015_;
}
}
}
else
{
lean_dec(v___x_3032_);
lean_dec(v_pos_3031_);
lean_dec(v_nextId_3029_);
lean_dec(v_receivers_3028_);
lean_dec(v_read_3027_);
lean_dec(v_write_3026_);
lean_dec_ref(v_buffer_3025_);
lean_dec(v_size_3024_);
lean_dec(v_capacity_3023_);
lean_dec_ref(v_waiters_3022_);
lean_dec(v_snd_3014_);
v_st_3016_ = v___x_3020_;
v___y_3017_ = v_a_3005_;
goto v___jp_3015_;
}
}
}
else
{
lean_object* v___x_3054_; 
lean_dec(v_snd_3014_);
lean_dec(v_fst_3013_);
lean_dec(v___x_3007_);
v___x_3054_ = lean_box(0);
return v___x_3054_;
}
v___jp_3015_:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_st_ref_set(v___y_3017_, v_st_3016_);
return v_fst_3013_;
}
}
else
{
lean_object* v___x_3055_; 
lean_dec(v___x_3007_);
v___x_3055_ = lean_box(0);
return v___x_3055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_3056_, lean_object* v_a_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3056_, v_a_3057_);
lean_dec(v_a_3057_);
lean_dec(v_next_3056_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v___x_3063_; lean_object* v_receivers_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_st_ref_get(v_a_3061_);
v_receivers_3064_ = lean_ctor_get(v___x_3063_, 7);
lean_inc(v_receivers_3064_);
lean_dec(v___x_3063_);
v___x_3065_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3064_, v_receiverId_3060_);
if (lean_obj_tag(v___x_3065_) == 1)
{
lean_object* v_val_3066_; lean_object* v___x_3067_; 
v_val_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_val_3066_);
lean_dec_ref(v___x_3065_);
v___x_3067_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_3066_, v_a_3061_);
lean_dec(v_val_3066_);
if (lean_obj_tag(v___x_3067_) == 1)
{
lean_object* v___x_3068_; lean_object* v_producers_3069_; lean_object* v_waiters_3070_; lean_object* v_capacity_3071_; lean_object* v_size_3072_; lean_object* v_buffer_3073_; lean_object* v_write_3074_; lean_object* v_read_3075_; lean_object* v_nextId_3076_; uint8_t v_closed_3077_; lean_object* v_pos_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3087_; 
v___x_3068_ = lean_st_ref_take(v_a_3061_);
v_producers_3069_ = lean_ctor_get(v___x_3068_, 0);
v_waiters_3070_ = lean_ctor_get(v___x_3068_, 1);
v_capacity_3071_ = lean_ctor_get(v___x_3068_, 2);
v_size_3072_ = lean_ctor_get(v___x_3068_, 3);
v_buffer_3073_ = lean_ctor_get(v___x_3068_, 4);
v_write_3074_ = lean_ctor_get(v___x_3068_, 5);
v_read_3075_ = lean_ctor_get(v___x_3068_, 6);
v_nextId_3076_ = lean_ctor_get(v___x_3068_, 8);
v_closed_3077_ = lean_ctor_get_uint8(v___x_3068_, sizeof(void*)*10);
v_pos_3078_ = lean_ctor_get(v___x_3068_, 9);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3068_, 7);
lean_dec(v_unused_3088_);
v___x_3080_ = v___x_3068_;
v_isShared_3081_ = v_isSharedCheck_3087_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_pos_3078_);
lean_inc(v_nextId_3076_);
lean_inc(v_read_3075_);
lean_inc(v_write_3074_);
lean_inc(v_buffer_3073_);
lean_inc(v_size_3072_);
lean_inc(v_capacity_3071_);
lean_inc(v_waiters_3070_);
lean_inc(v_producers_3069_);
lean_dec(v___x_3068_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3087_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3060_, v_receivers_3064_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 7, v___x_3082_);
v___x_3084_ = v___x_3080_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_producers_3069_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_waiters_3070_);
lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_capacity_3071_);
lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_size_3072_);
lean_ctor_set(v_reuseFailAlloc_3086_, 4, v_buffer_3073_);
lean_ctor_set(v_reuseFailAlloc_3086_, 5, v_write_3074_);
lean_ctor_set(v_reuseFailAlloc_3086_, 6, v_read_3075_);
lean_ctor_set(v_reuseFailAlloc_3086_, 7, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3086_, 8, v_nextId_3076_);
lean_ctor_set(v_reuseFailAlloc_3086_, 9, v_pos_3078_);
lean_ctor_set_uint8(v_reuseFailAlloc_3086_, sizeof(void*)*10, v_closed_3077_);
v___x_3084_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_st_ref_set(v_a_3061_, v___x_3084_);
return v___x_3067_;
}
}
}
else
{
lean_object* v___x_3089_; 
lean_dec(v___x_3067_);
lean_dec(v_receivers_3064_);
lean_dec(v_receiverId_3060_);
v___x_3089_ = lean_box(0);
return v___x_3089_;
}
}
else
{
lean_object* v___x_3090_; 
lean_dec(v___x_3065_);
lean_dec(v_receivers_3064_);
lean_dec(v_receiverId_3060_);
v___x_3090_ = lean_box(0);
return v___x_3090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3091_, lean_object* v_a_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3091_, v_a_3092_);
lean_dec(v_a_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3095_, v___y_3096_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3099_, v___y_3100_);
lean_dec(v___y_3100_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3103_){
_start:
{
lean_object* v_state_3105_; lean_object* v_id_3106_; lean_object* v___f_3107_; lean_object* v___x_3108_; 
v_state_3105_ = lean_ctor_get(v_ch_3103_, 0);
lean_inc_ref(v_state_3105_);
v_id_3106_ = lean_ctor_get(v_ch_3103_, 1);
lean_inc(v_id_3106_);
lean_dec_ref(v_ch_3103_);
v___f_3107_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3107_, 0, v_id_3106_);
v___x_3108_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3105_, v___f_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3109_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3112_, lean_object* v_ch_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3116_, lean_object* v_ch_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3116_, v_ch_3117_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3120_, lean_object* v_receiverId_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3121_, v_a_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3125_, lean_object* v_receiverId_3126_, lean_object* v_a_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3125_, v_receiverId_3126_, v_a_3127_);
lean_dec(v_a_3127_);
return v_res_3129_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3130_, lean_object* v_a_3131_){
_start:
{
uint8_t v___x_3133_; 
v___x_3133_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3134_, lean_object* v_a_3135_, lean_object* v___y_3136_){
_start:
{
uint8_t v_res_3137_; lean_object* v_r_3138_; 
v_res_3137_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3134_, v_a_3135_);
lean_dec(v_a_3135_);
v_r_3138_ = lean_box(v_res_3137_);
return v_r_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3139_, lean_object* v_place_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3140_, v_a_3141_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3144_, lean_object* v_place_3145_, lean_object* v_a_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3144_, v_place_3145_, v_a_3146_);
lean_dec(v_a_3146_);
lean_dec(v_place_3145_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3149_, lean_object* v_slot_3150_, lean_object* v_next_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3154_; 
v___x_3154_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3150_, v_next_3151_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3155_, lean_object* v_slot_3156_, lean_object* v_next_3157_, lean_object* v_a_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3155_, v_slot_3156_, v_next_3157_, v_a_3158_);
lean_dec(v_a_3158_);
lean_dec(v_next_3157_);
lean_dec(v_slot_3156_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3161_, lean_object* v_next_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3162_, v_a_3163_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3166_, lean_object* v_next_3167_, lean_object* v_a_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3166_, v_next_3167_, v_a_3168_);
lean_dec(v_a_3168_);
lean_dec(v_next_3167_);
return v_res_3170_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3171_, lean_object* v_t_3172_){
_start:
{
if (lean_obj_tag(v_t_3172_) == 0)
{
lean_object* v_k_3173_; lean_object* v_l_3174_; lean_object* v_r_3175_; uint8_t v___x_3176_; 
v_k_3173_ = lean_ctor_get(v_t_3172_, 1);
v_l_3174_ = lean_ctor_get(v_t_3172_, 3);
v_r_3175_ = lean_ctor_get(v_t_3172_, 4);
v___x_3176_ = lean_nat_dec_lt(v_k_3171_, v_k_3173_);
if (v___x_3176_ == 0)
{
uint8_t v___x_3177_; 
v___x_3177_ = lean_nat_dec_eq(v_k_3171_, v_k_3173_);
if (v___x_3177_ == 0)
{
v_t_3172_ = v_r_3175_;
goto _start;
}
else
{
return v___x_3177_;
}
}
else
{
v_t_3172_ = v_l_3174_;
goto _start;
}
}
else
{
uint8_t v___x_3180_; 
v___x_3180_ = 0;
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3181_, lean_object* v_t_3182_){
_start:
{
uint8_t v_res_3183_; lean_object* v_r_3184_; 
v_res_3183_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3181_, v_t_3182_);
lean_dec(v_t_3182_);
lean_dec(v_k_3181_);
v_r_3184_ = lean_box(v_res_3183_);
return v_r_3184_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_box(0);
v___x_3186_ = lean_task_pure(v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3187_, lean_object* v___f_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; lean_object* v_receivers_3192_; uint8_t v___x_3193_; 
v___x_3191_ = lean_st_ref_get(v___y_3189_);
v_receivers_3192_ = lean_ctor_get(v___x_3191_, 7);
lean_inc(v_receivers_3192_);
lean_dec(v___x_3191_);
v___x_3193_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3187_, v_receivers_3192_);
lean_dec(v_receivers_3192_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; 
lean_dec_ref(v___f_3188_);
lean_dec(v_id_3187_);
v___x_3194_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3194_;
}
else
{
lean_object* v___x_3195_; 
v___x_3195_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3187_, v___y_3189_);
if (lean_obj_tag(v___x_3195_) == 1)
{
lean_object* v___x_3196_; 
lean_dec_ref(v___f_3188_);
v___x_3196_ = lean_task_pure(v___x_3195_);
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; uint8_t v_closed_3198_; 
lean_dec(v___x_3195_);
v___x_3197_ = lean_st_ref_get(v___y_3189_);
v_closed_3198_ = lean_ctor_get_uint8(v___x_3197_, sizeof(void*)*10);
lean_dec(v___x_3197_);
if (v_closed_3198_ == 0)
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v_producers_3201_; lean_object* v_waiters_3202_; lean_object* v_capacity_3203_; lean_object* v_size_3204_; lean_object* v_buffer_3205_; lean_object* v_write_3206_; lean_object* v_read_3207_; lean_object* v_receivers_3208_; lean_object* v_nextId_3209_; uint8_t v_closed_3210_; lean_object* v_pos_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3225_; 
v___x_3199_ = lean_io_promise_new();
v___x_3200_ = lean_st_ref_take(v___y_3189_);
v_producers_3201_ = lean_ctor_get(v___x_3200_, 0);
v_waiters_3202_ = lean_ctor_get(v___x_3200_, 1);
v_capacity_3203_ = lean_ctor_get(v___x_3200_, 2);
v_size_3204_ = lean_ctor_get(v___x_3200_, 3);
v_buffer_3205_ = lean_ctor_get(v___x_3200_, 4);
v_write_3206_ = lean_ctor_get(v___x_3200_, 5);
v_read_3207_ = lean_ctor_get(v___x_3200_, 6);
v_receivers_3208_ = lean_ctor_get(v___x_3200_, 7);
v_nextId_3209_ = lean_ctor_get(v___x_3200_, 8);
v_closed_3210_ = lean_ctor_get_uint8(v___x_3200_, sizeof(void*)*10);
v_pos_3211_ = lean_ctor_get(v___x_3200_, 9);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3213_ = v___x_3200_;
v_isShared_3214_ = v_isSharedCheck_3225_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_pos_3211_);
lean_inc(v_nextId_3209_);
lean_inc(v_receivers_3208_);
lean_inc(v_read_3207_);
lean_inc(v_write_3206_);
lean_inc(v_buffer_3205_);
lean_inc(v_size_3204_);
lean_inc(v_capacity_3203_);
lean_inc(v_waiters_3202_);
lean_inc(v_producers_3201_);
lean_dec(v___x_3200_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3225_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3215_ = lean_box(0);
lean_inc(v___x_3199_);
v___x_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3199_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = l_Std_Queue_enqueue___redArg(v___x_3216_, v_waiters_3202_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 1, v___x_3217_);
v___x_3219_ = v___x_3213_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_producers_3201_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_capacity_3203_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_size_3204_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_buffer_3205_);
lean_ctor_set(v_reuseFailAlloc_3224_, 5, v_write_3206_);
lean_ctor_set(v_reuseFailAlloc_3224_, 6, v_read_3207_);
lean_ctor_set(v_reuseFailAlloc_3224_, 7, v_receivers_3208_);
lean_ctor_set(v_reuseFailAlloc_3224_, 8, v_nextId_3209_);
lean_ctor_set(v_reuseFailAlloc_3224_, 9, v_pos_3211_);
lean_ctor_set_uint8(v_reuseFailAlloc_3224_, sizeof(void*)*10, v_closed_3210_);
v___x_3219_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3220_ = lean_st_ref_set(v___y_3189_, v___x_3219_);
v___x_3221_ = lean_io_promise_result_opt(v___x_3199_);
lean_dec(v___x_3199_);
v___x_3222_ = lean_unsigned_to_nat(0u);
v___x_3223_ = lean_io_bind_task(v___x_3221_, v___f_3188_, v___x_3222_, v_closed_3198_);
return v___x_3223_;
}
}
}
else
{
lean_object* v___x_3226_; 
lean_dec_ref(v___f_3188_);
v___x_3226_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3227_, lean_object* v___f_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3227_, v___f_3228_, v___y_3229_);
lean_dec(v___y_3229_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3232_, lean_object* v_res_3233_){
_start:
{
if (lean_obj_tag(v_res_3233_) == 0)
{
lean_dec_ref(v_ch_3232_);
goto v___jp_3235_;
}
else
{
lean_object* v_val_3237_; uint8_t v___x_3238_; 
v_val_3237_ = lean_ctor_get(v_res_3233_, 0);
v___x_3238_ = lean_unbox(v_val_3237_);
if (v___x_3238_ == 0)
{
lean_dec_ref(v_ch_3232_);
goto v___jp_3235_;
}
else
{
lean_object* v___x_3239_; 
v___x_3239_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3232_);
return v___x_3239_;
}
}
v___jp_3235_:
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3240_, lean_object* v_res_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3240_, v_res_3241_);
lean_dec(v_res_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3244_){
_start:
{
lean_object* v_state_3246_; lean_object* v_id_3247_; lean_object* v___f_3248_; lean_object* v___f_3249_; lean_object* v___x_3250_; 
v_state_3246_ = lean_ctor_get(v_ch_3244_, 0);
lean_inc_ref(v_state_3246_);
v_id_3247_ = lean_ctor_get(v_ch_3244_, 1);
lean_inc(v_id_3247_);
v___f_3248_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3248_, 0, v_ch_3244_);
v___f_3249_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3249_, 0, v_id_3247_);
lean_closure_set(v___f_3249_, 1, v___f_3248_);
v___x_3250_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3246_, v___f_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3251_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3254_, lean_object* v_ch_3255_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3258_, lean_object* v_ch_3259_, lean_object* v_a_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3258_, v_ch_3259_);
return v_res_3261_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3262_, lean_object* v_k_3263_, lean_object* v_t_3264_){
_start:
{
uint8_t v___x_3265_; 
v___x_3265_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3263_, v_t_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3266_, lean_object* v_k_3267_, lean_object* v_t_3268_){
_start:
{
uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_res_3269_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3266_, v_k_3267_, v_t_3268_);
lean_dec(v_t_3268_);
lean_dec(v_k_3267_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_task_pure(v___x_3271_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3273_, lean_object* v_ch_3274_, lean_object* v_prio_3275_, lean_object* v_x_3276_){
_start:
{
if (lean_obj_tag(v_x_3276_) == 0)
{
lean_object* v___x_3278_; 
lean_dec(v_prio_3275_);
lean_dec_ref(v_ch_3274_);
lean_dec_ref(v_f_3273_);
v___x_3278_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3278_;
}
else
{
lean_object* v_val_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_val_3279_ = lean_ctor_get(v_x_3276_, 0);
lean_inc(v_val_3279_);
lean_dec_ref(v_x_3276_);
lean_inc_ref(v_f_3273_);
v___x_3280_ = lean_apply_2(v_f_3273_, v_val_3279_, lean_box(0));
v___x_3281_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3273_, v_ch_3274_, v_prio_3275_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3282_, lean_object* v_ch_3283_, lean_object* v_prio_3284_, lean_object* v_x_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3282_, v_ch_3283_, v_prio_3284_, v_x_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3288_, lean_object* v_ch_3289_, lean_object* v_prio_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v___f_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; 
lean_inc_ref(v_ch_3289_);
v___x_3292_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3289_);
lean_inc(v_prio_3290_);
v___f_3293_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3293_, 0, v_f_3288_);
lean_closure_set(v___f_3293_, 1, v_ch_3289_);
lean_closure_set(v___f_3293_, 2, v_prio_3290_);
v___x_3294_ = 0;
v___x_3295_ = lean_io_bind_task(v___x_3292_, v___f_3293_, v_prio_3290_, v___x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3296_, lean_object* v_ch_3297_, lean_object* v_prio_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3296_, v_ch_3297_, v_prio_3298_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3301_, lean_object* v_f_3302_, lean_object* v_ch_3303_, lean_object* v_prio_3304_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3302_, v_ch_3303_, v_prio_3304_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3307_, lean_object* v_f_3308_, lean_object* v_ch_3309_, lean_object* v_prio_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3307_, v_f_3308_, v_ch_3309_, v_prio_3310_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3313_, lean_object* v_val_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_pos_3316_; lean_object* v_toPure_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_pos_3316_ = lean_ctor_get(v_a_3315_, 1);
v_toPure_3317_ = lean_ctor_get(v_toApplicative_3313_, 1);
lean_inc(v_toPure_3317_);
lean_dec_ref(v_toApplicative_3313_);
v___x_3318_ = lean_nat_dec_eq(v_pos_3316_, v_val_3314_);
v___x_3319_ = lean_box(v___x_3318_);
v___x_3320_ = lean_apply_2(v_toPure_3317_, lean_box(0), v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3321_, lean_object* v_val_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3321_, v_val_3322_, v_a_3323_);
lean_dec_ref(v_a_3323_);
lean_dec(v_val_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3325_, lean_object* v_toBind_3326_, lean_object* v___f_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3329_, 0, lean_box(0));
lean_closure_set(v___x_3329_, 1, lean_box(0));
lean_closure_set(v___x_3329_, 2, v_a_3328_);
v___x_3330_ = lean_apply_2(v_inst_3325_, lean_box(0), v___x_3329_);
v___x_3331_ = lean_apply_4(v_toBind_3326_, lean_box(0), lean_box(0), v___x_3330_, v___f_3327_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3332_, lean_object* v_receiverId_3333_, lean_object* v_toApplicative_3334_, lean_object* v_inst_3335_, lean_object* v_toBind_3336_, lean_object* v_inst_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
uint8_t v_closed_3340_; 
v_closed_3340_ = lean_ctor_get_uint8(v_a_3339_, sizeof(void*)*10);
if (v_closed_3340_ == 0)
{
lean_object* v_capacity_3341_; lean_object* v_size_3342_; lean_object* v_receivers_3343_; lean_object* v___x_3344_; 
v_capacity_3341_ = lean_ctor_get(v_a_3339_, 2);
lean_inc(v_capacity_3341_);
v_size_3342_ = lean_ctor_get(v_a_3339_, 3);
lean_inc(v_size_3342_);
v_receivers_3343_ = lean_ctor_get(v_a_3339_, 7);
lean_inc(v_receivers_3343_);
lean_dec_ref(v_a_3339_);
v___x_3344_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3332_, v_receivers_3343_, v_receiverId_3333_);
if (lean_obj_tag(v___x_3344_) == 1)
{
lean_object* v_val_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_val_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_val_3345_);
lean_dec_ref(v___x_3344_);
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3347_ = lean_nat_dec_eq(v_size_3342_, v___x_3346_);
lean_dec(v_size_3342_);
if (v___x_3347_ == 0)
{
lean_object* v___f_3348_; lean_object* v___f_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_inc(v_val_3345_);
v___f_3348_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3348_, 0, v_toApplicative_3334_);
lean_closure_set(v___f_3348_, 1, v_val_3345_);
lean_inc(v_toBind_3336_);
lean_inc(v_inst_3335_);
v___f_3349_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3349_, 0, v_inst_3335_);
lean_closure_set(v___f_3349_, 1, v_toBind_3336_);
lean_closure_set(v___f_3349_, 2, v___f_3348_);
v___x_3350_ = lean_nat_mod(v_val_3345_, v_capacity_3341_);
lean_dec(v_capacity_3341_);
lean_dec(v_val_3345_);
v___x_3351_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3337_, v_inst_3335_, v___x_3350_, v_a_3338_);
v___x_3352_ = lean_apply_4(v_toBind_3336_, lean_box(0), lean_box(0), v___x_3351_, v___f_3349_);
return v___x_3352_;
}
else
{
lean_object* v_toPure_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec(v_val_3345_);
lean_dec(v_capacity_3341_);
lean_dec_ref(v_inst_3337_);
lean_dec(v_toBind_3336_);
lean_dec(v_inst_3335_);
v_toPure_3353_ = lean_ctor_get(v_toApplicative_3334_, 1);
lean_inc(v_toPure_3353_);
lean_dec_ref(v_toApplicative_3334_);
v___x_3354_ = lean_box(v_closed_3340_);
v___x_3355_ = lean_apply_2(v_toPure_3353_, lean_box(0), v___x_3354_);
return v___x_3355_;
}
}
else
{
lean_object* v_toPure_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec(v___x_3344_);
lean_dec(v_size_3342_);
lean_dec(v_capacity_3341_);
lean_dec_ref(v_inst_3337_);
lean_dec(v_toBind_3336_);
lean_dec(v_inst_3335_);
v_toPure_3356_ = lean_ctor_get(v_toApplicative_3334_, 1);
lean_inc(v_toPure_3356_);
lean_dec_ref(v_toApplicative_3334_);
v___x_3357_ = lean_box(v_closed_3340_);
v___x_3358_ = lean_apply_2(v_toPure_3356_, lean_box(0), v___x_3357_);
return v___x_3358_;
}
}
else
{
lean_object* v_toPure_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec_ref(v_a_3339_);
lean_dec_ref(v_inst_3337_);
lean_dec(v_toBind_3336_);
lean_dec(v_inst_3335_);
lean_dec(v_receiverId_3333_);
lean_dec_ref(v___f_3332_);
v_toPure_3359_ = lean_ctor_get(v_toApplicative_3334_, 1);
lean_inc(v_toPure_3359_);
lean_dec_ref(v_toApplicative_3334_);
v___x_3360_ = lean_box(v_closed_3340_);
v___x_3361_ = lean_apply_2(v_toPure_3359_, lean_box(0), v___x_3360_);
return v___x_3361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object* v___f_3362_, lean_object* v_receiverId_3363_, lean_object* v_toApplicative_3364_, lean_object* v_inst_3365_, lean_object* v_toBind_3366_, lean_object* v_inst_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(v___f_3362_, v_receiverId_3363_, v_toApplicative_3364_, v_inst_3365_, v_toBind_3366_, v_inst_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3371_, lean_object* v_inst_3372_, lean_object* v_receiverId_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v_toApplicative_3375_; lean_object* v_toBind_3376_; lean_object* v___f_3377_; lean_object* v___f_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_toApplicative_3375_ = lean_ctor_get(v_inst_3371_, 0);
lean_inc_ref(v_toApplicative_3375_);
v_toBind_3376_ = lean_ctor_get(v_inst_3371_, 1);
lean_inc_n(v_toBind_3376_, 2);
v___f_3377_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3374_, 2);
lean_inc(v_inst_3372_);
v___f_3378_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3378_, 0, v___f_3377_);
lean_closure_set(v___f_3378_, 1, v_receiverId_3373_);
lean_closure_set(v___f_3378_, 2, v_toApplicative_3375_);
lean_closure_set(v___f_3378_, 3, v_inst_3372_);
lean_closure_set(v___f_3378_, 4, v_toBind_3376_);
lean_closure_set(v___f_3378_, 5, v_inst_3371_);
lean_closure_set(v___f_3378_, 6, v_a_3374_);
v___x_3379_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3379_, 0, lean_box(0));
lean_closure_set(v___x_3379_, 1, lean_box(0));
lean_closure_set(v___x_3379_, 2, v_a_3374_);
v___x_3380_ = lean_apply_2(v_inst_3372_, lean_box(0), v___x_3379_);
v___x_3381_ = lean_apply_4(v_toBind_3376_, lean_box(0), lean_box(0), v___x_3380_, v___f_3378_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object* v_inst_3382_, lean_object* v_inst_3383_, lean_object* v_receiverId_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(v_inst_3382_, v_inst_3383_, v_receiverId_3384_, v_a_3385_);
lean_dec(v_a_3385_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3387_, lean_object* v_00_u03b1_3388_, lean_object* v_inst_3389_, lean_object* v_inst_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_receiverId_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v_toApplicative_3395_; lean_object* v_toBind_3396_; lean_object* v___f_3397_; lean_object* v___f_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v_toApplicative_3395_ = lean_ctor_get(v_inst_3389_, 0);
lean_inc_ref(v_toApplicative_3395_);
v_toBind_3396_ = lean_ctor_get(v_inst_3389_, 1);
lean_inc_n(v_toBind_3396_, 2);
v___f_3397_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3394_, 2);
lean_inc(v_inst_3390_);
v___f_3398_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3398_, 0, v___f_3397_);
lean_closure_set(v___f_3398_, 1, v_receiverId_3393_);
lean_closure_set(v___f_3398_, 2, v_toApplicative_3395_);
lean_closure_set(v___f_3398_, 3, v_inst_3390_);
lean_closure_set(v___f_3398_, 4, v_toBind_3396_);
lean_closure_set(v___f_3398_, 5, v_inst_3389_);
lean_closure_set(v___f_3398_, 6, v_a_3394_);
v___x_3399_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3399_, 0, lean_box(0));
lean_closure_set(v___x_3399_, 1, lean_box(0));
lean_closure_set(v___x_3399_, 2, v_a_3394_);
v___x_3400_ = lean_apply_2(v_inst_3390_, lean_box(0), v___x_3399_);
v___x_3401_ = lean_apply_4(v_toBind_3396_, lean_box(0), lean_box(0), v___x_3400_, v___f_3398_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3402_, lean_object* v_00_u03b1_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_receiverId_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3402_, v_00_u03b1_3403_, v_inst_3404_, v_inst_3405_, v_inst_3406_, v_inst_3407_, v_receiverId_3408_, v_a_3409_);
lean_dec(v_a_3409_);
lean_dec(v_inst_3407_);
lean_dec(v_inst_3406_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3413_, lean_object* v_lose_3414_){
_start:
{
lean_object* v_finished_3416_; lean_object* v_promise_3417_; lean_object* v___x_3418_; uint8_t v___y_3420_; uint8_t v___x_3428_; 
v_finished_3416_ = lean_ctor_get(v_w_3413_, 0);
v_promise_3417_ = lean_ctor_get(v_w_3413_, 1);
v___x_3418_ = lean_st_ref_take(v_finished_3416_);
v___x_3428_ = lean_unbox(v___x_3418_);
lean_dec(v___x_3418_);
if (v___x_3428_ == 0)
{
uint8_t v___x_3429_; 
v___x_3429_ = 1;
v___y_3420_ = v___x_3429_;
goto v___jp_3419_;
}
else
{
uint8_t v___x_3430_; 
v___x_3430_ = 0;
v___y_3420_ = v___x_3430_;
goto v___jp_3419_;
}
v___jp_3419_:
{
uint8_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = 1;
v___x_3422_ = lean_box(v___x_3421_);
v___x_3423_ = lean_st_ref_set(v_finished_3416_, v___x_3422_);
if (v___y_3420_ == 0)
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_apply_1(v_lose_3414_, lean_box(0));
return v___x_3424_;
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_dec_ref(v_lose_3414_);
v___x_3425_ = ((lean_object*)(l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3426_ = lean_io_promise_resolve(v___x_3425_, v_promise_3417_);
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
return v___x_3427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3431_, lean_object* v_lose_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3431_, v_lose_3432_);
lean_dec_ref(v_w_3431_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3435_, lean_object* v_w_3436_, lean_object* v_lose_3437_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3436_, v_lose_3437_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3440_, lean_object* v_w_3441_, lean_object* v_lose_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3440_, v_w_3441_, v_lose_3442_);
lean_dec_ref(v_w_3441_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v_receivers_3449_; lean_object* v___x_3450_; 
v___x_3448_ = lean_st_ref_get(v_a_3446_);
v_receivers_3449_ = lean_ctor_get(v___x_3448_, 7);
lean_inc(v_receivers_3449_);
lean_dec(v___x_3448_);
v___x_3450_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3449_, v_receiverId_3445_);
if (lean_obj_tag(v___x_3450_) == 1)
{
lean_object* v_val_3451_; lean_object* v___x_3452_; 
v_val_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_val_3451_);
lean_dec_ref(v___x_3450_);
v___x_3452_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3451_, v_a_3446_);
lean_dec(v_val_3451_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3485_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3485_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3485_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
if (lean_obj_tag(v_a_3453_) == 1)
{
lean_object* v___x_3457_; lean_object* v_producers_3458_; lean_object* v_waiters_3459_; lean_object* v_capacity_3460_; lean_object* v_size_3461_; lean_object* v_buffer_3462_; lean_object* v_write_3463_; lean_object* v_read_3464_; lean_object* v_nextId_3465_; uint8_t v_closed_3466_; lean_object* v_pos_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3479_; 
v___x_3457_ = lean_st_ref_take(v_a_3446_);
v_producers_3458_ = lean_ctor_get(v___x_3457_, 0);
v_waiters_3459_ = lean_ctor_get(v___x_3457_, 1);
v_capacity_3460_ = lean_ctor_get(v___x_3457_, 2);
v_size_3461_ = lean_ctor_get(v___x_3457_, 3);
v_buffer_3462_ = lean_ctor_get(v___x_3457_, 4);
v_write_3463_ = lean_ctor_get(v___x_3457_, 5);
v_read_3464_ = lean_ctor_get(v___x_3457_, 6);
v_nextId_3465_ = lean_ctor_get(v___x_3457_, 8);
v_closed_3466_ = lean_ctor_get_uint8(v___x_3457_, sizeof(void*)*10);
v_pos_3467_ = lean_ctor_get(v___x_3457_, 9);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v___x_3457_, 7);
lean_dec(v_unused_3480_);
v___x_3469_ = v___x_3457_;
v_isShared_3470_ = v_isSharedCheck_3479_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_pos_3467_);
lean_inc(v_nextId_3465_);
lean_inc(v_read_3464_);
lean_inc(v_write_3463_);
lean_inc(v_buffer_3462_);
lean_inc(v_size_3461_);
lean_inc(v_capacity_3460_);
lean_inc(v_waiters_3459_);
lean_inc(v_producers_3458_);
lean_dec(v___x_3457_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3479_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3445_, v_receivers_3449_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 7, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_producers_3458_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_waiters_3459_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_capacity_3460_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_size_3461_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_buffer_3462_);
lean_ctor_set(v_reuseFailAlloc_3478_, 5, v_write_3463_);
lean_ctor_set(v_reuseFailAlloc_3478_, 6, v_read_3464_);
lean_ctor_set(v_reuseFailAlloc_3478_, 7, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3478_, 8, v_nextId_3465_);
lean_ctor_set(v_reuseFailAlloc_3478_, 9, v_pos_3467_);
lean_ctor_set_uint8(v_reuseFailAlloc_3478_, sizeof(void*)*10, v_closed_3466_);
v___x_3473_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3474_ = lean_st_ref_set(v_a_3446_, v___x_3473_);
if (v_isShared_3456_ == 0)
{
v___x_3476_ = v___x_3455_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3453_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3483_; 
lean_dec(v_a_3453_);
lean_dec(v_receivers_3449_);
lean_dec(v_receiverId_3445_);
v___x_3481_ = lean_box(0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3481_);
v___x_3483_ = v___x_3455_;
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
else
{
lean_dec(v_receivers_3449_);
lean_dec(v_receiverId_3445_);
return v___x_3452_;
}
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v___x_3450_);
lean_dec(v_receivers_3449_);
lean_dec(v_receiverId_3445_);
v___x_3486_ = lean_box(0);
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3488_, lean_object* v_a_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3488_, v_a_3489_);
lean_dec(v_a_3489_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3492_, lean_object* v_w_3493_, lean_object* v_lose_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_finished_3497_; lean_object* v_promise_3498_; lean_object* v___x_3499_; uint8_t v___y_3501_; uint8_t v___x_3525_; 
v_finished_3497_ = lean_ctor_get(v_w_3493_, 0);
v_promise_3498_ = lean_ctor_get(v_w_3493_, 1);
v___x_3499_ = lean_st_ref_take(v_finished_3497_);
v___x_3525_ = lean_unbox(v___x_3499_);
lean_dec(v___x_3499_);
if (v___x_3525_ == 0)
{
uint8_t v___x_3526_; 
v___x_3526_ = 1;
v___y_3501_ = v___x_3526_;
goto v___jp_3500_;
}
else
{
uint8_t v___x_3527_; 
v___x_3527_ = 0;
v___y_3501_ = v___x_3527_;
goto v___jp_3500_;
}
v___jp_3500_:
{
uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = 1;
v___x_3503_ = lean_box(v___x_3502_);
v___x_3504_ = lean_st_ref_set(v_finished_3497_, v___x_3503_);
if (v___y_3501_ == 0)
{
lean_object* v___x_3505_; 
lean_dec(v___x_3492_);
lean_inc(v___y_3495_);
v___x_3505_ = lean_apply_2(v_lose_3494_, v___y_3495_, lean_box(0));
return v___x_3505_;
}
else
{
lean_object* v___x_3506_; 
lean_dec_ref(v_lose_3494_);
v___x_3506_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3492_, v___y_3495_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3516_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3516_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3516_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3511_, 0, v_a_3507_);
v___x_3512_ = lean_io_promise_resolve(v___x_3511_, v_promise_3498_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3512_);
v___x_3514_ = v___x_3509_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
v_a_3517_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3506_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3506_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3528_, lean_object* v_w_3529_, lean_object* v_lose_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3528_, v_w_3529_, v_lose_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v_w_3529_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3534_, lean_object* v___x_3535_, lean_object* v_w_3536_, lean_object* v_lose_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3535_, v_w_3536_, v_lose_3537_, v___y_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3541_, lean_object* v___x_3542_, lean_object* v_w_3543_, lean_object* v_lose_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3541_, v___x_3542_, v_w_3543_, v_lose_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v_w_3543_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3548_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3554_, lean_object* v___f_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v___x_3558_; uint8_t v_closed_3559_; 
v___x_3558_ = lean_st_ref_get(v___y_3556_);
v_closed_3559_ = lean_ctor_get_uint8(v___x_3558_, sizeof(void*)*10);
if (v_closed_3559_ == 0)
{
lean_object* v_capacity_3560_; lean_object* v_size_3561_; lean_object* v_receivers_3562_; lean_object* v___x_3563_; 
v_capacity_3560_ = lean_ctor_get(v___x_3558_, 2);
lean_inc(v_capacity_3560_);
v_size_3561_ = lean_ctor_get(v___x_3558_, 3);
lean_inc(v_size_3561_);
v_receivers_3562_ = lean_ctor_get(v___x_3558_, 7);
lean_inc(v_receivers_3562_);
lean_dec(v___x_3558_);
v___x_3563_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3562_, v_id_3554_);
lean_dec(v_receivers_3562_);
if (lean_obj_tag(v___x_3563_) == 1)
{
lean_object* v_val_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v_val_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_val_3564_);
lean_dec_ref(v___x_3563_);
v___x_3565_ = lean_unsigned_to_nat(0u);
v___x_3566_ = lean_nat_dec_eq(v_size_3561_, v___x_3565_);
lean_dec(v_size_3561_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = lean_nat_mod(v_val_3564_, v_capacity_3560_);
lean_dec(v_capacity_3560_);
v___x_3568_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3567_, v___y_3556_);
lean_dec(v___x_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; lean_object* v_pos_3571_; uint8_t v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref(v___x_3568_);
v___x_3570_ = lean_st_ref_get(v_a_3569_);
lean_dec(v_a_3569_);
v_pos_3571_ = lean_ctor_get(v___x_3570_, 1);
lean_inc(v_pos_3571_);
lean_dec(v___x_3570_);
v___x_3572_ = lean_nat_dec_eq(v_pos_3571_, v_val_3564_);
lean_dec(v_val_3564_);
lean_dec(v_pos_3571_);
v___x_3573_ = lean_box(v___x_3572_);
lean_inc(v___y_3556_);
v___x_3574_ = lean_apply_3(v___f_3555_, v___x_3573_, v___y_3556_, lean_box(0));
return v___x_3574_;
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v_val_3564_);
lean_dec_ref(v___f_3555_);
v_a_3575_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3568_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3568_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
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
lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec(v_val_3564_);
lean_dec(v_capacity_3560_);
v___x_3583_ = lean_box(v_closed_3559_);
lean_inc(v___y_3556_);
v___x_3584_ = lean_apply_3(v___f_3555_, v___x_3583_, v___y_3556_, lean_box(0));
return v___x_3584_;
}
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec(v___x_3563_);
lean_dec(v_size_3561_);
lean_dec(v_capacity_3560_);
v___x_3585_ = lean_box(v_closed_3559_);
lean_inc(v___y_3556_);
v___x_3586_ = lean_apply_3(v___f_3555_, v___x_3585_, v___y_3556_, lean_box(0));
return v___x_3586_;
}
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec(v___x_3558_);
v___x_3587_ = lean_box(v_closed_3559_);
lean_inc(v___y_3556_);
v___x_3588_ = lean_apply_3(v___f_3555_, v___x_3587_, v___y_3556_, lean_box(0));
return v___x_3588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3589_, lean_object* v___f_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3589_, v___f_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec(v_id_3589_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; lean_object* v_producers_3598_; lean_object* v_waiters_3599_; lean_object* v_capacity_3600_; lean_object* v_size_3601_; lean_object* v_buffer_3602_; lean_object* v_write_3603_; lean_object* v_read_3604_; lean_object* v_receivers_3605_; lean_object* v_nextId_3606_; uint8_t v_closed_3607_; lean_object* v_pos_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3630_; 
v___x_3597_ = lean_st_ref_get(v___y_3595_);
v_producers_3598_ = lean_ctor_get(v___x_3597_, 0);
v_waiters_3599_ = lean_ctor_get(v___x_3597_, 1);
v_capacity_3600_ = lean_ctor_get(v___x_3597_, 2);
v_size_3601_ = lean_ctor_get(v___x_3597_, 3);
v_buffer_3602_ = lean_ctor_get(v___x_3597_, 4);
v_write_3603_ = lean_ctor_get(v___x_3597_, 5);
v_read_3604_ = lean_ctor_get(v___x_3597_, 6);
v_receivers_3605_ = lean_ctor_get(v___x_3597_, 7);
v_nextId_3606_ = lean_ctor_get(v___x_3597_, 8);
v_closed_3607_ = lean_ctor_get_uint8(v___x_3597_, sizeof(void*)*10);
v_pos_3608_ = lean_ctor_get(v___x_3597_, 9);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3610_ = v___x_3597_;
v_isShared_3611_ = v_isSharedCheck_3630_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_pos_3608_);
lean_inc(v_nextId_3606_);
lean_inc(v_receivers_3605_);
lean_inc(v_read_3604_);
lean_inc(v_write_3603_);
lean_inc(v_buffer_3602_);
lean_inc(v_size_3601_);
lean_inc(v_capacity_3600_);
lean_inc(v_waiters_3599_);
lean_inc(v_producers_3598_);
lean_dec(v___x_3597_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3630_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3599_);
if (lean_obj_tag(v___x_3612_) == 1)
{
lean_object* v_val_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3627_; 
v_val_3613_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3615_ = v___x_3612_;
v_isShared_3616_ = v_isSharedCheck_3627_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_val_3613_);
lean_dec(v___x_3612_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3627_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v_fst_3617_; lean_object* v_snd_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
v_fst_3617_ = lean_ctor_get(v_val_3613_, 0);
lean_inc(v_fst_3617_);
v_snd_3618_ = lean_ctor_get(v_val_3613_, 1);
lean_inc(v_snd_3618_);
lean_dec(v_val_3613_);
v___x_3619_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3617_, v_____do__lift_3594_);
lean_dec(v_fst_3617_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 1, v_snd_3618_);
v___x_3621_ = v___x_3610_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_producers_3598_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_snd_3618_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_capacity_3600_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_size_3601_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_buffer_3602_);
lean_ctor_set(v_reuseFailAlloc_3626_, 5, v_write_3603_);
lean_ctor_set(v_reuseFailAlloc_3626_, 6, v_read_3604_);
lean_ctor_set(v_reuseFailAlloc_3626_, 7, v_receivers_3605_);
lean_ctor_set(v_reuseFailAlloc_3626_, 8, v_nextId_3606_);
lean_ctor_set(v_reuseFailAlloc_3626_, 9, v_pos_3608_);
lean_ctor_set_uint8(v_reuseFailAlloc_3626_, sizeof(void*)*10, v_closed_3607_);
v___x_3621_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3622_ = lean_st_ref_set(v___y_3595_, v___x_3621_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set_tag(v___x_3615_, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3622_);
v___x_3624_ = v___x_3615_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
lean_dec(v___x_3612_);
lean_del_object(v___x_3610_);
lean_dec(v_pos_3608_);
lean_dec(v_nextId_3606_);
lean_dec(v_receivers_3605_);
lean_dec(v_read_3604_);
lean_dec(v_write_3603_);
lean_dec_ref(v_buffer_3602_);
lean_dec(v_size_3601_);
lean_dec(v_capacity_3600_);
lean_dec_ref(v_producers_3598_);
v___x_3628_ = lean_box(0);
v___x_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
return v___x_3629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
uint8_t v_____do__lift_4155__boxed_3634_; lean_object* v_res_3635_; 
v_____do__lift_4155__boxed_3634_ = lean_unbox(v_____do__lift_3631_);
v_res_3635_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_4155__boxed_3634_, v___y_3632_);
lean_dec(v___y_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3636_, lean_object* v___f_3637_, lean_object* v_id_3638_, uint8_t v_____do__lift_3639_, lean_object* v___y_3640_){
_start:
{
if (v_____do__lift_3639_ == 0)
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_producers_3644_; lean_object* v_waiters_3645_; lean_object* v_capacity_3646_; lean_object* v_size_3647_; lean_object* v_buffer_3648_; lean_object* v_write_3649_; lean_object* v_read_3650_; lean_object* v_receivers_3651_; lean_object* v_nextId_3652_; uint8_t v_closed_3653_; lean_object* v_pos_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3668_; 
lean_dec(v_id_3638_);
v___x_3642_ = lean_io_promise_new();
v___x_3643_ = lean_st_ref_take(v___y_3640_);
v_producers_3644_ = lean_ctor_get(v___x_3643_, 0);
v_waiters_3645_ = lean_ctor_get(v___x_3643_, 1);
v_capacity_3646_ = lean_ctor_get(v___x_3643_, 2);
v_size_3647_ = lean_ctor_get(v___x_3643_, 3);
v_buffer_3648_ = lean_ctor_get(v___x_3643_, 4);
v_write_3649_ = lean_ctor_get(v___x_3643_, 5);
v_read_3650_ = lean_ctor_get(v___x_3643_, 6);
v_receivers_3651_ = lean_ctor_get(v___x_3643_, 7);
v_nextId_3652_ = lean_ctor_get(v___x_3643_, 8);
v_closed_3653_ = lean_ctor_get_uint8(v___x_3643_, sizeof(void*)*10);
v_pos_3654_ = lean_ctor_get(v___x_3643_, 9);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3656_ = v___x_3643_;
v_isShared_3657_ = v_isSharedCheck_3668_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_pos_3654_);
lean_inc(v_nextId_3652_);
lean_inc(v_receivers_3651_);
lean_inc(v_read_3650_);
lean_inc(v_write_3649_);
lean_inc(v_buffer_3648_);
lean_inc(v_size_3647_);
lean_inc(v_capacity_3646_);
lean_inc(v_waiters_3645_);
lean_inc(v_producers_3644_);
lean_dec(v___x_3643_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3668_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
v___x_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3658_, 0, v_waiter_3636_);
lean_inc(v___x_3642_);
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3642_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = l_Std_Queue_enqueue___redArg(v___x_3659_, v_waiters_3645_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 1, v___x_3660_);
v___x_3662_ = v___x_3656_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_producers_3644_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_capacity_3646_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_size_3647_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v_buffer_3648_);
lean_ctor_set(v_reuseFailAlloc_3667_, 5, v_write_3649_);
lean_ctor_set(v_reuseFailAlloc_3667_, 6, v_read_3650_);
lean_ctor_set(v_reuseFailAlloc_3667_, 7, v_receivers_3651_);
lean_ctor_set(v_reuseFailAlloc_3667_, 8, v_nextId_3652_);
lean_ctor_set(v_reuseFailAlloc_3667_, 9, v_pos_3654_);
lean_ctor_set_uint8(v_reuseFailAlloc_3667_, sizeof(void*)*10, v_closed_3653_);
v___x_3662_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3663_ = lean_st_ref_set(v___y_3640_, v___x_3662_);
v___x_3664_ = lean_io_promise_result_opt(v___x_3642_);
lean_dec(v___x_3642_);
v___x_3665_ = lean_unsigned_to_nat(0u);
v___x_3666_ = l_EIO_chainTask___redArg(v___x_3664_, v___f_3637_, v___x_3665_, v_____do__lift_3639_);
return v___x_3666_;
}
}
}
else
{
lean_object* v___x_3669_; lean_object* v_lose_3670_; lean_object* v___x_3671_; 
lean_dec_ref(v___f_3637_);
v___x_3669_ = lean_box(v_____do__lift_3639_);
v_lose_3670_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3670_, 0, v___x_3669_);
v___x_3671_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3638_, v_waiter_3636_, v_lose_3670_, v___y_3640_);
lean_dec_ref(v_waiter_3636_);
return v___x_3671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3672_, lean_object* v___f_3673_, lean_object* v_id_3674_, lean_object* v_____do__lift_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v_____do__lift_4211__boxed_3678_; lean_object* v_res_3679_; 
v_____do__lift_4211__boxed_3678_ = lean_unbox(v_____do__lift_3675_);
v_res_3679_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3672_, v___f_3673_, v_id_3674_, v_____do__lift_4211__boxed_3678_, v___y_3676_);
lean_dec(v___y_3676_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3682_, lean_object* v_ch_3683_, lean_object* v_res_x3f_3684_){
_start:
{
if (lean_obj_tag(v_res_x3f_3684_) == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_dec_ref(v_ch_3683_);
lean_dec_ref(v_waiter_3682_);
v___x_3686_ = lean_box(0);
v___x_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
return v___x_3687_;
}
else
{
lean_object* v_val_3688_; uint8_t v___x_3689_; 
v_val_3688_ = lean_ctor_get(v_res_x3f_3684_, 0);
v___x_3689_ = lean_unbox(v_val_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___f_3690_; lean_object* v___x_3691_; 
lean_dec_ref(v_ch_3683_);
v___f_3690_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3691_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3682_, v___f_3690_);
lean_dec_ref(v_waiter_3682_);
return v___x_3691_;
}
else
{
lean_object* v___x_3692_; 
v___x_3692_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3683_, v_waiter_3682_);
return v___x_3692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3693_, lean_object* v_ch_3694_, lean_object* v_res_x3f_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3693_, v_ch_3694_, v_res_x3f_3695_);
lean_dec(v_res_x3f_3695_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3698_, lean_object* v_waiter_3699_){
_start:
{
lean_object* v_state_3701_; lean_object* v_id_3702_; lean_object* v___f_3703_; lean_object* v___f_3704_; lean_object* v___f_3705_; lean_object* v___x_3706_; 
v_state_3701_ = lean_ctor_get(v_ch_3698_, 0);
lean_inc_ref(v_state_3701_);
v_id_3702_ = lean_ctor_get(v_ch_3698_, 1);
lean_inc_n(v_id_3702_, 2);
lean_inc_ref(v_waiter_3699_);
v___f_3703_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3703_, 0, v_waiter_3699_);
lean_closure_set(v___f_3703_, 1, v_ch_3698_);
v___f_3704_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3704_, 0, v_waiter_3699_);
lean_closure_set(v___f_3704_, 1, v___f_3703_);
lean_closure_set(v___f_3704_, 2, v_id_3702_);
v___f_3705_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3705_, 0, v_id_3702_);
lean_closure_set(v___f_3705_, 1, v___f_3704_);
v___x_3706_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3701_, v___f_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3707_, lean_object* v_waiter_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3707_, v_waiter_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3711_, lean_object* v_ch_3712_, lean_object* v_waiter_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3712_, v_waiter_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3716_, lean_object* v_ch_3717_, lean_object* v_waiter_3718_, lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3716_, v_ch_3717_, v_waiter_3718_);
return v_res_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3721_, lean_object* v_receiverId_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3722_, v_a_3723_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3726_, lean_object* v_receiverId_3727_, lean_object* v_a_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3726_, v_receiverId_3727_, v_a_3728_);
lean_dec(v_a_3728_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3731_, lean_object* v_x_3732_){
_start:
{
if (lean_obj_tag(v_x_3732_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3742_; 
v_a_3734_ = lean_ctor_get(v_x_3732_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_x_3732_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3736_ = v_x_3732_;
v_isShared_3737_ = v_isSharedCheck_3742_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v_x_3732_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3742_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3755_; 
v_a_3743_ = lean_ctor_get(v_x_3732_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_x_3732_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3745_ = v_x_3732_;
v_isShared_3746_ = v_isSharedCheck_3755_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v_x_3732_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3755_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_capacity_3747_; lean_object* v_buffer_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v_capacity_3747_ = lean_ctor_get(v_a_3743_, 2);
lean_inc(v_capacity_3747_);
v_buffer_3748_ = lean_ctor_get(v_a_3743_, 4);
lean_inc_ref(v_buffer_3748_);
lean_dec(v_a_3743_);
v___x_3749_ = lean_nat_mod(v_place_3731_, v_capacity_3747_);
lean_dec(v_capacity_3747_);
v___x_3750_ = lean_array_fget(v_buffer_3748_, v___x_3749_);
lean_dec(v___x_3749_);
lean_dec_ref(v_buffer_3748_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3750_);
v___x_3752_ = v___x_3745_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
return v___x_3753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3756_, lean_object* v_x_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3756_, v_x_3757_);
lean_dec(v_place_3756_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v___x_3763_; lean_object* v___f_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; uint8_t v___x_3768_; lean_object* v___x_3769_; 
v___x_3763_ = lean_st_ref_get(v_a_3761_);
v___f_3764_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3764_, 0, v_place_3760_);
v___x_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
v___x_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
v___x_3767_ = lean_unsigned_to_nat(0u);
v___x_3768_ = 0;
v___x_3769_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3767_, v___x_3768_, v___x_3766_, v___f_3764_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3770_, lean_object* v_a_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3770_, v_a_3771_);
lean_dec(v_a_3771_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3774_, lean_object* v_place_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3775_, v_a_3776_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3779_, lean_object* v_place_3780_, lean_object* v_a_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3779_, v_place_3780_, v_a_3781_);
lean_dec(v_a_3781_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_3784_, lean_object* v_x_3785_){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3787_ = lean_io_basemutex_unlock(v_mutex_3784_);
v___x_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3787_);
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_3790_, lean_object* v_x_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(v_mutex_3790_, v_x_3791_);
lean_dec(v_x_3791_);
lean_dec(v_mutex_3790_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_3794_, lean_object* v_ref_3795_, lean_object* v_x_3796_){
_start:
{
if (lean_obj_tag(v_x_3796_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3806_; 
lean_dec(v_ref_3795_);
lean_dec_ref(v_k_3794_);
v_a_3798_ = lean_ctor_get(v_x_3796_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_x_3796_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3800_ = v_x_3796_;
v_isShared_3801_ = v_isSharedCheck_3806_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v_x_3796_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3806_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3804_; 
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
return v___x_3804_;
}
}
}
else
{
lean_object* v___x_3807_; 
lean_dec_ref(v_x_3796_);
v___x_3807_ = lean_apply_2(v_k_3794_, v_ref_3795_, lean_box(0));
return v___x_3807_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_3808_, lean_object* v_ref_3809_, lean_object* v_x_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_k_3808_, v_ref_3809_, v_x_3810_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_3813_, lean_object* v___f_3814_){
_start:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; lean_object* v___x_3821_; 
v___x_3816_ = lean_io_basemutex_lock(v_mutex_3813_);
v___x_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
v___x_3819_ = lean_unsigned_to_nat(0u);
v___x_3820_ = 0;
v___x_3821_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3819_, v___x_3820_, v___x_3818_, v___f_3814_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_3822_, lean_object* v___f_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_mutex_3822_, v___f_3823_);
lean_dec(v_mutex_3822_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_3826_){
_start:
{
if (lean_obj_tag(v___y_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
v_a_3827_ = lean_ctor_get(v___y_3826_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___y_3826_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___y_3826_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___y_3826_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
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
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3843_; 
v_a_3835_ = lean_ctor_get(v___y_3826_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___y_3826_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3837_ = v___y_3826_;
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___y_3826_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3843_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v_fst_3839_; lean_object* v___x_3841_; 
v_fst_3839_ = lean_ctor_get(v_a_3835_, 0);
lean_inc(v_fst_3839_);
lean_dec(v_a_3835_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v_fst_3839_);
v___x_3841_ = v___x_3837_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_fst_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_3845_, lean_object* v_k_3846_){
_start:
{
lean_object* v_ref_3848_; lean_object* v_mutex_3849_; lean_object* v___f_3850_; lean_object* v___f_3851_; lean_object* v___f_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v___x_3855_; lean_object* v___y_3857_; 
v_ref_3848_ = lean_ctor_get(v_mutex_3845_, 0);
lean_inc(v_ref_3848_);
v_mutex_3849_ = lean_ctor_get(v_mutex_3845_, 1);
lean_inc_n(v_mutex_3849_, 2);
lean_dec_ref(v_mutex_3845_);
v___f_3850_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3850_, 0, v_mutex_3849_);
v___f_3851_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3851_, 0, v_k_3846_);
lean_closure_set(v___f_3851_, 1, v_ref_3848_);
v___f_3852_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3852_, 0, v_mutex_3849_);
lean_closure_set(v___f_3852_, 1, v___f_3851_);
v___x_3853_ = lean_unsigned_to_nat(0u);
v___x_3854_ = 0;
v___x_3855_ = l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(v___f_3852_, v___f_3850_, v___x_3853_, v___x_3854_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3859_; 
v_a_3859_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3859_);
lean_dec_ref(v___x_3855_);
if (lean_obj_tag(v_a_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
v_a_3860_ = lean_ctor_get(v_a_3859_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_a_3859_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v_a_3859_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v_a_3859_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
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
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
v___y_3857_ = v___x_3865_;
goto v___jp_3856_;
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3876_; 
v_a_3868_ = lean_ctor_get(v_a_3859_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v_a_3859_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3870_ = v_a_3859_;
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v_a_3859_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3876_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v_fst_3872_; lean_object* v___x_3874_; 
v_fst_3872_ = lean_ctor_get(v_a_3868_, 0);
lean_inc(v_fst_3872_);
lean_dec(v_a_3868_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v_fst_3872_);
v___x_3874_ = v___x_3870_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_fst_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
v___y_3857_ = v___x_3874_;
goto v___jp_3856_;
}
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3886_; 
v_a_3877_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3879_ = v___x_3855_;
v_isShared_3880_ = v_isSharedCheck_3886_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3855_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3886_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___f_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___f_3881_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___x_3882_ = lean_task_map(v___f_3881_, v_a_3877_, v___x_3853_, v___x_3854_);
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 0, v___x_3882_);
v___x_3884_ = v___x_3879_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
v___jp_3856_:
{
lean_object* v___x_3858_; 
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___y_3857_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_3887_, lean_object* v_k_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3887_, v_k_3888_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_3891_, lean_object* v_00_u03b2_3892_, lean_object* v_mutex_3893_, lean_object* v_k_3894_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3893_, v_k_3894_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_3897_, lean_object* v_00_u03b2_3898_, lean_object* v_mutex_3899_, lean_object* v_k_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_3897_, v_00_u03b2_3898_, v_mutex_3899_, v_k_3900_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_3903_, lean_object* v_capacity_3904_, lean_object* v_size_3905_, lean_object* v_buffer_3906_, lean_object* v_write_3907_, lean_object* v_read_3908_, lean_object* v_receivers_3909_, lean_object* v_nextId_3910_, uint8_t v_closed_3911_, lean_object* v_pos_3912_, lean_object* v___y_3913_, lean_object* v_x_3914_){
_start:
{
if (lean_obj_tag(v_x_3914_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3924_; 
lean_dec(v_pos_3912_);
lean_dec(v_nextId_3910_);
lean_dec(v_receivers_3909_);
lean_dec(v_read_3908_);
lean_dec(v_write_3907_);
lean_dec_ref(v_buffer_3906_);
lean_dec(v_size_3905_);
lean_dec(v_capacity_3904_);
lean_dec_ref(v_producers_3903_);
v_a_3916_ = lean_ctor_get(v_x_3914_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_x_3914_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3918_ = v_x_3914_;
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v_x_3914_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3924_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3935_; 
v_a_3925_ = lean_ctor_get(v_x_3914_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_x_3914_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3927_ = v_x_3914_;
v_isShared_3928_ = v_isSharedCheck_3935_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v_x_3914_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3935_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
v___x_3929_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3929_, 0, v_producers_3903_);
lean_ctor_set(v___x_3929_, 1, v_a_3925_);
lean_ctor_set(v___x_3929_, 2, v_capacity_3904_);
lean_ctor_set(v___x_3929_, 3, v_size_3905_);
lean_ctor_set(v___x_3929_, 4, v_buffer_3906_);
lean_ctor_set(v___x_3929_, 5, v_write_3907_);
lean_ctor_set(v___x_3929_, 6, v_read_3908_);
lean_ctor_set(v___x_3929_, 7, v_receivers_3909_);
lean_ctor_set(v___x_3929_, 8, v_nextId_3910_);
lean_ctor_set(v___x_3929_, 9, v_pos_3912_);
lean_ctor_set_uint8(v___x_3929_, sizeof(void*)*10, v_closed_3911_);
v___x_3930_ = lean_st_ref_set(v___y_3913_, v___x_3929_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3930_);
v___x_3932_ = v___x_3927_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3930_);
v___x_3932_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; 
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
}
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
lean_dec_ref(v_x_4002_);
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
lean_dec_ref(v_x_4029_);
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
v___x_4056_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4054_, v___x_4055_, v___x_4053_, v___f_4050_);
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
v___x_4042_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4040_, v___x_4041_, v_val_4039_, v___f_4037_);
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
lean_dec_ref(v_x_4062_);
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
lean_dec_ref(v_x_4085_);
lean_inc(v___x_4083_);
v___x_4097_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4082_, v___x_4083_);
v___x_4098_ = lean_unsigned_to_nat(0u);
v___x_4099_ = 0;
v___x_4100_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4098_, v___x_4099_, v___x_4097_, v___f_4084_);
v___f_4101_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4101_, 0, v_a_4096_);
lean_closure_set(v___f_4101_, 1, v___x_4083_);
v___x_4102_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4098_, v___x_4099_, v___x_4100_, v___f_4101_);
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
v___x_4120_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4118_, v___x_4119_, v___x_4116_, v___f_4117_);
v___f_4121_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4121_, 0, v_eList_4113_);
lean_closure_set(v___f_4121_, 1, v___x_4115_);
lean_closure_set(v___f_4121_, 2, v___f_4117_);
v___x_4122_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4118_, v___x_4119_, v___x_4120_, v___f_4121_);
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
lean_dec_ref(v_x_4128_);
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
v___x_4156_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4154_, v___x_4155_, v___x_4151_, v___f_4153_);
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
v___x_4169_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4167_, v___x_4168_, v___x_4166_, v___f_4164_);
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
v___x_4274_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4252_, v_closed_4253_, v___x_4273_, v___f_4254_);
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
v___x_4317_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4310_, v_closed_4301_, v___x_4313_, v___f_4316_);
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
lean_dec_ref(v_x_4343_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4365_, lean_object* v_receiverId_4366_, lean_object* v_receivers_4367_, lean_object* v_x_4368_){
_start:
{
if (lean_obj_tag(v_x_4368_) == 0)
{
lean_object* v___x_4370_; 
lean_dec(v_receivers_4367_);
lean_dec(v_receiverId_4366_);
v___x_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4370_, 0, v_x_4368_);
return v___x_4370_;
}
else
{
lean_object* v_a_4371_; 
v_a_4371_ = lean_ctor_get(v_x_4368_, 0);
if (lean_obj_tag(v_a_4371_) == 1)
{
lean_object* v___x_4372_; lean_object* v_producers_4373_; lean_object* v_waiters_4374_; lean_object* v_capacity_4375_; lean_object* v_size_4376_; lean_object* v_buffer_4377_; lean_object* v_write_4378_; lean_object* v_read_4379_; lean_object* v_nextId_4380_; uint8_t v_closed_4381_; lean_object* v_pos_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4396_; 
v___x_4372_ = lean_st_ref_take(v_a_4365_);
v_producers_4373_ = lean_ctor_get(v___x_4372_, 0);
v_waiters_4374_ = lean_ctor_get(v___x_4372_, 1);
v_capacity_4375_ = lean_ctor_get(v___x_4372_, 2);
v_size_4376_ = lean_ctor_get(v___x_4372_, 3);
v_buffer_4377_ = lean_ctor_get(v___x_4372_, 4);
v_write_4378_ = lean_ctor_get(v___x_4372_, 5);
v_read_4379_ = lean_ctor_get(v___x_4372_, 6);
v_nextId_4380_ = lean_ctor_get(v___x_4372_, 8);
v_closed_4381_ = lean_ctor_get_uint8(v___x_4372_, sizeof(void*)*10);
v_pos_4382_ = lean_ctor_get(v___x_4372_, 9);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4396_ == 0)
{
lean_object* v_unused_4397_; 
v_unused_4397_ = lean_ctor_get(v___x_4372_, 7);
lean_dec(v_unused_4397_);
v___x_4384_ = v___x_4372_;
v_isShared_4385_ = v_isSharedCheck_4396_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_pos_4382_);
lean_inc(v_nextId_4380_);
lean_inc(v_read_4379_);
lean_inc(v_write_4378_);
lean_inc(v_buffer_4377_);
lean_inc(v_size_4376_);
lean_inc(v_capacity_4375_);
lean_inc(v_waiters_4374_);
lean_inc(v_producers_4373_);
lean_dec(v___x_4372_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4396_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; lean_object* v___x_4388_; 
v___x_4386_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4366_, v_receivers_4367_);
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 7, v___x_4386_);
v___x_4388_ = v___x_4384_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_producers_4373_);
lean_ctor_set(v_reuseFailAlloc_4395_, 1, v_waiters_4374_);
lean_ctor_set(v_reuseFailAlloc_4395_, 2, v_capacity_4375_);
lean_ctor_set(v_reuseFailAlloc_4395_, 3, v_size_4376_);
lean_ctor_set(v_reuseFailAlloc_4395_, 4, v_buffer_4377_);
lean_ctor_set(v_reuseFailAlloc_4395_, 5, v_write_4378_);
lean_ctor_set(v_reuseFailAlloc_4395_, 6, v_read_4379_);
lean_ctor_set(v_reuseFailAlloc_4395_, 7, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4395_, 8, v_nextId_4380_);
lean_ctor_set(v_reuseFailAlloc_4395_, 9, v_pos_4382_);
lean_ctor_set_uint8(v_reuseFailAlloc_4395_, sizeof(void*)*10, v_closed_4381_);
v___x_4388_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4389_; lean_object* v___f_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; lean_object* v___x_4394_; 
v___x_4389_ = lean_st_ref_set(v_a_4365_, v___x_4388_);
v___f_4390_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4390_, 0, v_x_4368_);
v___x_4391_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_4392_ = lean_unsigned_to_nat(0u);
v___x_4393_ = 0;
v___x_4394_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4392_, v___x_4393_, v___x_4391_, v___f_4390_);
return v___x_4394_;
}
}
}
else
{
lean_object* v___x_4398_; 
lean_dec_ref(v_x_4368_);
lean_dec(v_receivers_4367_);
lean_dec(v_receiverId_4366_);
v___x_4398_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4398_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4399_, lean_object* v_receiverId_4400_, lean_object* v_receivers_4401_, lean_object* v_x_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4399_, v_receiverId_4400_, v_receivers_4401_, v_x_4402_);
lean_dec(v_a_4399_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4405_){
_start:
{
if (lean_obj_tag(v_x_4405_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4415_; 
v_a_4407_ = lean_ctor_get(v_x_4405_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v_x_4405_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4409_ = v_x_4405_;
v_isShared_4410_ = v_isSharedCheck_4415_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v_x_4405_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4415_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
return v___x_4413_;
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4428_; 
v_a_4416_ = lean_ctor_get(v_x_4405_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_x_4405_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4418_ = v_x_4405_;
v_isShared_4419_ = v_isSharedCheck_4428_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v_x_4405_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4428_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v_size_4420_; lean_object* v___x_4421_; uint8_t v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4425_; 
v_size_4420_ = lean_ctor_get(v_a_4416_, 3);
lean_inc(v_size_4420_);
lean_dec(v_a_4416_);
v___x_4421_ = lean_unsigned_to_nat(0u);
v___x_4422_ = lean_nat_dec_eq(v_size_4420_, v___x_4421_);
lean_dec(v_size_4420_);
v___x_4423_ = lean_box(v___x_4422_);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4423_);
v___x_4425_ = v___x_4418_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4423_);
v___x_4425_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_object* v___x_4426_; 
v___x_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
return v___x_4426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4429_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4433_){
_start:
{
lean_object* v___x_4435_; lean_object* v___f_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; uint8_t v___x_4440_; lean_object* v___x_4441_; 
v___x_4435_ = lean_st_ref_get(v_a_4433_);
v___f_4436_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
v___x_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
v___x_4439_ = lean_unsigned_to_nat(0u);
v___x_4440_ = 0;
v___x_4441_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4439_, v___x_4440_, v___x_4438_, v___f_4436_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4442_);
lean_dec(v_a_4442_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4445_, lean_object* v_next_4446_){
_start:
{
lean_object* v___x_4448_; lean_object* v_fst_4450_; lean_object* v_snd_4451_; lean_object* v_value_4455_; lean_object* v_pos_4456_; lean_object* v_remaining_4457_; uint8_t v___x_4458_; 
v___x_4448_ = lean_st_ref_take(v_slot_4445_);
v_value_4455_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_value_4455_);
v_pos_4456_ = lean_ctor_get(v___x_4448_, 1);
lean_inc(v_pos_4456_);
v_remaining_4457_ = lean_ctor_get(v___x_4448_, 2);
lean_inc(v_remaining_4457_);
v___x_4458_ = lean_nat_dec_eq(v_next_4446_, v_pos_4456_);
if (v___x_4458_ == 0)
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
lean_dec(v_remaining_4457_);
lean_dec(v_pos_4456_);
lean_dec(v_value_4455_);
v___x_4459_ = lean_box(0);
v___x_4460_ = lean_box(v___x_4458_);
v___x_4461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4459_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v_fst_4450_ = v___x_4461_;
v_snd_4451_ = v___x_4448_;
goto v___jp_4449_;
}
else
{
lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4480_; 
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4480_ == 0)
{
lean_object* v_unused_4481_; lean_object* v_unused_4482_; lean_object* v_unused_4483_; 
v_unused_4481_ = lean_ctor_get(v___x_4448_, 2);
lean_dec(v_unused_4481_);
v_unused_4482_ = lean_ctor_get(v___x_4448_, 1);
lean_dec(v_unused_4482_);
v_unused_4483_ = lean_ctor_get(v___x_4448_, 0);
lean_dec(v_unused_4483_);
v___x_4463_ = v___x_4448_;
v_isShared_4464_ = v_isSharedCheck_4480_;
goto v_resetjp_4462_;
}
else
{
lean_dec(v___x_4448_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4480_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4465_; uint8_t v___x_4466_; 
v___x_4465_ = lean_unsigned_to_nat(1u);
v___x_4466_ = lean_nat_dec_eq(v_remaining_4457_, v___x_4465_);
if (v___x_4466_ == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4471_; 
v___x_4467_ = lean_box(v___x_4466_);
lean_inc(v_value_4455_);
v___x_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4468_, 0, v_value_4455_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
v___x_4469_ = lean_nat_sub(v_remaining_4457_, v___x_4465_);
lean_dec(v_remaining_4457_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 2, v___x_4469_);
v___x_4471_ = v___x_4463_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_value_4455_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_pos_4456_);
lean_ctor_set(v_reuseFailAlloc_4472_, 2, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
v_fst_4450_ = v___x_4468_;
v_snd_4451_ = v___x_4471_;
goto v___jp_4449_;
}
}
else
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4478_; 
lean_dec(v_remaining_4457_);
v___x_4473_ = lean_box(v___x_4458_);
v___x_4474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4474_, 0, v_value_4455_);
lean_ctor_set(v___x_4474_, 1, v___x_4473_);
v___x_4475_ = lean_box(0);
v___x_4476_ = lean_unsigned_to_nat(0u);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 2, v___x_4476_);
lean_ctor_set(v___x_4463_, 0, v___x_4475_);
v___x_4478_ = v___x_4463_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_pos_4456_);
lean_ctor_set(v_reuseFailAlloc_4479_, 2, v___x_4476_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
v_fst_4450_ = v___x_4474_;
v_snd_4451_ = v___x_4478_;
goto v___jp_4449_;
}
}
}
}
v___jp_4449_:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = lean_st_ref_set(v_slot_4445_, v_snd_4451_);
v___x_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4453_, 0, v_fst_4450_);
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
return v___x_4454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4484_, lean_object* v_next_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4484_, v_next_4485_);
lean_dec(v_next_4485_);
lean_dec(v_slot_4484_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4488_, uint8_t v_a_4489_, lean_object* v___f_4490_, lean_object* v_x_4491_){
_start:
{
if (lean_obj_tag(v_x_4491_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4501_; 
lean_dec_ref(v___f_4490_);
v_a_4493_ = lean_ctor_get(v_x_4491_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v_x_4491_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4495_ = v_x_4491_;
v_isShared_4496_ = v_isSharedCheck_4501_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v_x_4491_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4501_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; 
v___x_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
return v___x_4499_;
}
}
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; 
v_a_4502_ = lean_ctor_get(v_x_4491_, 0);
lean_inc(v_a_4502_);
lean_dec_ref(v_x_4491_);
v___x_4503_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4502_, v_next_4488_);
lean_dec(v_a_4502_);
v___x_4504_ = lean_unsigned_to_nat(0u);
v___x_4505_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4504_, v_a_4489_, v___x_4503_, v___f_4490_);
return v___x_4505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4506_, lean_object* v_a_4507_, lean_object* v___f_4508_, lean_object* v_x_4509_, lean_object* v___y_4510_){
_start:
{
uint8_t v_a_11569__boxed_4511_; lean_object* v_res_4512_; 
v_a_11569__boxed_4511_ = lean_unbox(v_a_4507_);
v_res_4512_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4506_, v_a_11569__boxed_4511_, v___f_4508_, v_x_4509_);
lean_dec(v_next_4506_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4513_, lean_object* v___f_4514_, lean_object* v_____r_4515_, lean_object* v_st_4516_, lean_object* v___y_4517_){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4519_ = lean_st_ref_set(v___y_4517_, v_st_4516_);
v___x_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
v___x_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4520_);
v___x_4522_ = lean_unsigned_to_nat(0u);
v___x_4523_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4522_, v_a_4513_, v___x_4521_, v___f_4514_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4524_, lean_object* v___f_4525_, lean_object* v_____r_4526_, lean_object* v_st_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
uint8_t v_a_11607__boxed_4530_; lean_object* v_res_4531_; 
v_a_11607__boxed_4530_ = lean_unbox(v_a_4524_);
v_res_4531_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_11607__boxed_4530_, v___f_4525_, v_____r_4526_, v_st_4527_, v___y_4528_);
lean_dec(v___y_4528_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4532_, lean_object* v_waiters_4533_, lean_object* v_capacity_4534_, lean_object* v_size_4535_, lean_object* v_buffer_4536_, lean_object* v_write_4537_, lean_object* v_read_4538_, lean_object* v_receivers_4539_, lean_object* v_nextId_4540_, uint8_t v_closed_4541_, lean_object* v_pos_4542_, lean_object* v___f_4543_, lean_object* v_a_4544_, lean_object* v_x_4545_){
_start:
{
if (lean_obj_tag(v_x_4545_) == 0)
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4555_; 
lean_dec_ref(v___f_4543_);
lean_dec(v_pos_4542_);
lean_dec(v_nextId_4540_);
lean_dec(v_receivers_4539_);
lean_dec(v_read_4538_);
lean_dec(v_write_4537_);
lean_dec_ref(v_buffer_4536_);
lean_dec(v_size_4535_);
lean_dec(v_capacity_4534_);
lean_dec_ref(v_waiters_4533_);
lean_dec_ref(v_snd_4532_);
v_a_4547_ = lean_ctor_get(v_x_4545_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v_x_4545_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4549_ = v_x_4545_;
v_isShared_4550_ = v_isSharedCheck_4555_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v_x_4545_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4555_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_object* v___x_4553_; 
v___x_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
return v___x_4553_;
}
}
}
else
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; 
lean_dec_ref(v_x_4545_);
v___x_4556_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4556_, 0, v_snd_4532_);
lean_ctor_set(v___x_4556_, 1, v_waiters_4533_);
lean_ctor_set(v___x_4556_, 2, v_capacity_4534_);
lean_ctor_set(v___x_4556_, 3, v_size_4535_);
lean_ctor_set(v___x_4556_, 4, v_buffer_4536_);
lean_ctor_set(v___x_4556_, 5, v_write_4537_);
lean_ctor_set(v___x_4556_, 6, v_read_4538_);
lean_ctor_set(v___x_4556_, 7, v_receivers_4539_);
lean_ctor_set(v___x_4556_, 8, v_nextId_4540_);
lean_ctor_set(v___x_4556_, 9, v_pos_4542_);
lean_ctor_set_uint8(v___x_4556_, sizeof(void*)*10, v_closed_4541_);
v___x_4557_ = lean_box(0);
lean_inc(v_a_4544_);
v___x_4558_ = lean_apply_4(v___f_4543_, v___x_4557_, v___x_4556_, v_a_4544_, lean_box(0));
return v___x_4558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4559_, lean_object* v_waiters_4560_, lean_object* v_capacity_4561_, lean_object* v_size_4562_, lean_object* v_buffer_4563_, lean_object* v_write_4564_, lean_object* v_read_4565_, lean_object* v_receivers_4566_, lean_object* v_nextId_4567_, lean_object* v_closed_4568_, lean_object* v_pos_4569_, lean_object* v___f_4570_, lean_object* v_a_4571_, lean_object* v_x_4572_, lean_object* v___y_4573_){
_start:
{
uint8_t v_closed_boxed_4574_; lean_object* v_res_4575_; 
v_closed_boxed_4574_ = lean_unbox(v_closed_4568_);
v_res_4575_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4559_, v_waiters_4560_, v_capacity_4561_, v_size_4562_, v_buffer_4563_, v_write_4564_, v_read_4565_, v_receivers_4566_, v_nextId_4567_, v_closed_boxed_4574_, v_pos_4569_, v___f_4570_, v_a_4571_, v_x_4572_);
lean_dec(v_a_4571_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4576_, lean_object* v_x_4577_){
_start:
{
if (lean_obj_tag(v_x_4577_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_fst_4576_);
v_a_4579_ = lean_ctor_get(v_x_4577_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_x_4577_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4581_ = v_x_4577_;
v_isShared_4582_ = v_isSharedCheck_4587_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v_x_4577_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4587_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; 
v___x_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___x_4584_);
return v___x_4585_;
}
}
}
else
{
lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4595_; 
v_isSharedCheck_4595_ = !lean_is_exclusive(v_x_4577_);
if (v_isSharedCheck_4595_ == 0)
{
lean_object* v_unused_4596_; 
v_unused_4596_ = lean_ctor_get(v_x_4577_, 0);
lean_dec(v_unused_4596_);
v___x_4589_ = v_x_4577_;
v_isShared_4590_ = v_isSharedCheck_4595_;
goto v_resetjp_4588_;
}
else
{
lean_dec(v_x_4577_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4595_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v_fst_4576_);
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_fst_4576_);
v___x_4592_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4592_);
return v___x_4593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4597_, lean_object* v_x_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v_res_4600_; 
v_res_4600_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4597_, v_x_4598_);
return v_res_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, uint8_t v___x_4604_, lean_object* v_x_4605_){
_start:
{
if (lean_obj_tag(v_x_4605_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4615_; 
lean_dec_ref(v_a_4602_);
v_a_4607_ = lean_ctor_get(v_x_4605_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v_x_4605_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4609_ = v_x_4605_;
v_isShared_4610_ = v_isSharedCheck_4615_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v_x_4605_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4615_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4613_; 
v___x_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4612_);
return v___x_4613_;
}
}
}
else
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4663_; 
v_a_4616_ = lean_ctor_get(v_x_4605_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v_x_4605_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4618_ = v_x_4605_;
v_isShared_4619_ = v_isSharedCheck_4663_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v_x_4605_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4663_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v_fst_4620_; 
v_fst_4620_ = lean_ctor_get(v_a_4616_, 0);
lean_inc(v_fst_4620_);
if (lean_obj_tag(v_fst_4620_) == 1)
{
lean_object* v_snd_4621_; lean_object* v___f_4622_; lean_object* v___x_4623_; lean_object* v___f_4624_; uint8_t v___x_4625_; 
v_snd_4621_ = lean_ctor_get(v_a_4616_, 1);
lean_inc(v_snd_4621_);
lean_dec(v_a_4616_);
v___f_4622_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4622_, 0, v_fst_4620_);
v___x_4623_ = lean_box(v_a_4601_);
lean_inc_ref(v___f_4622_);
v___f_4624_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4624_, 0, v___x_4623_);
lean_closure_set(v___f_4624_, 1, v___f_4622_);
v___x_4625_ = lean_unbox(v_snd_4621_);
lean_dec(v_snd_4621_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
lean_dec_ref(v___f_4624_);
lean_del_object(v___x_4618_);
v___x_4626_ = lean_box(0);
v___x_4627_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4601_, v___f_4622_, v___x_4626_, v_a_4602_, v_a_4603_);
return v___x_4627_;
}
else
{
lean_object* v___x_4628_; lean_object* v_producers_4629_; lean_object* v_waiters_4630_; lean_object* v_capacity_4631_; lean_object* v_size_4632_; lean_object* v_buffer_4633_; lean_object* v_write_4634_; lean_object* v_read_4635_; lean_object* v_receivers_4636_; lean_object* v_nextId_4637_; uint8_t v_closed_4638_; lean_object* v_pos_4639_; lean_object* v___x_4640_; 
v___x_4628_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4602_);
v_producers_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc_ref(v_producers_4629_);
v_waiters_4630_ = lean_ctor_get(v___x_4628_, 1);
lean_inc_ref(v_waiters_4630_);
v_capacity_4631_ = lean_ctor_get(v___x_4628_, 2);
lean_inc(v_capacity_4631_);
v_size_4632_ = lean_ctor_get(v___x_4628_, 3);
lean_inc(v_size_4632_);
v_buffer_4633_ = lean_ctor_get(v___x_4628_, 4);
lean_inc_ref(v_buffer_4633_);
v_write_4634_ = lean_ctor_get(v___x_4628_, 5);
lean_inc(v_write_4634_);
v_read_4635_ = lean_ctor_get(v___x_4628_, 6);
lean_inc(v_read_4635_);
v_receivers_4636_ = lean_ctor_get(v___x_4628_, 7);
lean_inc(v_receivers_4636_);
v_nextId_4637_ = lean_ctor_get(v___x_4628_, 8);
lean_inc(v_nextId_4637_);
v_closed_4638_ = lean_ctor_get_uint8(v___x_4628_, sizeof(void*)*10);
v_pos_4639_ = lean_ctor_get(v___x_4628_, 9);
lean_inc(v_pos_4639_);
v___x_4640_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4629_);
if (lean_obj_tag(v___x_4640_) == 1)
{
lean_object* v_val_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4659_; 
lean_dec_ref(v___x_4628_);
lean_dec_ref(v___f_4622_);
v_val_4641_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4643_ = v___x_4640_;
v_isShared_4644_ = v_isSharedCheck_4659_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_val_4641_);
lean_dec(v___x_4640_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4659_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v_fst_4645_; lean_object* v_snd_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___f_4650_; lean_object* v___x_4652_; 
v_fst_4645_ = lean_ctor_get(v_val_4641_, 0);
lean_inc(v_fst_4645_);
v_snd_4646_ = lean_ctor_get(v_val_4641_, 1);
lean_inc(v_snd_4646_);
lean_dec(v_val_4641_);
v___x_4647_ = lean_box(v___x_4604_);
v___x_4648_ = lean_io_promise_resolve(v___x_4647_, v_fst_4645_);
lean_dec(v_fst_4645_);
v___x_4649_ = lean_box(v_closed_4638_);
lean_inc(v_a_4603_);
v___f_4650_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4650_, 0, v_snd_4646_);
lean_closure_set(v___f_4650_, 1, v_waiters_4630_);
lean_closure_set(v___f_4650_, 2, v_capacity_4631_);
lean_closure_set(v___f_4650_, 3, v_size_4632_);
lean_closure_set(v___f_4650_, 4, v_buffer_4633_);
lean_closure_set(v___f_4650_, 5, v_write_4634_);
lean_closure_set(v___f_4650_, 6, v_read_4635_);
lean_closure_set(v___f_4650_, 7, v_receivers_4636_);
lean_closure_set(v___f_4650_, 8, v_nextId_4637_);
lean_closure_set(v___f_4650_, 9, v___x_4649_);
lean_closure_set(v___f_4650_, 10, v_pos_4639_);
lean_closure_set(v___f_4650_, 11, v___f_4624_);
lean_closure_set(v___f_4650_, 12, v_a_4603_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4648_);
v___x_4652_ = v___x_4618_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4648_);
v___x_4652_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
lean_object* v___x_4654_; 
if (v_isShared_4644_ == 0)
{
lean_ctor_set_tag(v___x_4643_, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4652_);
v___x_4654_ = v___x_4643_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4652_);
v___x_4654_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = lean_unsigned_to_nat(0u);
v___x_4656_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4655_, v_a_4601_, v___x_4654_, v___f_4650_);
return v___x_4656_;
}
}
}
}
else
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
lean_dec(v___x_4640_);
lean_dec(v_pos_4639_);
lean_dec(v_nextId_4637_);
lean_dec(v_receivers_4636_);
lean_dec(v_read_4635_);
lean_dec(v_write_4634_);
lean_dec_ref(v_buffer_4633_);
lean_dec(v_size_4632_);
lean_dec(v_capacity_4631_);
lean_dec_ref(v_waiters_4630_);
lean_dec_ref(v___f_4624_);
lean_del_object(v___x_4618_);
v___x_4660_ = lean_box(0);
v___x_4661_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4601_, v___f_4622_, v___x_4660_, v___x_4628_, v_a_4603_);
return v___x_4661_;
}
}
}
else
{
lean_object* v___x_4662_; 
lean_dec(v_fst_4620_);
lean_del_object(v___x_4618_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4602_);
v___x_4662_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v___x_4667_, lean_object* v_x_4668_, lean_object* v___y_4669_){
_start:
{
uint8_t v_a_11719__boxed_4670_; uint8_t v___x_11721__boxed_4671_; lean_object* v_res_4672_; 
v_a_11719__boxed_4670_ = lean_unbox(v_a_4664_);
v___x_11721__boxed_4671_ = lean_unbox(v___x_4667_);
v_res_4672_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_11719__boxed_4670_, v_a_4665_, v_a_4666_, v___x_11721__boxed_4671_, v_x_4668_);
lean_dec(v_a_4666_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4673_, lean_object* v_next_4674_, lean_object* v_a_4675_, lean_object* v_x_4676_){
_start:
{
if (lean_obj_tag(v_x_4676_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4686_; 
lean_dec(v_next_4674_);
lean_dec_ref(v_a_4673_);
v_a_4678_ = lean_ctor_get(v_x_4676_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_x_4676_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4680_ = v_x_4676_;
v_isShared_4681_ = v_isSharedCheck_4686_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v_x_4676_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4686_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
lean_object* v___x_4684_; 
v___x_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4683_);
return v___x_4684_;
}
}
}
else
{
lean_object* v_a_4687_; uint8_t v___x_4688_; 
v_a_4687_ = lean_ctor_get(v_x_4676_, 0);
lean_inc(v_a_4687_);
lean_dec_ref(v_x_4676_);
v___x_4688_ = lean_unbox(v_a_4687_);
if (v___x_4688_ == 0)
{
lean_object* v_capacity_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___f_4694_; lean_object* v___f_4695_; lean_object* v___x_4696_; uint8_t v___x_4697_; lean_object* v___x_4698_; 
v_capacity_4689_ = lean_ctor_get(v_a_4673_, 2);
v___x_4690_ = lean_nat_mod(v_next_4674_, v_capacity_4689_);
v___x_4691_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4690_, v_a_4675_);
v___x_4692_ = 1;
v___x_4693_ = lean_box(v___x_4692_);
lean_inc(v_a_4675_);
lean_inc_n(v_a_4687_, 2);
v___f_4694_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4694_, 0, v_a_4687_);
lean_closure_set(v___f_4694_, 1, v_a_4673_);
lean_closure_set(v___f_4694_, 2, v_a_4675_);
lean_closure_set(v___f_4694_, 3, v___x_4693_);
v___f_4695_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4695_, 0, v_next_4674_);
lean_closure_set(v___f_4695_, 1, v_a_4687_);
lean_closure_set(v___f_4695_, 2, v___f_4694_);
v___x_4696_ = lean_unsigned_to_nat(0u);
v___x_4697_ = lean_unbox(v_a_4687_);
lean_dec(v_a_4687_);
v___x_4698_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4696_, v___x_4697_, v___x_4691_, v___f_4695_);
return v___x_4698_;
}
else
{
lean_object* v___x_4699_; 
lean_dec(v_a_4687_);
lean_dec(v_next_4674_);
lean_dec_ref(v_a_4673_);
v___x_4699_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4700_, lean_object* v_next_4701_, lean_object* v_a_4702_, lean_object* v_x_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4700_, v_next_4701_, v_a_4702_, v_x_4703_);
lean_dec(v_a_4702_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4706_, lean_object* v_next_4707_, lean_object* v_x_4708_){
_start:
{
if (lean_obj_tag(v_x_4708_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4718_; 
lean_dec(v_next_4707_);
v_a_4710_ = lean_ctor_get(v_x_4708_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v_x_4708_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4712_ = v_x_4708_;
v_isShared_4713_ = v_isSharedCheck_4718_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v_x_4708_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4718_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
lean_object* v___x_4716_; 
v___x_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
return v___x_4716_;
}
}
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4720_; lean_object* v___f_4721_; lean_object* v___x_4722_; uint8_t v___x_4723_; lean_object* v___x_4724_; 
v_a_4719_ = lean_ctor_get(v_x_4708_, 0);
lean_inc(v_a_4719_);
lean_dec_ref(v_x_4708_);
v___x_4720_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4706_);
lean_inc(v_a_4706_);
v___f_4721_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4721_, 0, v_a_4719_);
lean_closure_set(v___f_4721_, 1, v_next_4707_);
lean_closure_set(v___f_4721_, 2, v_a_4706_);
v___x_4722_ = lean_unsigned_to_nat(0u);
v___x_4723_ = 0;
v___x_4724_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4722_, v___x_4723_, v___x_4720_, v___f_4721_);
return v___x_4724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4725_, lean_object* v_next_4726_, lean_object* v_x_4727_, lean_object* v___y_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4725_, v_next_4726_, v_x_4727_);
lean_dec(v_a_4725_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v___x_4733_; lean_object* v___f_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; uint8_t v___x_4738_; lean_object* v___x_4739_; 
v___x_4733_ = lean_st_ref_get(v_a_4731_);
lean_inc(v_a_4731_);
v___f_4734_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4734_, 0, v_a_4731_);
lean_closure_set(v___f_4734_, 1, v_next_4730_);
v___x_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4733_);
v___x_4736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4735_);
v___x_4737_ = lean_unsigned_to_nat(0u);
v___x_4738_ = 0;
v___x_4739_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4737_, v___x_4738_, v___x_4736_, v___f_4734_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4740_, lean_object* v_a_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v_res_4743_; 
v_res_4743_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4740_, v_a_4741_);
lean_dec(v_a_4741_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4744_, lean_object* v_a_4745_, lean_object* v_x_4746_){
_start:
{
if (lean_obj_tag(v_x_4746_) == 0)
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4756_; 
lean_dec(v_receiverId_4744_);
v_a_4748_ = lean_ctor_get(v_x_4746_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_x_4746_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4750_ = v_x_4746_;
v_isShared_4751_ = v_isSharedCheck_4756_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v_x_4746_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4756_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
lean_object* v___x_4754_; 
v___x_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4754_, 0, v___x_4753_);
return v___x_4754_;
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v_receivers_4758_; lean_object* v___x_4759_; 
v_a_4757_ = lean_ctor_get(v_x_4746_, 0);
lean_inc(v_a_4757_);
lean_dec_ref(v_x_4746_);
v_receivers_4758_ = lean_ctor_get(v_a_4757_, 7);
lean_inc(v_receivers_4758_);
lean_dec(v_a_4757_);
v___x_4759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4758_, v_receiverId_4744_);
if (lean_obj_tag(v___x_4759_) == 1)
{
lean_object* v_val_4760_; lean_object* v___x_4761_; lean_object* v___f_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; lean_object* v___x_4765_; 
v_val_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_val_4760_);
lean_dec_ref(v___x_4759_);
v___x_4761_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4760_, v_a_4745_);
lean_inc(v_a_4745_);
v___f_4762_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4762_, 0, v_a_4745_);
lean_closure_set(v___f_4762_, 1, v_receiverId_4744_);
lean_closure_set(v___f_4762_, 2, v_receivers_4758_);
v___x_4763_ = lean_unsigned_to_nat(0u);
v___x_4764_ = 0;
v___x_4765_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4763_, v___x_4764_, v___x_4761_, v___f_4762_);
return v___x_4765_;
}
else
{
lean_object* v___x_4766_; 
lean_dec(v___x_4759_);
lean_dec(v_receivers_4758_);
lean_dec(v_receiverId_4744_);
v___x_4766_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4767_, lean_object* v_a_4768_, lean_object* v_x_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4767_, v_a_4768_, v_x_4769_);
lean_dec(v_a_4768_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v___x_4775_; lean_object* v___f_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; uint8_t v___x_4780_; lean_object* v___x_4781_; 
v___x_4775_ = lean_st_ref_get(v_a_4773_);
lean_inc(v_a_4773_);
v___f_4776_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4776_, 0, v_receiverId_4772_);
lean_closure_set(v___f_4776_, 1, v_a_4773_);
v___x_4777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4775_);
v___x_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4777_);
v___x_4779_ = lean_unsigned_to_nat(0u);
v___x_4780_ = 0;
v___x_4781_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4779_, v___x_4780_, v___x_4778_, v___f_4776_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4782_, lean_object* v_a_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4782_, v_a_4783_);
lean_dec(v_a_4783_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4790_, lean_object* v___y_4791_, lean_object* v___f_4792_, lean_object* v_x_4793_){
_start:
{
if (lean_obj_tag(v_x_4793_) == 0)
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4803_; 
lean_dec_ref(v___f_4792_);
lean_dec(v_id_4790_);
v_a_4795_ = lean_ctor_get(v_x_4793_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v_x_4793_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4797_ = v_x_4793_;
v_isShared_4798_ = v_isSharedCheck_4803_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v_x_4793_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4803_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4801_; 
v___x_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4800_);
return v___x_4801_;
}
}
}
else
{
lean_object* v_a_4804_; uint8_t v___x_4805_; 
v_a_4804_ = lean_ctor_get(v_x_4793_, 0);
lean_inc(v_a_4804_);
lean_dec_ref(v_x_4793_);
v___x_4805_ = lean_unbox(v_a_4804_);
lean_dec(v_a_4804_);
if (v___x_4805_ == 0)
{
lean_object* v___x_4806_; 
lean_dec_ref(v___f_4792_);
lean_dec(v_id_4790_);
v___x_4806_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1));
return v___x_4806_;
}
else
{
lean_object* v___x_4807_; lean_object* v___x_4808_; uint8_t v___x_4809_; lean_object* v___x_4810_; 
v___x_4807_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4790_, v___y_4791_);
v___x_4808_ = lean_unsigned_to_nat(0u);
v___x_4809_ = 0;
v___x_4810_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4808_, v___x_4809_, v___x_4807_, v___f_4792_);
return v___x_4810_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4811_, lean_object* v___y_4812_, lean_object* v___f_4813_, lean_object* v_x_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4811_, v___y_4812_, v___f_4813_, v_x_4814_);
lean_dec(v___y_4812_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4817_, lean_object* v___f_4818_, lean_object* v___y_4819_){
_start:
{
lean_object* v___x_4821_; lean_object* v___f_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; uint8_t v___x_4826_; lean_object* v___x_4827_; lean_object* v___f_4828_; lean_object* v___x_4829_; 
v___x_4821_ = lean_st_ref_get(v___y_4819_);
lean_inc_n(v___y_4819_, 2);
lean_inc(v_id_4817_);
v___f_4822_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_4822_, 0, v_id_4817_);
lean_closure_set(v___f_4822_, 1, v___y_4819_);
v___x_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4821_);
v___x_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4823_);
v___x_4825_ = lean_unsigned_to_nat(0u);
v___x_4826_ = 0;
v___x_4827_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4825_, v___x_4826_, v___x_4824_, v___f_4822_);
v___f_4828_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4828_, 0, v_id_4817_);
lean_closure_set(v___f_4828_, 1, v___y_4819_);
lean_closure_set(v___f_4828_, 2, v___f_4818_);
v___x_4829_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4825_, v___x_4826_, v___x_4827_, v___f_4828_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4830_, lean_object* v___f_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4830_, v___f_4831_, v___y_4832_);
lean_dec(v___y_4832_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4837_){
_start:
{
lean_object* v_state_4838_; lean_object* v_id_4839_; lean_object* v___f_4840_; lean_object* v___f_4841_; lean_object* v___f_4842_; lean_object* v___f_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v_state_4838_ = lean_ctor_get(v_ch_4837_, 0);
lean_inc_ref_n(v_state_4838_, 2);
v_id_4839_ = lean_ctor_get(v_ch_4837_, 1);
lean_inc(v_id_4839_);
v___f_4840_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4841_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4841_, 0, v_ch_4837_);
v___f_4842_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4843_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4843_, 0, v_id_4839_);
lean_closure_set(v___f_4843_, 1, v___f_4842_);
v___x_4844_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4844_, 0, lean_box(0));
lean_closure_set(v___x_4844_, 1, lean_box(0));
lean_closure_set(v___x_4844_, 2, v_state_4838_);
lean_closure_set(v___x_4844_, 3, v___f_4843_);
v___x_4845_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4845_, 0, lean_box(0));
lean_closure_set(v___x_4845_, 1, lean_box(0));
lean_closure_set(v___x_4845_, 2, v_state_4838_);
lean_closure_set(v___x_4845_, 3, v___f_4840_);
v___x_4846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4844_);
lean_ctor_set(v___x_4846_, 1, v___f_4841_);
lean_ctor_set(v___x_4846_, 2, v___x_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4847_, lean_object* v_ch_4848_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4850_, lean_object* v_receiverId_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v___x_4854_; 
v___x_4854_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4851_, v_a_4852_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4855_, lean_object* v_receiverId_4856_, lean_object* v_a_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4855_, v_receiverId_4856_, v_a_4857_);
lean_dec(v_a_4857_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4860_, lean_object* v_q_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v___x_4864_; 
v___x_4864_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4861_, v___y_4862_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4865_, lean_object* v_q_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4865_, v_q_4866_, v___y_4867_);
lean_dec(v___y_4867_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4870_, lean_object* v_slot_4871_, lean_object* v_next_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v___x_4875_; 
v___x_4875_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4871_, v_next_4872_);
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4876_, lean_object* v_slot_4877_, lean_object* v_next_4878_, lean_object* v_a_4879_, lean_object* v___y_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4876_, v_slot_4877_, v_next_4878_, v_a_4879_);
lean_dec(v_a_4879_);
lean_dec(v_next_4878_);
lean_dec(v_slot_4877_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4883_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4886_, lean_object* v_a_4887_, lean_object* v___y_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4886_, v_a_4887_);
lean_dec(v_a_4887_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4890_, lean_object* v_next_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v___x_4894_; 
v___x_4894_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4891_, v_a_4892_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4895_, lean_object* v_next_4896_, lean_object* v_a_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4895_, v_next_4896_, v_a_4897_);
lean_dec(v_a_4897_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4900_, lean_object* v_x_4901_, lean_object* v_x_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v___x_4905_; 
v___x_4905_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4901_, v_x_4902_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4906_, lean_object* v_x_4907_, lean_object* v_x_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4906_, v_x_4907_, v_x_4908_, v___y_4909_);
lean_dec(v___y_4909_);
return v_res_4911_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4913_){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4913_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4916_, lean_object* v_a_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Std_Broadcast_new___redArg(v_capacity_4916_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4919_, lean_object* v_capacity_4920_, lean_object* v_h_4921_){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4920_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4924_, lean_object* v_capacity_4925_, lean_object* v_h_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v_res_4928_; 
v_res_4928_ = l_Std_Broadcast_new(v_00_u03b1_4924_, v_capacity_4925_, v_h_4926_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4929_, lean_object* v_v_4930_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4929_, v_v_4930_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4933_, lean_object* v_v_4934_, lean_object* v_a_4935_){
_start:
{
lean_object* v_res_4936_; 
v_res_4936_ = l_Std_Broadcast_trySend___redArg(v_ch_4933_, v_v_4934_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4937_, lean_object* v_ch_4938_, lean_object* v_v_4939_){
_start:
{
lean_object* v___x_4941_; 
v___x_4941_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4938_, v_v_4939_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4942_, lean_object* v_ch_4943_, lean_object* v_v_4944_, lean_object* v_a_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Std_Broadcast_trySend(v_00_u03b1_4942_, v_ch_4943_, v_v_4944_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4947_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4949_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4949_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
else
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
v_a_4958_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4949_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4949_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Std_Broadcast_subscribe___redArg(v_ch_4966_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_4969_, lean_object* v_ch_4970_){
_start:
{
lean_object* v___x_4972_; 
v___x_4972_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4970_);
if (lean_obj_tag(v___x_4972_) == 0)
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4975_ = v___x_4972_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4972_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
v_a_4981_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4972_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4972_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_4989_, lean_object* v_ch_4990_, lean_object* v_a_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Std_Broadcast_subscribe(v_00_u03b1_4989_, v_ch_4990_);
return v_res_4992_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_4993_){
_start:
{
lean_object* v___x_4995_; 
v___x_4995_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_4993_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5003_; 
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4998_ = v___x_4995_;
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4995_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4999_ == 0)
{
v___x_5001_ = v___x_4998_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4996_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5021_; 
v_a_5004_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5006_ = v___x_4995_;
v_isShared_5007_ = v_isSharedCheck_5021_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_4995_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5021_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
uint8_t v___x_5008_; 
v___x_5008_ = lean_unbox(v_a_5004_);
lean_dec(v_a_5004_);
switch(v___x_5008_)
{
case 0:
{
lean_object* v___x_5009_; lean_object* v___x_5011_; 
v___x_5009_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 0, v___x_5009_);
v___x_5011_ = v___x_5006_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_5009_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
case 1:
{
lean_object* v___x_5013_; lean_object* v___x_5015_; 
v___x_5013_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 0, v___x_5013_);
v___x_5015_ = v___x_5006_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
default: 
{
lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5017_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5007_ == 0)
{
lean_ctor_set(v___x_5006_, 0, v___x_5017_);
v___x_5019_ = v___x_5006_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5022_, lean_object* v_a_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Std_Broadcast_close___redArg(v_ch_5022_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5025_, lean_object* v_ch_5026_){
_start:
{
lean_object* v___x_5028_; 
v___x_5028_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5026_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_5028_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5028_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
else
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5054_; 
v_a_5037_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5039_ = v___x_5028_;
v_isShared_5040_ = v_isSharedCheck_5054_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5028_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5054_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
uint8_t v___x_5041_; 
v___x_5041_ = lean_unbox(v_a_5037_);
lean_dec(v_a_5037_);
switch(v___x_5041_)
{
case 0:
{
lean_object* v___x_5042_; lean_object* v___x_5044_; 
v___x_5042_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5040_ == 0)
{
lean_ctor_set(v___x_5039_, 0, v___x_5042_);
v___x_5044_ = v___x_5039_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v___x_5042_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
case 1:
{
lean_object* v___x_5046_; lean_object* v___x_5048_; 
v___x_5046_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5040_ == 0)
{
lean_ctor_set(v___x_5039_, 0, v___x_5046_);
v___x_5048_ = v___x_5039_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5046_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
default: 
{
lean_object* v___x_5050_; lean_object* v___x_5052_; 
v___x_5050_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5040_ == 0)
{
lean_ctor_set(v___x_5039_, 0, v___x_5050_);
v___x_5052_ = v___x_5039_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5050_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5055_, lean_object* v_ch_5056_, lean_object* v_a_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l_Std_Broadcast_close(v_00_u03b1_5055_, v_ch_5056_);
return v_res_5058_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5059_){
_start:
{
lean_object* v___y_5062_; 
if (lean_obj_tag(v_x_5059_) == 0)
{
lean_object* v_a_5066_; uint8_t v___x_5067_; 
v_a_5066_ = lean_ctor_get(v_x_5059_, 0);
lean_inc(v_a_5066_);
lean_dec_ref(v_x_5059_);
v___x_5067_ = lean_unbox(v_a_5066_);
lean_dec(v_a_5066_);
switch(v___x_5067_)
{
case 0:
{
lean_object* v___x_5068_; 
v___x_5068_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5062_ = v___x_5068_;
goto v___jp_5061_;
}
case 1:
{
lean_object* v___x_5069_; 
v___x_5069_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5062_ = v___x_5069_;
goto v___jp_5061_;
}
default: 
{
lean_object* v___x_5070_; 
v___x_5070_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5062_ = v___x_5070_;
goto v___jp_5061_;
}
}
}
else
{
lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5079_; 
v_a_5071_ = lean_ctor_get(v_x_5059_, 0);
v_isSharedCheck_5079_ = !lean_is_exclusive(v_x_5059_);
if (v_isSharedCheck_5079_ == 0)
{
v___x_5073_ = v_x_5059_;
v_isShared_5074_ = v_isSharedCheck_5079_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v_x_5059_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5079_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5076_; 
if (v_isShared_5074_ == 0)
{
v___x_5076_ = v___x_5073_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5078_; 
v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5071_);
v___x_5076_ = v_reuseFailAlloc_5078_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5077_; 
v___x_5077_ = lean_task_pure(v___x_5076_);
return v___x_5077_;
}
}
}
v___jp_5061_:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
lean_inc_ref(v___y_5062_);
v___x_5063_ = lean_mk_io_user_error(v___y_5062_);
v___x_5064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
v___x_5065_ = lean_task_pure(v___x_5064_);
return v___x_5065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5080_, lean_object* v___y_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5080_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5084_, lean_object* v_v_5085_){
_start:
{
lean_object* v___x_5087_; lean_object* v___f_5088_; lean_object* v___x_5089_; uint8_t v___x_5090_; lean_object* v___x_5091_; 
v___x_5087_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5084_, v_v_5085_);
v___f_5088_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5089_ = lean_unsigned_to_nat(0u);
v___x_5090_ = 1;
v___x_5091_ = lean_io_bind_task(v___x_5087_, v___f_5088_, v___x_5089_, v___x_5090_);
return v___x_5091_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5092_, lean_object* v_v_5093_, lean_object* v_a_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_Std_Broadcast_send___redArg(v_ch_5092_, v_v_5093_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5096_, lean_object* v_ch_5097_, lean_object* v_v_5098_){
_start:
{
lean_object* v___x_5100_; lean_object* v___f_5101_; lean_object* v___x_5102_; uint8_t v___x_5103_; lean_object* v___x_5104_; 
v___x_5100_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5097_, v_v_5098_);
v___f_5101_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5102_ = lean_unsigned_to_nat(0u);
v___x_5103_ = 1;
v___x_5104_ = lean_io_bind_task(v___x_5100_, v___f_5101_, v___x_5102_, v___x_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5105_, lean_object* v_ch_5106_, lean_object* v_v_5107_, lean_object* v_a_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l_Std_Broadcast_send(v_00_u03b1_5105_, v_ch_5106_, v_v_5107_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5110_){
_start:
{
lean_object* v___x_5112_; 
v___x_5112_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5110_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5113_, lean_object* v_a_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5113_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5116_, lean_object* v_ch_5117_){
_start:
{
lean_object* v___x_5119_; 
v___x_5119_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5117_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5120_, lean_object* v_ch_5121_, lean_object* v_a_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5120_, v_ch_5121_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5124_){
_start:
{
lean_object* v___x_5126_; 
v___x_5126_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5124_);
return v___x_5126_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v_res_5129_; 
v_res_5129_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5127_);
return v_res_5129_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5130_, lean_object* v_inst_5131_, lean_object* v_ch_5132_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5132_);
return v___x_5134_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5135_, lean_object* v_inst_5136_, lean_object* v_ch_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5135_, v_inst_5136_, v_ch_5137_);
lean_dec(v_inst_5136_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5140_){
_start:
{
lean_object* v___x_5141_; 
v___x_5141_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5140_);
return v___x_5141_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5142_, lean_object* v_inst_5143_, lean_object* v_ch_5144_){
_start:
{
lean_object* v___x_5145_; 
v___x_5145_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5144_);
return v___x_5145_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5146_, lean_object* v_inst_5147_, lean_object* v_ch_5148_){
_start:
{
lean_object* v_res_5149_; 
v_res_5149_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5146_, v_inst_5147_, v_ch_5148_);
lean_dec(v_inst_5147_);
return v_res_5149_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5150_){
_start:
{
lean_object* v___x_5152_; 
v___x_5152_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5150_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5153_, lean_object* v_a_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5153_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5156_, lean_object* v_ch_5157_){
_start:
{
lean_object* v___x_5159_; 
v___x_5159_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5157_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5160_, lean_object* v_ch_5161_, lean_object* v_a_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5160_, v_ch_5161_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5164_, lean_object* v_ch_5165_, lean_object* v_prio_5166_){
_start:
{
lean_object* v___x_5168_; 
v___x_5168_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5164_, v_ch_5165_, v_prio_5166_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5169_, lean_object* v_ch_5170_, lean_object* v_prio_5171_, lean_object* v_a_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5169_, v_ch_5170_, v_prio_5171_);
return v_res_5173_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5174_, lean_object* v_f_5175_, lean_object* v_ch_5176_, lean_object* v_prio_5177_){
_start:
{
lean_object* v___x_5179_; 
v___x_5179_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5175_, v_ch_5176_, v_prio_5177_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5180_, lean_object* v_f_5181_, lean_object* v_ch_5182_, lean_object* v_prio_5183_, lean_object* v_a_5184_){
_start:
{
lean_object* v_res_5185_; 
v_res_5185_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5180_, v_f_5181_, v_ch_5182_, v_prio_5183_);
return v_res_5185_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5191_, lean_object* v_inst_5192_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5194_, lean_object* v_inst_5195_){
_start:
{
lean_object* v_res_5196_; 
v_res_5196_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5194_, v_inst_5195_);
lean_dec(v_inst_5195_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_5197_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5198_, 0, v_a_5197_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_5199_, lean_object* v_x_5200_){
_start:
{
if (lean_obj_tag(v_x_5200_) == 0)
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5210_; 
lean_dec_ref(v___f_5199_);
v_a_5202_ = lean_ctor_get(v_x_5200_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v_x_5200_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5204_ = v_x_5200_;
v_isShared_5205_ = v_isSharedCheck_5210_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v_x_5200_);
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
lean_object* v_a_5211_; 
v_a_5211_ = lean_ctor_get(v_x_5200_, 0);
lean_inc(v_a_5211_);
lean_dec_ref(v_x_5200_);
if (lean_obj_tag(v_a_5211_) == 0)
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5220_; 
lean_dec_ref(v___f_5199_);
v_a_5212_ = lean_ctor_get(v_a_5211_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v_a_5211_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5214_ = v_a_5211_;
v_isShared_5215_ = v_isSharedCheck_5220_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v_a_5211_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5220_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5217_; 
if (v_isShared_5215_ == 0)
{
v___x_5217_ = v___x_5214_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5212_);
v___x_5217_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
lean_object* v___x_5218_; 
v___x_5218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5218_, 0, v___x_5217_);
return v___x_5218_;
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5222_; uint8_t v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v_a_5221_ = lean_ctor_get(v_a_5211_, 0);
lean_inc(v_a_5221_);
lean_dec_ref(v_a_5211_);
v___x_5222_ = lean_unsigned_to_nat(0u);
v___x_5223_ = 0;
v___x_5224_ = lean_task_map(v___f_5199_, v_a_5221_, v___x_5222_, v___x_5223_);
v___x_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5224_);
return v___x_5225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_5226_, lean_object* v_x_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(v___f_5226_, v_x_5227_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_5230_, lean_object* v_receiver_5231_){
_start:
{
lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; uint8_t v___x_5238_; lean_object* v___x_5239_; 
v___x_5233_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5231_);
v___x_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5233_);
v___x_5235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5234_);
v___x_5236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5235_);
v___x_5237_ = lean_unsigned_to_nat(0u);
v___x_5238_ = 0;
v___x_5239_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5237_, v___x_5238_, v___x_5236_, v___f_5230_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_5240_, lean_object* v_receiver_5241_, lean_object* v___y_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(v___f_5240_, v_receiver_5241_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5249_, lean_object* v_inst_5250_){
_start:
{
lean_object* v___f_5251_; 
v___f_5251_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2));
return v___f_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5252_, lean_object* v_inst_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5252_, v_inst_5253_);
lean_dec(v_inst_5253_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__1(lean_object* v_a_5255_){
_start:
{
lean_object* v___x_5256_; 
v___x_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5256_, 0, v_a_5255_);
return v___x_5256_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_5261_, lean_object* v_x_5262_){
_start:
{
if (lean_obj_tag(v_x_5262_) == 0)
{
lean_object* v_a_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5272_; 
lean_dec_ref(v___f_5261_);
v_a_5264_ = lean_ctor_get(v_x_5262_, 0);
v_isSharedCheck_5272_ = !lean_is_exclusive(v_x_5262_);
if (v_isSharedCheck_5272_ == 0)
{
v___x_5266_ = v_x_5262_;
v_isShared_5267_ = v_isSharedCheck_5272_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_a_5264_);
lean_dec(v_x_5262_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5272_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5269_; 
if (v_isShared_5267_ == 0)
{
v___x_5269_ = v___x_5266_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_a_5264_);
v___x_5269_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
lean_object* v___x_5270_; 
v___x_5270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5270_, 0, v___x_5269_);
return v___x_5270_;
}
}
}
else
{
lean_object* v_a_5273_; lean_object* v___x_5274_; uint8_t v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v_a_5273_ = lean_ctor_get(v_x_5262_, 0);
lean_inc(v_a_5273_);
lean_dec_ref(v_x_5262_);
v___x_5274_ = lean_unsigned_to_nat(0u);
v___x_5275_ = 0;
v___x_5276_ = lean_task_map(v___f_5261_, v_a_5273_, v___x_5274_, v___x_5275_);
v___x_5277_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1));
v___x_5278_ = lean_task_map(v___x_5277_, v___x_5276_, v___x_5274_, v___x_5275_);
v___x_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
return v___x_5279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_5280_, lean_object* v_x_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(v___f_5280_, v_x_5281_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5284_, lean_object* v___f_5285_, lean_object* v_receiver_5286_, lean_object* v_x_5287_){
_start:
{
lean_object* v___x_5289_; lean_object* v___x_5290_; uint8_t v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; lean_object* v___x_5296_; 
v___x_5289_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5286_, v_x_5287_);
v___x_5290_ = lean_unsigned_to_nat(0u);
v___x_5291_ = 1;
v___x_5292_ = lean_io_bind_task(v___x_5289_, v___f_5284_, v___x_5290_, v___x_5291_);
v___x_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
v___x_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
v___x_5295_ = 0;
v___x_5296_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5290_, v___x_5295_, v___x_5294_, v___f_5285_);
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5297_, lean_object* v___f_5298_, lean_object* v_receiver_5299_, lean_object* v_x_5300_, lean_object* v___y_5301_){
_start:
{
lean_object* v_res_5302_; 
v_res_5302_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(v___f_5297_, v___f_5298_, v_receiver_5299_, v_x_5300_);
return v_res_5302_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(lean_object* v_x_5303_){
_start:
{
lean_object* v___x_5305_; 
v___x_5305_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5305_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v_x_5306_, lean_object* v___y_5307_){
_start:
{
lean_object* v_res_5308_; 
v_res_5308_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(v_x_5306_);
lean_dec_ref(v_x_5306_);
return v_res_5308_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_5309_, lean_object* v_socket_5310_, lean_object* v_x_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = lean_apply_3(v___f_5309_, v_socket_5310_, v___y_5312_, lean_box(0));
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_5315_, lean_object* v_socket_5316_, lean_object* v_x_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(v___f_5315_, v_socket_5316_, v_x_5317_, v___y_5318_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(lean_object* v___f_5321_, lean_object* v___x_5322_, lean_object* v_socket_5323_, lean_object* v_data_5324_){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; uint8_t v___x_5329_; 
v___x_5326_ = lean_unsigned_to_nat(0u);
v___x_5327_ = lean_array_get_size(v_data_5324_);
v___x_5328_ = lean_box(0);
v___x_5329_ = lean_nat_dec_lt(v___x_5326_, v___x_5327_);
if (v___x_5329_ == 0)
{
lean_object* v___x_5330_; 
lean_dec_ref(v_data_5324_);
lean_dec_ref(v_socket_5323_);
lean_dec_ref(v___x_5322_);
lean_dec_ref(v___f_5321_);
v___x_5330_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5330_;
}
else
{
lean_object* v___f_5331_; uint8_t v___x_5332_; 
v___f_5331_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5331_, 0, v___f_5321_);
lean_closure_set(v___f_5331_, 1, v_socket_5323_);
v___x_5332_ = lean_nat_dec_le(v___x_5327_, v___x_5327_);
if (v___x_5332_ == 0)
{
if (v___x_5329_ == 0)
{
lean_object* v___x_5333_; 
lean_dec_ref(v___f_5331_);
lean_dec_ref(v_data_5324_);
lean_dec_ref(v___x_5322_);
v___x_5333_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5333_;
}
else
{
size_t v___x_5334_; size_t v___x_5335_; lean_object* v___x_857__overap_5336_; lean_object* v___x_5337_; 
v___x_5334_ = ((size_t)0ULL);
v___x_5335_ = lean_usize_of_nat(v___x_5327_);
v___x_857__overap_5336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5322_, v___f_5331_, v_data_5324_, v___x_5334_, v___x_5335_, v___x_5328_);
v___x_5337_ = lean_apply_1(v___x_857__overap_5336_, lean_box(0));
return v___x_5337_;
}
}
else
{
size_t v___x_5338_; size_t v___x_5339_; lean_object* v___x_860__overap_5340_; lean_object* v___x_5341_; 
v___x_5338_ = ((size_t)0ULL);
v___x_5339_ = lean_usize_of_nat(v___x_5327_);
v___x_860__overap_5340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5322_, v___f_5331_, v_data_5324_, v___x_5338_, v___x_5339_, v___x_5328_);
v___x_5341_ = lean_apply_1(v___x_860__overap_5340_, lean_box(0));
return v___x_5341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed(lean_object* v___f_5342_, lean_object* v___x_5343_, lean_object* v_socket_5344_, lean_object* v_data_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(v___f_5342_, v___x_5343_, v_socket_5344_, v_data_5345_);
return v_res_5347_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_5355_; 
v___x_5355_ = l_Std_Internal_IO_Async_EAsync_instMonad(lean_box(0));
return v___x_5355_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___x_5356_; lean_object* v___f_5357_; lean_object* v___f_5358_; 
v___x_5356_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4);
v___f_5357_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___f_5358_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed), 5, 2);
lean_closure_set(v___f_5358_, 0, v___f_5357_);
lean_closure_set(v___f_5358_, 1, v___x_5356_);
return v___f_5358_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6(void){
_start:
{
lean_object* v___f_5359_; lean_object* v___f_5360_; lean_object* v___f_5361_; lean_object* v___x_5362_; 
v___f_5359_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3));
v___f_5360_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5);
v___f_5361_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___x_5362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5362_, 0, v___f_5361_);
lean_ctor_set(v___x_5362_, 1, v___f_5360_);
lean_ctor_set(v___x_5362_, 2, v___f_5359_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5363_, lean_object* v_inst_5364_){
_start:
{
lean_object* v___x_5365_; 
v___x_5365_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6);
return v___x_5365_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5366_, lean_object* v_inst_5367_){
_start:
{
lean_object* v_res_5368_; 
v_res_5368_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5366_, v_inst_5367_);
lean_dec(v_inst_5367_);
return v_res_5368_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5369_; 
v___x_5369_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5369_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5370_){
_start:
{
lean_object* v___x_5372_; 
v___x_5372_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5370_);
return v___x_5372_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5373_, lean_object* v_a_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5373_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5376_, lean_object* v_capacity_5377_, lean_object* v_h_5378_){
_start:
{
lean_object* v___x_5380_; 
v___x_5380_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5377_);
return v___x_5380_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5381_, lean_object* v_capacity_5382_, lean_object* v_h_5383_, lean_object* v_a_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5381_, v_capacity_5382_, v_h_5383_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5386_, lean_object* v_v_5387_){
_start:
{
lean_object* v___x_5389_; 
v___x_5389_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5386_, v_v_5387_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5390_, lean_object* v_v_5391_, lean_object* v_a_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5390_, v_v_5391_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5394_, lean_object* v_ch_5395_, lean_object* v_v_5396_){
_start:
{
lean_object* v___x_5398_; 
v___x_5398_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5395_, v_v_5396_);
return v___x_5398_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5399_, lean_object* v_ch_5400_, lean_object* v_v_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5399_, v_ch_5400_, v_v_5401_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5405_, lean_object* v_v_5406_){
_start:
{
lean_object* v___x_5408_; lean_object* v___f_5409_; lean_object* v___x_5410_; uint8_t v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; 
v___x_5408_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5405_, v_v_5406_);
v___f_5409_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5410_ = lean_unsigned_to_nat(0u);
v___x_5411_ = 1;
v___x_5412_ = lean_io_bind_task(v___x_5408_, v___f_5409_, v___x_5410_, v___x_5411_);
v___x_5413_ = lean_io_wait(v___x_5412_);
v___x_5414_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5415_ = l_IO_ofExcept___redArg(v___x_5414_, v___x_5413_);
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5416_, lean_object* v_v_5417_, lean_object* v_a_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5416_, v_v_5417_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5420_, lean_object* v_ch_5421_, lean_object* v_v_5422_){
_start:
{
lean_object* v___x_5424_; lean_object* v___f_5425_; lean_object* v___x_5426_; uint8_t v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5424_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5421_, v_v_5422_);
v___f_5425_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5426_ = lean_unsigned_to_nat(0u);
v___x_5427_ = 1;
v___x_5428_ = lean_io_bind_task(v___x_5424_, v___f_5425_, v___x_5426_, v___x_5427_);
v___x_5429_ = lean_io_wait(v___x_5428_);
v___x_5430_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5431_ = l_IO_ofExcept___redArg(v___x_5430_, v___x_5429_);
return v___x_5431_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5432_, lean_object* v_ch_5433_, lean_object* v_v_5434_, lean_object* v_a_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5432_, v_ch_5433_, v_v_5434_);
return v_res_5436_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5437_){
_start:
{
lean_object* v___x_5439_; 
v___x_5439_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5437_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5440_, lean_object* v_a_5441_){
_start:
{
lean_object* v_res_5442_; 
v_res_5442_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5440_);
return v_res_5442_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5443_, lean_object* v_ch_5444_){
_start:
{
lean_object* v___x_5446_; 
v___x_5446_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5444_);
return v___x_5446_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5447_, lean_object* v_ch_5448_, lean_object* v_a_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5447_, v_ch_5448_);
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5451_){
_start:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; 
v___x_5453_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5451_);
v___x_5454_ = lean_io_wait(v___x_5453_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5455_, lean_object* v_a_5456_){
_start:
{
lean_object* v_res_5457_; 
v_res_5457_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5455_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5458_, lean_object* v_inst_5459_, lean_object* v_ch_5460_){
_start:
{
lean_object* v___x_5462_; 
v___x_5462_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5460_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5463_, lean_object* v_inst_5464_, lean_object* v_ch_5465_, lean_object* v_a_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5463_, v_inst_5464_, v_ch_5465_);
lean_dec(v_inst_5464_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5468_, lean_object* v_b_5469_, lean_object* v_f_5470_, lean_object* v_toBind_5471_, lean_object* v___f_5472_, lean_object* v_a_5473_){
_start:
{
if (lean_obj_tag(v_a_5473_) == 0)
{
lean_object* v___x_5474_; 
lean_dec(v___f_5472_);
lean_dec(v_toBind_5471_);
lean_dec(v_f_5470_);
v___x_5474_ = lean_apply_2(v_toPure_5468_, lean_box(0), v_b_5469_);
return v___x_5474_;
}
else
{
lean_object* v_val_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; 
lean_dec(v_toPure_5468_);
v_val_5475_ = lean_ctor_get(v_a_5473_, 0);
lean_inc(v_val_5475_);
lean_dec_ref(v_a_5473_);
v___x_5476_ = lean_apply_2(v_f_5470_, v_val_5475_, v_b_5469_);
v___x_5477_ = lean_apply_4(v_toBind_5471_, lean_box(0), lean_box(0), v___x_5476_, v___f_5472_);
return v___x_5477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5478_, lean_object* v_inst_5479_, lean_object* v_inst_5480_, lean_object* v_ch_5481_, lean_object* v_f_5482_, lean_object* v_b_5483_){
_start:
{
lean_object* v_toApplicative_5484_; lean_object* v_toBind_5485_; lean_object* v_toPure_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___f_5489_; lean_object* v___f_5490_; lean_object* v___x_5491_; 
v_toApplicative_5484_ = lean_ctor_get(v_inst_5479_, 0);
v_toBind_5485_ = lean_ctor_get(v_inst_5479_, 1);
lean_inc_n(v_toBind_5485_, 2);
v_toPure_5486_ = lean_ctor_get(v_toApplicative_5484_, 1);
lean_inc_n(v_toPure_5486_, 2);
lean_inc_ref(v_ch_5481_);
lean_inc(v_inst_5478_);
v___x_5487_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5487_, 0, lean_box(0));
lean_closure_set(v___x_5487_, 1, v_inst_5478_);
lean_closure_set(v___x_5487_, 2, v_ch_5481_);
lean_inc(v_inst_5480_);
v___x_5488_ = lean_apply_2(v_inst_5480_, lean_box(0), v___x_5487_);
lean_inc(v_f_5482_);
v___f_5489_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5489_, 0, v_toPure_5486_);
lean_closure_set(v___f_5489_, 1, v_inst_5478_);
lean_closure_set(v___f_5489_, 2, v_inst_5479_);
lean_closure_set(v___f_5489_, 3, v_inst_5480_);
lean_closure_set(v___f_5489_, 4, v_ch_5481_);
lean_closure_set(v___f_5489_, 5, v_f_5482_);
v___f_5490_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5490_, 0, v_toPure_5486_);
lean_closure_set(v___f_5490_, 1, v_b_5483_);
lean_closure_set(v___f_5490_, 2, v_f_5482_);
lean_closure_set(v___f_5490_, 3, v_toBind_5485_);
lean_closure_set(v___f_5490_, 4, v___f_5489_);
v___x_5491_ = lean_apply_4(v_toBind_5485_, lean_box(0), lean_box(0), v___x_5488_, v___f_5490_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5492_, lean_object* v_inst_5493_, lean_object* v_inst_5494_, lean_object* v_inst_5495_, lean_object* v_ch_5496_, lean_object* v_f_5497_, lean_object* v_____do__lift_5498_){
_start:
{
if (lean_obj_tag(v_____do__lift_5498_) == 0)
{
lean_object* v_a_5499_; lean_object* v___x_5500_; 
lean_dec(v_f_5497_);
lean_dec_ref(v_ch_5496_);
lean_dec(v_inst_5495_);
lean_dec_ref(v_inst_5494_);
lean_dec(v_inst_5493_);
v_a_5499_ = lean_ctor_get(v_____do__lift_5498_, 0);
lean_inc(v_a_5499_);
lean_dec_ref(v_____do__lift_5498_);
v___x_5500_ = lean_apply_2(v_toPure_5492_, lean_box(0), v_a_5499_);
return v___x_5500_;
}
else
{
lean_object* v_a_5501_; lean_object* v___x_5502_; 
lean_dec(v_toPure_5492_);
v_a_5501_ = lean_ctor_get(v_____do__lift_5498_, 0);
lean_inc(v_a_5501_);
lean_dec_ref(v_____do__lift_5498_);
v___x_5502_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5493_, v_inst_5494_, v_inst_5495_, v_ch_5496_, v_f_5497_, v_a_5501_);
return v___x_5502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5503_, lean_object* v_m_5504_, lean_object* v_00_u03b2_5505_, lean_object* v_inst_5506_, lean_object* v_inst_5507_, lean_object* v_inst_5508_, lean_object* v_ch_5509_, lean_object* v_f_5510_, lean_object* v_b_5511_){
_start:
{
lean_object* v___x_5512_; 
v___x_5512_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5506_, v_inst_5507_, v_inst_5508_, v_ch_5509_, v_f_5510_, v_b_5511_);
return v___x_5512_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5513_, lean_object* v_inst_5514_, lean_object* v_inst_5515_, lean_object* v_00_u03b2_5516_, lean_object* v_ch_5517_, lean_object* v_b_5518_, lean_object* v_f_5519_){
_start:
{
lean_object* v___x_5520_; 
v___x_5520_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5513_, v_inst_5514_, v_inst_5515_, v_ch_5517_, v_f_5519_, v_b_5518_);
return v___x_5520_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5521_, lean_object* v_inst_5522_, lean_object* v_inst_5523_){
_start:
{
lean_object* v___f_5524_; 
v___f_5524_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5524_, 0, v_inst_5521_);
lean_closure_set(v___f_5524_, 1, v_inst_5522_);
lean_closure_set(v___f_5524_, 2, v_inst_5523_);
return v___f_5524_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5525_, lean_object* v_m_5526_, lean_object* v_inst_5527_, lean_object* v_inst_5528_, lean_object* v_inst_5529_){
_start:
{
lean_object* v___f_5530_; 
v___f_5530_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5530_, 0, v_inst_5527_);
lean_closure_set(v___f_5530_, 1, v_inst_5528_);
lean_closure_set(v___f_5530_, 2, v_inst_5529_);
return v___f_5530_;
}
}
lean_object* runtime_initialize_Std_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Async_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Broadcast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = runtime_initialize_Std_Internal_Async_IO(builtin);
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
lean_object* initialize_Std_Internal_Async_IO(uint8_t builtin);
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
res = initialize_Std_Internal_Async_IO(builtin);
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

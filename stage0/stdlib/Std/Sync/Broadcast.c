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
lean_object* l_Option_repr___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_ST_Prim_Ref_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_IO_Async_EAsync_instMonad(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot_default___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot_default(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot_default(lean_object* v_a_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot_default___closed__0));
return v___x_233_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___closed__0(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot_default(lean_box(0));
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
v___x_413_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot_default___closed__0));
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
lean_object* v_ref_491_; lean_object* v_mutex_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_ref_491_ = lean_ctor_get(v_mutex_488_, 0);
lean_inc(v_ref_491_);
v_mutex_492_ = lean_ctor_get(v_mutex_488_, 1);
lean_inc(v_mutex_492_);
lean_dec_ref(v_mutex_488_);
v___x_493_ = lean_io_basemutex_lock(v_mutex_492_);
v___x_494_ = lean_apply_2(v_k_489_, v_ref_491_, lean_box(0));
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_503_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_503_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_503_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_494_);
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
v_a_504_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v___x_494_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_494_);
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
v___x_579_ = lean_nat_add(v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec(v___y_577_);
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
lean_ctor_set(v___x_559_, 3, v___y_576_);
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
lean_ctor_set(v_reuseFailAlloc_584_, 3, v___y_576_);
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
v___y_576_ = v___x_590_;
v___y_577_ = v___x_591_;
v___y_578_ = v_size_592_;
goto v___jp_575_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_unsigned_to_nat(0u);
v___y_576_ = v___x_590_;
v___y_577_ = v___x_591_;
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
v___x_717_ = lean_nat_add(v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec(v___y_715_);
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
lean_ctor_set(v___x_697_, 3, v___y_714_);
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
lean_ctor_set(v_reuseFailAlloc_722_, 3, v___y_714_);
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
v___y_714_ = v___x_729_;
v___y_715_ = v___x_730_;
v___y_716_ = v_size_731_;
goto v___jp_713_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___y_714_ = v___x_729_;
v___y_715_ = v___x_730_;
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
v___x_905_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_905_, 0, lean_box(0));
lean_closure_set(v___x_905_, 1, lean_box(0));
lean_closure_set(v___x_905_, 2, v_a_901_);
v___x_906_ = lean_apply_2(v_inst_900_, lean_box(0), v___x_905_);
v___x_907_ = lean_apply_4(v_toBind_903_, lean_box(0), lean_box(0), v___x_906_, v___f_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(lean_object* v_m_908_, lean_object* v_00_u03b1_909_, lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_910_, v_inst_911_, v_a_912_);
return v___x_913_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(lean_object* v_a_914_){
_start:
{
lean_object* v___x_916_; lean_object* v_capacity_917_; lean_object* v_size_918_; uint8_t v___x_919_; 
v___x_916_ = lean_st_ref_get(v_a_914_);
v_capacity_917_ = lean_ctor_get(v___x_916_, 2);
lean_inc(v_capacity_917_);
v_size_918_ = lean_ctor_get(v___x_916_, 3);
lean_inc(v_size_918_);
lean_dec(v___x_916_);
v___x_919_ = lean_nat_dec_le(v_capacity_917_, v_size_918_);
lean_dec(v_size_918_);
lean_dec(v_capacity_917_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg___boxed(lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
uint8_t v_res_922_; lean_object* v_r_923_; 
v_res_922_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_920_);
lean_dec(v_a_920_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(lean_object* v_00_u03b1_924_, lean_object* v_a_925_){
_start:
{
uint8_t v___x_927_; 
v___x_927_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___boxed(lean_object* v_00_u03b1_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
uint8_t v_res_931_; lean_object* v_r_932_; 
v_res_931_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(v_00_u03b1_928_, v_a_929_);
lean_dec(v_a_929_);
v_r_932_ = lean_box(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(lean_object* v_value_933_, lean_object* v_st_934_){
_start:
{
lean_object* v_producers_936_; lean_object* v_waiters_937_; lean_object* v_capacity_938_; lean_object* v_size_939_; lean_object* v_buffer_940_; lean_object* v_write_941_; lean_object* v_read_942_; lean_object* v_receivers_943_; lean_object* v_nextId_944_; uint8_t v_closed_945_; lean_object* v_pos_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_966_; 
v_producers_936_ = lean_ctor_get(v_st_934_, 0);
v_waiters_937_ = lean_ctor_get(v_st_934_, 1);
v_capacity_938_ = lean_ctor_get(v_st_934_, 2);
v_size_939_ = lean_ctor_get(v_st_934_, 3);
v_buffer_940_ = lean_ctor_get(v_st_934_, 4);
v_write_941_ = lean_ctor_get(v_st_934_, 5);
v_read_942_ = lean_ctor_get(v_st_934_, 6);
v_receivers_943_ = lean_ctor_get(v_st_934_, 7);
v_nextId_944_ = lean_ctor_get(v_st_934_, 8);
v_closed_945_ = lean_ctor_get_uint8(v_st_934_, sizeof(void*)*10);
v_pos_946_ = lean_ctor_get(v_st_934_, 9);
v_isSharedCheck_966_ = !lean_is_exclusive(v_st_934_);
if (v_isSharedCheck_966_ == 0)
{
v___x_948_ = v_st_934_;
v_isShared_949_ = v_isSharedCheck_966_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_pos_946_);
lean_inc(v_nextId_944_);
lean_inc(v_receivers_943_);
lean_inc(v_read_942_);
lean_inc(v_write_941_);
lean_inc(v_buffer_940_);
lean_inc(v_size_939_);
lean_inc(v_capacity_938_);
lean_inc(v_waiters_937_);
lean_inc(v_producers_936_);
lean_dec(v_st_934_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_966_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_tailRef_950_; lean_object* v___x_951_; lean_object* v___y_953_; 
v_tailRef_950_ = lean_array_fget_borrowed(v_buffer_940_, v_write_941_);
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_value_933_);
if (lean_obj_tag(v_receivers_943_) == 0)
{
lean_object* v_size_964_; 
v_size_964_ = lean_ctor_get(v_receivers_943_, 0);
lean_inc(v_size_964_);
v___y_953_ = v_size_964_;
goto v___jp_952_;
}
else
{
lean_object* v___x_965_; 
v___x_965_ = lean_unsigned_to_nat(0u);
v___y_953_ = v___x_965_;
goto v___jp_952_;
}
v___jp_952_:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
lean_inc(v_pos_946_);
v___x_954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_954_, 0, v___x_951_);
lean_ctor_set(v___x_954_, 1, v_pos_946_);
lean_ctor_set(v___x_954_, 2, v___y_953_);
v___x_955_ = lean_st_ref_set(v_tailRef_950_, v___x_954_);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_write_941_, v___x_956_);
lean_dec(v_write_941_);
v___x_958_ = lean_nat_mod(v___x_957_, v_capacity_938_);
lean_dec(v___x_957_);
v___x_959_ = lean_nat_add(v_size_939_, v___x_956_);
lean_dec(v_size_939_);
v___x_960_ = lean_nat_add(v_pos_946_, v___x_956_);
lean_dec(v_pos_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 9, v___x_960_);
lean_ctor_set(v___x_948_, 5, v___x_958_);
lean_ctor_set(v___x_948_, 3, v___x_959_);
v___x_962_ = v___x_948_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_producers_936_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_waiters_937_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_capacity_938_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v_buffer_940_);
lean_ctor_set(v_reuseFailAlloc_963_, 5, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_963_, 6, v_read_942_);
lean_ctor_set(v_reuseFailAlloc_963_, 7, v_receivers_943_);
lean_ctor_set(v_reuseFailAlloc_963_, 8, v_nextId_944_);
lean_ctor_set(v_reuseFailAlloc_963_, 9, v___x_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_963_, sizeof(void*)*10, v_closed_945_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg___boxed(lean_object* v_value_967_, lean_object* v_st_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_967_, v_st_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(lean_object* v_00_u03b1_971_, lean_object* v_value_972_, lean_object* v_st_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_972_, v_st_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___boxed(lean_object* v_00_u03b1_976_, lean_object* v_value_977_, lean_object* v_st_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(v_00_u03b1_976_, v_value_977_, v_st_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(lean_object* v_st_981_){
_start:
{
lean_object* v_producers_982_; lean_object* v_waiters_983_; lean_object* v_capacity_984_; lean_object* v_size_985_; lean_object* v_buffer_986_; lean_object* v_write_987_; lean_object* v_read_988_; lean_object* v_receivers_989_; lean_object* v_nextId_990_; uint8_t v_closed_991_; lean_object* v_pos_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1003_; 
v_producers_982_ = lean_ctor_get(v_st_981_, 0);
v_waiters_983_ = lean_ctor_get(v_st_981_, 1);
v_capacity_984_ = lean_ctor_get(v_st_981_, 2);
v_size_985_ = lean_ctor_get(v_st_981_, 3);
v_buffer_986_ = lean_ctor_get(v_st_981_, 4);
v_write_987_ = lean_ctor_get(v_st_981_, 5);
v_read_988_ = lean_ctor_get(v_st_981_, 6);
v_receivers_989_ = lean_ctor_get(v_st_981_, 7);
v_nextId_990_ = lean_ctor_get(v_st_981_, 8);
v_closed_991_ = lean_ctor_get_uint8(v_st_981_, sizeof(void*)*10);
v_pos_992_ = lean_ctor_get(v_st_981_, 9);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_st_981_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_994_ = v_st_981_;
v_isShared_995_ = v_isSharedCheck_1003_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_pos_992_);
lean_inc(v_nextId_990_);
lean_inc(v_receivers_989_);
lean_inc(v_read_988_);
lean_inc(v_write_987_);
lean_inc(v_buffer_986_);
lean_inc(v_size_985_);
lean_inc(v_capacity_984_);
lean_inc(v_waiters_983_);
lean_inc(v_producers_982_);
lean_dec(v_st_981_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1003_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v_size_997_; lean_object* v___x_998_; lean_object* v_read_999_; lean_object* v___x_1001_; 
v___x_996_ = lean_unsigned_to_nat(1u);
v_size_997_ = lean_nat_sub(v_size_985_, v___x_996_);
lean_dec(v_size_985_);
v___x_998_ = lean_nat_add(v_read_988_, v___x_996_);
lean_dec(v_read_988_);
v_read_999_ = lean_nat_mod(v___x_998_, v_capacity_984_);
lean_dec(v___x_998_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 6, v_read_999_);
lean_ctor_set(v___x_994_, 3, v_size_997_);
v___x_1001_ = v___x_994_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_producers_982_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_waiters_983_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_capacity_984_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_size_997_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_buffer_986_);
lean_ctor_set(v_reuseFailAlloc_1002_, 5, v_write_987_);
lean_ctor_set(v_reuseFailAlloc_1002_, 6, v_read_999_);
lean_ctor_set(v_reuseFailAlloc_1002_, 7, v_receivers_989_);
lean_ctor_set(v_reuseFailAlloc_1002_, 8, v_nextId_990_);
lean_ctor_set(v_reuseFailAlloc_1002_, 9, v_pos_992_);
lean_ctor_set_uint8(v_reuseFailAlloc_1002_, sizeof(void*)*10, v_closed_991_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue(lean_object* v_00_u03b1_1004_, lean_object* v_st_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_st_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(lean_object* v_toApplicative_1007_, lean_object* v_place_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_capacity_1010_; lean_object* v_buffer_1011_; lean_object* v_toPure_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_capacity_1010_ = lean_ctor_get(v_a_1009_, 2);
v_buffer_1011_ = lean_ctor_get(v_a_1009_, 4);
v_toPure_1012_ = lean_ctor_get(v_toApplicative_1007_, 1);
lean_inc(v_toPure_1012_);
lean_dec_ref(v_toApplicative_1007_);
v___x_1013_ = lean_nat_mod(v_place_1008_, v_capacity_1010_);
v___x_1014_ = lean_array_fget_borrowed(v_buffer_1011_, v___x_1013_);
lean_dec(v___x_1013_);
lean_inc(v___x_1014_);
v___x_1015_ = lean_apply_2(v_toPure_1012_, lean_box(0), v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed(lean_object* v_toApplicative_1016_, lean_object* v_place_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(v_toApplicative_1016_, v_place_1017_, v_a_1018_);
lean_dec_ref(v_a_1018_);
lean_dec(v_place_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_place_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_toApplicative_1024_; lean_object* v_toBind_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_toApplicative_1024_ = lean_ctor_get(v_inst_1020_, 0);
lean_inc_ref(v_toApplicative_1024_);
v_toBind_1025_ = lean_ctor_get(v_inst_1020_, 1);
lean_inc(v_toBind_1025_);
lean_dec_ref(v_inst_1020_);
v___f_1026_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1026_, 0, v_toApplicative_1024_);
lean_closure_set(v___f_1026_, 1, v_place_1022_);
v___x_1027_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1027_, 0, lean_box(0));
lean_closure_set(v___x_1027_, 1, lean_box(0));
lean_closure_set(v___x_1027_, 2, v_a_1023_);
v___x_1028_ = lean_apply_2(v_inst_1021_, lean_box(0), v___x_1027_);
v___x_1029_ = lean_apply_4(v_toBind_1025_, lean_box(0), lean_box(0), v___x_1028_, v___f_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(lean_object* v_m_1030_, lean_object* v_00_u03b1_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_place_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1032_, v_inst_1033_, v_place_1034_, v_a_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(lean_object* v_as_1037_, size_t v_sz_1038_, size_t v_i_1039_, lean_object* v_b_1040_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_usize_dec_lt(v_i_1039_, v_sz_1038_);
if (v___x_1042_ == 0)
{
return v_b_1040_;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; 
v_a_1043_ = lean_array_uget_borrowed(v_as_1037_, v_i_1039_);
v___x_1044_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1043_, v___x_1042_);
v___x_1045_ = lean_box(0);
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_add(v_i_1039_, v___x_1046_);
v_i_1039_ = v___x_1047_;
v_b_1040_ = v___x_1045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg___boxed(lean_object* v_as_1049_, lean_object* v_sz_1050_, lean_object* v_i_1051_, lean_object* v_b_1052_, lean_object* v___y_1053_){
_start:
{
size_t v_sz_boxed_1054_; size_t v_i_boxed_1055_; lean_object* v_res_1056_; 
v_sz_boxed_1054_ = lean_unbox_usize(v_sz_1050_);
lean_dec(v_sz_1050_);
v_i_boxed_1055_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_res_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1049_, v_sz_boxed_1054_, v_i_boxed_1055_, v_b_1052_);
lean_dec_ref(v_as_1049_);
return v_res_1056_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_Queue_empty(lean_box(0));
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(lean_object* v_v_1058_, lean_object* v_a_1059_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_1059_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_producers_1064_; lean_object* v_waiters_1065_; lean_object* v_capacity_1066_; lean_object* v_size_1067_; lean_object* v_buffer_1068_; lean_object* v_write_1069_; lean_object* v_read_1070_; lean_object* v_receivers_1071_; lean_object* v_nextId_1072_; uint8_t v_closed_1073_; lean_object* v_pos_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1093_; 
v___x_1062_ = lean_st_ref_get(v_a_1059_);
v___x_1063_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_v_1058_, v___x_1062_);
v_producers_1064_ = lean_ctor_get(v___x_1063_, 0);
v_waiters_1065_ = lean_ctor_get(v___x_1063_, 1);
v_capacity_1066_ = lean_ctor_get(v___x_1063_, 2);
v_size_1067_ = lean_ctor_get(v___x_1063_, 3);
v_buffer_1068_ = lean_ctor_get(v___x_1063_, 4);
v_write_1069_ = lean_ctor_get(v___x_1063_, 5);
v_read_1070_ = lean_ctor_get(v___x_1063_, 6);
v_receivers_1071_ = lean_ctor_get(v___x_1063_, 7);
v_nextId_1072_ = lean_ctor_get(v___x_1063_, 8);
v_closed_1073_ = lean_ctor_get_uint8(v___x_1063_, sizeof(void*)*10);
v_pos_1074_ = lean_ctor_get(v___x_1063_, 9);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1076_ = v___x_1063_;
v_isShared_1077_ = v_isSharedCheck_1093_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_pos_1074_);
lean_inc(v_nextId_1072_);
lean_inc(v_receivers_1071_);
lean_inc(v_read_1070_);
lean_inc(v_write_1069_);
lean_inc(v_buffer_1068_);
lean_inc(v_size_1067_);
lean_inc(v_capacity_1066_);
lean_inc(v_waiters_1065_);
lean_inc(v_producers_1064_);
lean_dec(v___x_1063_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1093_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0);
lean_inc(v_receivers_1071_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_producers_1064_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_capacity_1066_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_size_1067_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_buffer_1068_);
lean_ctor_set(v_reuseFailAlloc_1092_, 5, v_write_1069_);
lean_ctor_set(v_reuseFailAlloc_1092_, 6, v_read_1070_);
lean_ctor_set(v_reuseFailAlloc_1092_, 7, v_receivers_1071_);
lean_ctor_set(v_reuseFailAlloc_1092_, 8, v_nextId_1072_);
lean_ctor_set(v_reuseFailAlloc_1092_, 9, v_pos_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1092_, sizeof(void*)*10, v_closed_1073_);
v___x_1080_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; size_t v_sz_1084_; size_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___y_1088_; 
v___x_1081_ = lean_st_ref_set(v_a_1059_, v___x_1080_);
v___x_1082_ = l_Std_Queue_toArray___redArg(v_waiters_1065_);
v___x_1083_ = lean_box(0);
v_sz_1084_ = lean_array_size(v___x_1082_);
v___x_1085_ = ((size_t)0ULL);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v___x_1082_, v_sz_1084_, v___x_1085_, v___x_1083_);
lean_dec_ref(v___x_1082_);
if (lean_obj_tag(v_receivers_1071_) == 0)
{
lean_object* v_size_1090_; 
v_size_1090_ = lean_ctor_get(v_receivers_1071_, 0);
lean_inc(v_size_1090_);
lean_dec_ref(v_receivers_1071_);
v___y_1088_ = v_size_1090_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_unsigned_to_nat(0u);
v___y_1088_ = v___x_1091_;
goto v___jp_1087_;
}
v___jp_1087_:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___y_1088_);
return v___x_1089_;
}
}
}
}
else
{
lean_object* v___x_1094_; 
lean_dec(v_v_1058_);
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1095_, v_a_1096_);
lean_dec(v_a_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(lean_object* v_00_u03b1_1099_, lean_object* v_v_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1100_, v_a_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_v_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(v_00_u03b1_1104_, v_v_1105_, v_a_1106_);
lean_dec(v_a_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(lean_object* v_00_u03b1_1109_, lean_object* v_as_1110_, size_t v_sz_1111_, size_t v_i_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1110_, v_sz_1111_, v_i_1112_, v_b_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_as_1118_, lean_object* v_sz_1119_, lean_object* v_i_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
size_t v_sz_boxed_1124_; size_t v_i_boxed_1125_; lean_object* v_res_1126_; 
v_sz_boxed_1124_ = lean_unbox_usize(v_sz_1119_);
lean_dec(v_sz_1119_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1120_);
lean_dec(v_i_1120_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(v_00_u03b1_1117_, v_as_1118_, v_sz_boxed_1124_, v_i_boxed_1125_, v_b_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v_as_1118_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(lean_object* v_mutex_1127_, lean_object* v_k_1128_){
_start:
{
lean_object* v_ref_1130_; lean_object* v_mutex_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_ref_1130_ = lean_ctor_get(v_mutex_1127_, 0);
lean_inc(v_ref_1130_);
v_mutex_1131_ = lean_ctor_get(v_mutex_1127_, 1);
lean_inc(v_mutex_1131_);
lean_dec_ref(v_mutex_1127_);
v___x_1132_ = lean_io_basemutex_lock(v_mutex_1131_);
v___x_1133_ = lean_apply_2(v_k_1128_, v_ref_1130_, lean_box(0));
v___x_1134_ = lean_io_basemutex_unlock(v_mutex_1131_);
lean_dec(v_mutex_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg___boxed(lean_object* v_mutex_1135_, lean_object* v_k_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1135_, v_k_1136_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_mutex_1141_, lean_object* v_k_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1141_, v_k_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_mutex_1147_, lean_object* v_k_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(v_00_u03b1_1145_, v_00_u03b2_1146_, v_mutex_1147_, v_k_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(lean_object* v_v_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; uint8_t v_closed_1157_; 
v___x_1156_ = lean_st_ref_get(v___y_1154_);
v_closed_1157_ = lean_ctor_get_uint8(v___x_1156_, sizeof(void*)*10);
lean_dec(v___x_1156_);
if (v_closed_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v_receivers_1159_; 
v___x_1158_ = lean_st_ref_get(v___y_1154_);
v_receivers_1159_ = lean_ctor_get(v___x_1158_, 7);
lean_inc(v_receivers_1159_);
lean_dec(v___x_1158_);
if (lean_obj_tag(v_receivers_1159_) == 0)
{
lean_object* v___x_1160_; 
lean_dec_ref(v_receivers_1159_);
v___x_1160_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1153_, v___y_1154_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; 
lean_dec(v_v_1153_);
v___x_1161_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0));
return v___x_1161_;
}
}
else
{
lean_object* v___x_1162_; 
lean_dec(v_v_1153_);
v___x_1162_ = lean_box(0);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(v_v_1163_, v___y_1164_);
lean_dec(v___y_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(lean_object* v_ch_1167_, lean_object* v_v_1168_){
_start:
{
lean_object* v___f_1170_; lean_object* v___x_1171_; 
v___f_1170_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1170_, 0, v_v_1168_);
v___x_1171_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1167_, v___f_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___boxed(lean_object* v_ch_1172_, lean_object* v_v_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1172_, v_v_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(lean_object* v_00_u03b1_1176_, lean_object* v_ch_1177_, lean_object* v_v_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1177_, v_v_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_ch_1182_, lean_object* v_v_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(v_00_u03b1_1181_, v_ch_1182_, v_v_1183_);
return v_res_1185_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0));
v___x_1189_ = lean_task_pure(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2));
v___x_1194_ = lean_task_pure(v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(lean_object* v_v_1195_, lean_object* v___f_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; uint8_t v_closed_1200_; 
v___x_1199_ = lean_st_ref_get(v___y_1197_);
v_closed_1200_ = lean_ctor_get_uint8(v___x_1199_, sizeof(void*)*10);
lean_dec(v___x_1199_);
if (v_closed_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v_receivers_1202_; 
v___x_1201_ = lean_st_ref_get(v___y_1197_);
v_receivers_1202_ = lean_ctor_get(v___x_1201_, 7);
lean_inc(v_receivers_1202_);
lean_dec(v___x_1201_);
if (lean_obj_tag(v_receivers_1202_) == 0)
{
lean_object* v___x_1203_; 
lean_dec_ref(v_receivers_1202_);
v___x_1203_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1195_, v___y_1197_);
if (lean_obj_tag(v___x_1203_) == 1)
{
lean_object* v_val_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v___f_1196_);
v_val_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_val_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_val_1204_);
v___x_1209_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_task_pure(v___x_1209_);
return v___x_1210_;
}
}
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_producers_1215_; lean_object* v_waiters_1216_; lean_object* v_capacity_1217_; lean_object* v_size_1218_; lean_object* v_buffer_1219_; lean_object* v_write_1220_; lean_object* v_read_1221_; lean_object* v_receivers_1222_; lean_object* v_nextId_1223_; uint8_t v_closed_1224_; lean_object* v_pos_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v___x_1203_);
v___x_1213_ = lean_io_promise_new();
v___x_1214_ = lean_st_ref_take(v___y_1197_);
v_producers_1215_ = lean_ctor_get(v___x_1214_, 0);
v_waiters_1216_ = lean_ctor_get(v___x_1214_, 1);
v_capacity_1217_ = lean_ctor_get(v___x_1214_, 2);
v_size_1218_ = lean_ctor_get(v___x_1214_, 3);
v_buffer_1219_ = lean_ctor_get(v___x_1214_, 4);
v_write_1220_ = lean_ctor_get(v___x_1214_, 5);
v_read_1221_ = lean_ctor_get(v___x_1214_, 6);
v_receivers_1222_ = lean_ctor_get(v___x_1214_, 7);
v_nextId_1223_ = lean_ctor_get(v___x_1214_, 8);
v_closed_1224_ = lean_ctor_get_uint8(v___x_1214_, sizeof(void*)*10);
v_pos_1225_ = lean_ctor_get(v___x_1214_, 9);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1227_ = v___x_1214_;
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_pos_1225_);
lean_inc(v_nextId_1223_);
lean_inc(v_receivers_1222_);
lean_inc(v_read_1221_);
lean_inc(v_write_1220_);
lean_inc(v_buffer_1219_);
lean_inc(v_size_1218_);
lean_inc(v_capacity_1217_);
lean_inc(v_waiters_1216_);
lean_inc(v_producers_1215_);
lean_dec(v___x_1214_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1237_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_inc(v___x_1213_);
v___x_1229_ = l_Std_Queue_enqueue___redArg(v___x_1213_, v_producers_1215_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_waiters_1216_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_capacity_1217_);
lean_ctor_set(v_reuseFailAlloc_1236_, 3, v_size_1218_);
lean_ctor_set(v_reuseFailAlloc_1236_, 4, v_buffer_1219_);
lean_ctor_set(v_reuseFailAlloc_1236_, 5, v_write_1220_);
lean_ctor_set(v_reuseFailAlloc_1236_, 6, v_read_1221_);
lean_ctor_set(v_reuseFailAlloc_1236_, 7, v_receivers_1222_);
lean_ctor_set(v_reuseFailAlloc_1236_, 8, v_nextId_1223_);
lean_ctor_set(v_reuseFailAlloc_1236_, 9, v_pos_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1236_, sizeof(void*)*10, v_closed_1224_);
v___x_1231_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1232_ = lean_st_ref_set(v___y_1197_, v___x_1231_);
v___x_1233_ = lean_io_promise_result_opt(v___x_1213_);
lean_dec(v___x_1213_);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = lean_io_bind_task(v___x_1233_, v___f_1196_, v___x_1234_, v_closed_1200_);
return v___x_1235_;
}
}
}
}
else
{
lean_object* v___x_1238_; 
lean_dec_ref(v___f_1196_);
lean_dec(v_v_1195_);
v___x_1238_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1);
return v___x_1238_;
}
}
else
{
lean_object* v___x_1239_; 
lean_dec_ref(v___f_1196_);
lean_dec(v_v_1195_);
v___x_1239_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_1240_, lean_object* v___f_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(v_v_1240_, v___f_1241_, v___y_1242_);
lean_dec(v___y_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(lean_object* v_ch_1245_, lean_object* v_v_1246_, lean_object* v_res_1247_){
_start:
{
if (lean_obj_tag(v_res_1247_) == 0)
{
lean_dec(v_v_1246_);
lean_dec_ref(v_ch_1245_);
goto v___jp_1249_;
}
else
{
lean_object* v_val_1251_; uint8_t v___x_1252_; 
v_val_1251_ = lean_ctor_get(v_res_1247_, 0);
v___x_1252_ = lean_unbox(v_val_1251_);
if (v___x_1252_ == 0)
{
lean_dec(v_v_1246_);
lean_dec_ref(v_ch_1245_);
goto v___jp_1249_;
}
else
{
lean_object* v___x_1253_; 
v___x_1253_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1245_, v_v_1246_);
return v___x_1253_;
}
}
v___jp_1249_:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_1254_, lean_object* v_v_1255_, lean_object* v_res_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(v_ch_1254_, v_v_1255_, v_res_1256_);
lean_dec(v_res_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(lean_object* v_ch_1259_, lean_object* v_v_1260_){
_start:
{
lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; 
lean_inc(v_v_1260_);
lean_inc_ref(v_ch_1259_);
v___f_1262_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1262_, 0, v_ch_1259_);
lean_closure_set(v___f_1262_, 1, v_v_1260_);
v___f_1263_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1263_, 0, v_v_1260_);
lean_closure_set(v___f_1263_, 1, v___f_1262_);
v___x_1264_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1259_, v___f_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___boxed(lean_object* v_ch_1265_, lean_object* v_v_1266_, lean_object* v_a_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1265_, v_v_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send(lean_object* v_00_u03b1_1269_, lean_object* v_ch_1270_, lean_object* v_v_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1270_, v_v_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_ch_1275_, lean_object* v_v_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send(v_00_u03b1_1274_, v_ch_1275_, v_v_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(lean_object* v_mutex_1279_, lean_object* v_k_1280_){
_start:
{
lean_object* v_ref_1282_; lean_object* v_mutex_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_ref_1282_ = lean_ctor_get(v_mutex_1279_, 0);
lean_inc(v_ref_1282_);
v_mutex_1283_ = lean_ctor_get(v_mutex_1279_, 1);
lean_inc(v_mutex_1283_);
lean_dec_ref(v_mutex_1279_);
v___x_1284_ = lean_io_basemutex_lock(v_mutex_1283_);
v___x_1285_ = lean_apply_2(v_k_1280_, v_ref_1282_, lean_box(0));
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1294_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_io_basemutex_unlock(v_mutex_1283_);
lean_dec(v_mutex_1283_);
if (v_isShared_1289_ == 0)
{
v___x_1292_ = v___x_1288_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1286_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1303_; 
v_a_1295_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1297_ = v___x_1285_;
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1285_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_io_basemutex_unlock(v_mutex_1283_);
lean_dec(v_mutex_1283_);
if (v_isShared_1298_ == 0)
{
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1295_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object* v_mutex_1304_, lean_object* v_k_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_mutex_1304_, v_k_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object* v_00_u03b1_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_mutex_1310_, lean_object* v_k_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_mutex_1310_, v_k_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_1314_, lean_object* v_00_u03b2_1315_, lean_object* v_mutex_1316_, lean_object* v_k_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(v_00_u03b1_1314_, v_00_u03b2_1315_, v_mutex_1316_, v_k_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(uint8_t v___x_1320_, lean_object* v_as_1321_, size_t v_sz_1322_, size_t v_i_1323_, lean_object* v_b_1324_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_usize_dec_lt(v_i_1323_, v_sz_1322_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_b_1324_);
return v___x_1327_;
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; 
v_a_1328_ = lean_array_uget_borrowed(v_as_1321_, v_i_1323_);
v___x_1329_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1328_, v___x_1320_);
v___x_1330_ = lean_box(0);
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1323_, v___x_1331_);
v_i_1323_ = v___x_1332_;
v_b_1324_ = v___x_1330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_1334_, lean_object* v_as_1335_, lean_object* v_sz_1336_, lean_object* v_i_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v___x_2505__boxed_1340_; size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v___x_2505__boxed_1340_ = lean_unbox(v___x_1334_);
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1336_);
lean_dec(v_sz_1336_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1337_);
lean_dec(v_i_1337_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_2505__boxed_1340_, v_as_1335_, v_sz_boxed_1341_, v_i_boxed_1342_, v_b_1338_);
lean_dec_ref(v_as_1335_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; uint8_t v_closed_1347_; 
v___x_1346_ = lean_st_ref_get(v___y_1344_);
v_closed_1347_ = lean_ctor_get_uint8(v___x_1346_, sizeof(void*)*10);
if (v_closed_1347_ == 0)
{
lean_object* v_producers_1348_; lean_object* v_waiters_1349_; lean_object* v_capacity_1350_; lean_object* v_size_1351_; lean_object* v_buffer_1352_; lean_object* v_write_1353_; lean_object* v_read_1354_; lean_object* v_receivers_1355_; lean_object* v_nextId_1356_; lean_object* v_pos_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1380_; 
v_producers_1348_ = lean_ctor_get(v___x_1346_, 0);
v_waiters_1349_ = lean_ctor_get(v___x_1346_, 1);
v_capacity_1350_ = lean_ctor_get(v___x_1346_, 2);
v_size_1351_ = lean_ctor_get(v___x_1346_, 3);
v_buffer_1352_ = lean_ctor_get(v___x_1346_, 4);
v_write_1353_ = lean_ctor_get(v___x_1346_, 5);
v_read_1354_ = lean_ctor_get(v___x_1346_, 6);
v_receivers_1355_ = lean_ctor_get(v___x_1346_, 7);
v_nextId_1356_ = lean_ctor_get(v___x_1346_, 8);
v_pos_1357_ = lean_ctor_get(v___x_1346_, 9);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1359_ = v___x_1346_;
v_isShared_1360_ = v_isSharedCheck_1380_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_pos_1357_);
lean_inc(v_nextId_1356_);
lean_inc(v_receivers_1355_);
lean_inc(v_read_1354_);
lean_inc(v_write_1353_);
lean_inc(v_buffer_1352_);
lean_inc(v_size_1351_);
lean_inc(v_capacity_1350_);
lean_inc(v_waiters_1349_);
lean_inc(v_producers_1348_);
lean_dec(v___x_1346_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1380_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; size_t v_sz_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1361_ = l_Std_Queue_toArray___redArg(v_waiters_1349_);
v___x_1362_ = lean_box(0);
v_sz_1363_ = lean_array_size(v___x_1361_);
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v_closed_1347_, v___x_1361_, v_sz_1363_, v___x_1364_, v___x_1362_);
lean_dec_ref(v___x_1361_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1365_, 0);
lean_dec(v_unused_1379_);
v___x_1367_ = v___x_1365_;
v_isShared_1368_ = v_isSharedCheck_1378_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v___x_1365_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1378_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1372_; 
v___x_1369_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___closed__0);
v___x_1370_ = 1;
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1369_);
v___x_1372_ = v___x_1359_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_producers_1348_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_capacity_1350_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_size_1351_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_buffer_1352_);
lean_ctor_set(v_reuseFailAlloc_1377_, 5, v_write_1353_);
lean_ctor_set(v_reuseFailAlloc_1377_, 6, v_read_1354_);
lean_ctor_set(v_reuseFailAlloc_1377_, 7, v_receivers_1355_);
lean_ctor_set(v_reuseFailAlloc_1377_, 8, v_nextId_1356_);
lean_ctor_set(v_reuseFailAlloc_1377_, 9, v_pos_1357_);
v___x_1372_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_ctor_set_uint8(v___x_1372_, sizeof(void*)*10, v___x_1370_);
v___x_1373_ = lean_st_ref_set(v___y_1344_, v___x_1372_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1362_);
v___x_1375_ = v___x_1367_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1362_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_del_object(v___x_1359_);
lean_dec(v_pos_1357_);
lean_dec(v_nextId_1356_);
lean_dec(v_receivers_1355_);
lean_dec(v_read_1354_);
lean_dec(v_write_1353_);
lean_dec_ref(v_buffer_1352_);
lean_dec(v_size_1351_);
lean_dec(v_capacity_1350_);
lean_dec_ref(v_producers_1348_);
return v___x_1365_;
}
}
}
else
{
uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v___x_1346_);
v___x_1381_ = 1;
v___x_1382_ = lean_box(v___x_1381_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(v___y_1384_);
lean_dec(v___y_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(lean_object* v_ch_1388_){
_start:
{
lean_object* v___f_1390_; lean_object* v___x_1391_; 
v___f_1390_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0));
v___x_1391_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_ch_1388_, v___f_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___boxed(lean_object* v_ch_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1392_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_object* v_00_u03b1_1395_, lean_object* v_ch_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___boxed(lean_object* v_00_u03b1_1399_, lean_object* v_ch_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close(v_00_u03b1_1399_, v_ch_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_object* v_00_u03b1_1403_, uint8_t v___x_1404_, lean_object* v_as_1405_, size_t v_sz_1406_, size_t v_i_1407_, lean_object* v_b_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1404_, v_as_1405_, v_sz_1406_, v_i_1407_, v_b_1408_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_1412_, lean_object* v___x_1413_, lean_object* v_as_1414_, lean_object* v_sz_1415_, lean_object* v_i_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v___x_2601__boxed_1420_; size_t v_sz_boxed_1421_; size_t v_i_boxed_1422_; lean_object* v_res_1423_; 
v___x_2601__boxed_1420_ = lean_unbox(v___x_1413_);
v_sz_boxed_1421_ = lean_unbox_usize(v_sz_1415_);
lean_dec(v_sz_1415_);
v_i_boxed_1422_ = lean_unbox_usize(v_i_1416_);
lean_dec(v_i_1416_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1412_, v___x_2601__boxed_1420_, v_as_1414_, v_sz_boxed_1421_, v_i_boxed_1422_, v_b_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v_as_1414_);
return v_res_1423_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; uint8_t v_closed_1427_; 
v___x_1426_ = lean_st_ref_get(v___y_1424_);
v_closed_1427_ = lean_ctor_get_uint8(v___x_1426_, sizeof(void*)*10);
lean_dec(v___x_1426_);
return v_closed_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v_res_1430_; lean_object* v_r_1431_; 
v_res_1430_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(v___y_1428_);
lean_dec(v___y_1428_);
v_r_1431_ = lean_box(v_res_1430_);
return v_r_1431_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object* v_ch_1433_){
_start:
{
lean_object* v___f_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___f_1435_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0));
v___x_1436_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1433_, v___f_1435_);
v___x_1437_ = lean_unbox(v___x_1436_);
lean_dec(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___boxed(lean_object* v_ch_1438_, lean_object* v_a_1439_){
_start:
{
uint8_t v_res_1440_; lean_object* v_r_1441_; 
v_res_1440_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1438_);
v_r_1441_ = lean_box(v_res_1440_);
return v_r_1441_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_object* v_00_u03b1_1442_, lean_object* v_ch_1443_){
_start:
{
uint8_t v___x_1445_; 
v___x_1445_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___boxed(lean_object* v_00_u03b1_1446_, lean_object* v_ch_1447_, lean_object* v_a_1448_){
_start:
{
uint8_t v_res_1449_; lean_object* v_r_1450_; 
v_res_1449_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(v_00_u03b1_1446_, v_ch_1447_);
v_r_1450_ = lean_box(v_res_1449_);
return v_r_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object* v_next_1451_, lean_object* v_slot_1452_){
_start:
{
lean_object* v_value_1453_; lean_object* v_pos_1454_; lean_object* v_remaining_1455_; uint8_t v___x_1456_; 
v_value_1453_ = lean_ctor_get(v_slot_1452_, 0);
v_pos_1454_ = lean_ctor_get(v_slot_1452_, 1);
v_remaining_1455_ = lean_ctor_get(v_slot_1452_, 2);
v___x_1456_ = lean_nat_dec_eq(v_next_1451_, v_pos_1454_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_box(v___x_1456_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v_slot_1452_);
return v___x_1460_;
}
else
{
lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1481_; 
lean_inc(v_remaining_1455_);
lean_inc(v_pos_1454_);
lean_inc(v_value_1453_);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_slot_1452_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; 
v_unused_1482_ = lean_ctor_get(v_slot_1452_, 2);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_slot_1452_, 1);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_slot_1452_, 0);
lean_dec(v_unused_1484_);
v___x_1462_ = v_slot_1452_;
v_isShared_1463_ = v_isSharedCheck_1481_;
goto v_resetjp_1461_;
}
else
{
lean_dec(v_slot_1452_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1481_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = lean_unsigned_to_nat(1u);
v___x_1465_ = lean_nat_dec_eq(v_remaining_1455_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1466_ = lean_box(v___x_1465_);
lean_inc(v_value_1453_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_value_1453_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_nat_sub(v_remaining_1455_, v___x_1464_);
lean_dec(v_remaining_1455_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 2, v___x_1468_);
v___x_1470_ = v___x_1462_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_value_1453_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_pos_1454_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1467_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
return v___x_1471_;
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
lean_dec(v_remaining_1455_);
v___x_1473_ = lean_box(v___x_1456_);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_value_1453_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = lean_box(0);
v___x_1476_ = lean_unsigned_to_nat(0u);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 2, v___x_1476_);
lean_ctor_set(v___x_1462_, 0, v___x_1475_);
v___x_1478_ = v___x_1462_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_pos_1454_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1474_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
return v___x_1479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object* v_next_1485_, lean_object* v_slot_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(v_next_1485_, v_slot_1486_);
lean_dec(v_next_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object* v_inst_1488_, lean_object* v_slot_1489_, lean_object* v_next_1490_){
_start:
{
lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___f_1491_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1491_, 0, v_next_1490_);
v___x_1492_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1492_, 0, lean_box(0));
lean_closure_set(v___x_1492_, 1, lean_box(0));
lean_closure_set(v___x_1492_, 2, lean_box(0));
lean_closure_set(v___x_1492_, 3, v_slot_1489_);
lean_closure_set(v___x_1492_, 4, v___f_1491_);
v___x_1493_ = lean_apply_2(v_inst_1488_, lean_box(0), v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object* v_m_1494_, lean_object* v_00_u03b1_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_slot_1498_, lean_object* v_next_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1497_, v_slot_1498_, v_next_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object* v_m_1502_, lean_object* v_00_u03b1_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_slot_1506_, lean_object* v_next_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(v_m_1502_, v_00_u03b1_1503_, v_inst_1504_, v_inst_1505_, v_slot_1506_, v_next_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec_ref(v_inst_1504_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object* v_toApplicative_1510_, lean_object* v_fst_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_toPure_1513_; lean_object* v___x_1514_; 
v_toPure_1513_ = lean_ctor_get(v_toApplicative_1510_, 1);
lean_inc(v_toPure_1513_);
lean_dec_ref(v_toApplicative_1510_);
v___x_1514_ = lean_apply_2(v_toPure_1513_, lean_box(0), v_fst_1511_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object* v_inst_1515_, lean_object* v_toBind_1516_, lean_object* v___f_1517_, lean_object* v_____r_1518_, lean_object* v_st_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1521_, 0, lean_box(0));
lean_closure_set(v___x_1521_, 1, lean_box(0));
lean_closure_set(v___x_1521_, 2, v___y_1520_);
lean_closure_set(v___x_1521_, 3, v_st_1519_);
v___x_1522_ = lean_apply_2(v_inst_1515_, lean_box(0), v___x_1521_);
v___x_1523_ = lean_apply_4(v_toBind_1516_, lean_box(0), lean_box(0), v___x_1522_, v___f_1517_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object* v_snd_1524_, lean_object* v_waiters_1525_, lean_object* v_capacity_1526_, lean_object* v_size_1527_, lean_object* v_buffer_1528_, lean_object* v_write_1529_, lean_object* v_read_1530_, lean_object* v_receivers_1531_, lean_object* v_nextId_1532_, uint8_t v_closed_1533_, lean_object* v_pos_1534_, lean_object* v___f_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1538_, 0, v_snd_1524_);
lean_ctor_set(v___x_1538_, 1, v_waiters_1525_);
lean_ctor_set(v___x_1538_, 2, v_capacity_1526_);
lean_ctor_set(v___x_1538_, 3, v_size_1527_);
lean_ctor_set(v___x_1538_, 4, v_buffer_1528_);
lean_ctor_set(v___x_1538_, 5, v_write_1529_);
lean_ctor_set(v___x_1538_, 6, v_read_1530_);
lean_ctor_set(v___x_1538_, 7, v_receivers_1531_);
lean_ctor_set(v___x_1538_, 8, v_nextId_1532_);
lean_ctor_set(v___x_1538_, 9, v_pos_1534_);
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*10, v_closed_1533_);
v___x_1539_ = lean_box(0);
v___x_1540_ = lean_apply_3(v___f_1535_, v___x_1539_, v___x_1538_, v_a_1536_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object* v_snd_1541_, lean_object* v_waiters_1542_, lean_object* v_capacity_1543_, lean_object* v_size_1544_, lean_object* v_buffer_1545_, lean_object* v_write_1546_, lean_object* v_read_1547_, lean_object* v_receivers_1548_, lean_object* v_nextId_1549_, lean_object* v_closed_1550_, lean_object* v_pos_1551_, lean_object* v___f_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
uint8_t v_closed_boxed_1555_; lean_object* v_res_1556_; 
v_closed_boxed_1555_ = lean_unbox(v_closed_1550_);
v_res_1556_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1541_, v_waiters_1542_, v_capacity_1543_, v_size_1544_, v_buffer_1545_, v_write_1546_, v_read_1547_, v_receivers_1548_, v_nextId_1549_, v_closed_boxed_1555_, v_pos_1551_, v___f_1552_, v_a_1553_, v_a_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object* v_toApplicative_1557_, lean_object* v_inst_1558_, lean_object* v_toBind_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, uint8_t v___x_1562_, lean_object* v_inst_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_fst_1565_; 
v_fst_1565_ = lean_ctor_get(v_a_1564_, 0);
lean_inc(v_fst_1565_);
if (lean_obj_tag(v_fst_1565_) == 1)
{
lean_object* v_snd_1566_; lean_object* v___f_1567_; lean_object* v___f_1568_; uint8_t v___x_1569_; 
v_snd_1566_ = lean_ctor_get(v_a_1564_, 1);
lean_inc(v_snd_1566_);
lean_dec_ref(v_a_1564_);
v___f_1567_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1567_, 0, v_toApplicative_1557_);
lean_closure_set(v___f_1567_, 1, v_fst_1565_);
lean_inc_ref(v___f_1567_);
lean_inc(v_toBind_1559_);
lean_inc(v_inst_1558_);
v___f_1568_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1), 6, 3);
lean_closure_set(v___f_1568_, 0, v_inst_1558_);
lean_closure_set(v___f_1568_, 1, v_toBind_1559_);
lean_closure_set(v___f_1568_, 2, v___f_1567_);
v___x_1569_ = lean_unbox(v_snd_1566_);
lean_dec(v_snd_1566_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref(v___f_1568_);
lean_dec(v_inst_1563_);
v___x_1570_ = lean_box(0);
v___x_1571_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1558_, v_toBind_1559_, v___f_1567_, v___x_1570_, v_a_1560_, v_a_1561_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; lean_object* v_producers_1573_; lean_object* v_waiters_1574_; lean_object* v_capacity_1575_; lean_object* v_size_1576_; lean_object* v_buffer_1577_; lean_object* v_write_1578_; lean_object* v_read_1579_; lean_object* v_receivers_1580_; lean_object* v_nextId_1581_; uint8_t v_closed_1582_; lean_object* v_pos_1583_; lean_object* v___x_1584_; 
v___x_1572_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_1560_);
v_producers_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_ref(v_producers_1573_);
v_waiters_1574_ = lean_ctor_get(v___x_1572_, 1);
lean_inc_ref(v_waiters_1574_);
v_capacity_1575_ = lean_ctor_get(v___x_1572_, 2);
lean_inc(v_capacity_1575_);
v_size_1576_ = lean_ctor_get(v___x_1572_, 3);
lean_inc(v_size_1576_);
v_buffer_1577_ = lean_ctor_get(v___x_1572_, 4);
lean_inc_ref(v_buffer_1577_);
v_write_1578_ = lean_ctor_get(v___x_1572_, 5);
lean_inc(v_write_1578_);
v_read_1579_ = lean_ctor_get(v___x_1572_, 6);
lean_inc(v_read_1579_);
v_receivers_1580_ = lean_ctor_get(v___x_1572_, 7);
lean_inc(v_receivers_1580_);
v_nextId_1581_ = lean_ctor_get(v___x_1572_, 8);
lean_inc(v_nextId_1581_);
v_closed_1582_ = lean_ctor_get_uint8(v___x_1572_, sizeof(void*)*10);
v_pos_1583_ = lean_ctor_get(v___x_1572_, 9);
lean_inc(v_pos_1583_);
v___x_1584_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1573_);
if (lean_obj_tag(v___x_1584_) == 1)
{
lean_object* v_val_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref(v___x_1572_);
lean_dec_ref(v___f_1567_);
lean_dec(v_inst_1558_);
v_val_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_val_1585_);
lean_dec_ref(v___x_1584_);
v_fst_1586_ = lean_ctor_get(v_val_1585_, 0);
lean_inc(v_fst_1586_);
v_snd_1587_ = lean_ctor_get(v_val_1585_, 1);
lean_inc(v_snd_1587_);
lean_dec(v_val_1585_);
v___x_1588_ = lean_box(v_closed_1582_);
v___f_1589_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1589_, 0, v_snd_1587_);
lean_closure_set(v___f_1589_, 1, v_waiters_1574_);
lean_closure_set(v___f_1589_, 2, v_capacity_1575_);
lean_closure_set(v___f_1589_, 3, v_size_1576_);
lean_closure_set(v___f_1589_, 4, v_buffer_1577_);
lean_closure_set(v___f_1589_, 5, v_write_1578_);
lean_closure_set(v___f_1589_, 6, v_read_1579_);
lean_closure_set(v___f_1589_, 7, v_receivers_1580_);
lean_closure_set(v___f_1589_, 8, v_nextId_1581_);
lean_closure_set(v___f_1589_, 9, v___x_1588_);
lean_closure_set(v___f_1589_, 10, v_pos_1583_);
lean_closure_set(v___f_1589_, 11, v___f_1568_);
lean_closure_set(v___f_1589_, 12, v_a_1561_);
v___x_1590_ = lean_box(v___x_1562_);
v___x_1591_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1591_, 0, lean_box(0));
lean_closure_set(v___x_1591_, 1, v___x_1590_);
lean_closure_set(v___x_1591_, 2, v_fst_1586_);
v___x_1592_ = lean_apply_2(v_inst_1563_, lean_box(0), v___x_1591_);
v___x_1593_ = lean_apply_4(v_toBind_1559_, lean_box(0), lean_box(0), v___x_1592_, v___f_1589_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec(v___x_1584_);
lean_dec(v_pos_1583_);
lean_dec(v_nextId_1581_);
lean_dec(v_receivers_1580_);
lean_dec(v_read_1579_);
lean_dec(v_write_1578_);
lean_dec_ref(v_buffer_1577_);
lean_dec(v_size_1576_);
lean_dec(v_capacity_1575_);
lean_dec_ref(v_waiters_1574_);
lean_dec_ref(v___f_1568_);
lean_dec(v_inst_1563_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1558_, v_toBind_1559_, v___f_1567_, v___x_1594_, v___x_1572_, v_a_1561_);
return v___x_1595_;
}
}
}
else
{
lean_object* v_toPure_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_fst_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_inst_1563_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_toBind_1559_);
lean_dec(v_inst_1558_);
v_toPure_1596_ = lean_ctor_get(v_toApplicative_1557_, 1);
lean_inc(v_toPure_1596_);
lean_dec_ref(v_toApplicative_1557_);
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_apply_2(v_toPure_1596_, lean_box(0), v___x_1597_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object* v_toApplicative_1599_, lean_object* v_inst_1600_, lean_object* v_toBind_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v___x_1604_, lean_object* v_inst_1605_, lean_object* v_a_1606_){
_start:
{
uint8_t v___x_1156__boxed_1607_; lean_object* v_res_1608_; 
v___x_1156__boxed_1607_ = lean_unbox(v___x_1604_);
v_res_1608_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1599_, v_inst_1600_, v_toBind_1601_, v_a_1602_, v_a_1603_, v___x_1156__boxed_1607_, v_inst_1605_, v_a_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object* v_inst_1609_, lean_object* v_next_1610_, lean_object* v_toBind_1611_, lean_object* v___f_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1609_, v_a_1613_, v_next_1610_);
v___x_1615_ = lean_apply_4(v_toBind_1611_, lean_box(0), lean_box(0), v___x_1614_, v___f_1612_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object* v_a_1616_, lean_object* v_toApplicative_1617_, lean_object* v_inst_1618_, lean_object* v_toBind_1619_, lean_object* v_a_1620_, lean_object* v_inst_1621_, lean_object* v_next_1622_, lean_object* v_inst_1623_, uint8_t v_a_1624_){
_start:
{
if (v_a_1624_ == 0)
{
lean_object* v_capacity_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; lean_object* v___f_1628_; lean_object* v___f_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_capacity_1625_ = lean_ctor_get(v_a_1616_, 2);
lean_inc(v_capacity_1625_);
v___x_1626_ = 1;
v___x_1627_ = lean_box(v___x_1626_);
lean_inc(v_a_1620_);
lean_inc(v_toBind_1619_);
lean_inc(v_inst_1618_);
v___f_1628_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1628_, 0, v_toApplicative_1617_);
lean_closure_set(v___f_1628_, 1, v_inst_1618_);
lean_closure_set(v___f_1628_, 2, v_toBind_1619_);
lean_closure_set(v___f_1628_, 3, v_a_1616_);
lean_closure_set(v___f_1628_, 4, v_a_1620_);
lean_closure_set(v___f_1628_, 5, v___x_1627_);
lean_closure_set(v___f_1628_, 6, v_inst_1621_);
lean_inc(v_toBind_1619_);
lean_inc(v_next_1622_);
lean_inc(v_inst_1618_);
v___f_1629_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1629_, 0, v_inst_1618_);
lean_closure_set(v___f_1629_, 1, v_next_1622_);
lean_closure_set(v___f_1629_, 2, v_toBind_1619_);
lean_closure_set(v___f_1629_, 3, v___f_1628_);
v___x_1630_ = lean_nat_mod(v_next_1622_, v_capacity_1625_);
lean_dec(v_capacity_1625_);
lean_dec(v_next_1622_);
v___x_1631_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1623_, v_inst_1618_, v___x_1630_, v_a_1620_);
v___x_1632_ = lean_apply_4(v_toBind_1619_, lean_box(0), lean_box(0), v___x_1631_, v___f_1629_);
return v___x_1632_;
}
else
{
lean_object* v_toPure_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref(v_inst_1623_);
lean_dec(v_next_1622_);
lean_dec(v_inst_1621_);
lean_dec(v_a_1620_);
lean_dec(v_toBind_1619_);
lean_dec(v_inst_1618_);
lean_dec_ref(v_a_1616_);
v_toPure_1633_ = lean_ctor_get(v_toApplicative_1617_, 1);
lean_inc(v_toPure_1633_);
lean_dec_ref(v_toApplicative_1617_);
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_apply_2(v_toPure_1633_, lean_box(0), v___x_1634_);
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object* v_a_1636_, lean_object* v_toApplicative_1637_, lean_object* v_inst_1638_, lean_object* v_toBind_1639_, lean_object* v_a_1640_, lean_object* v_inst_1641_, lean_object* v_next_1642_, lean_object* v_inst_1643_, lean_object* v_a_1644_){
_start:
{
uint8_t v_a_boxed_1645_; lean_object* v_res_1646_; 
v_a_boxed_1645_ = lean_unbox(v_a_1644_);
v_res_1646_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1636_, v_toApplicative_1637_, v_inst_1638_, v_toBind_1639_, v_a_1640_, v_inst_1641_, v_next_1642_, v_inst_1643_, v_a_boxed_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object* v_toApplicative_1647_, lean_object* v_inst_1648_, lean_object* v_toBind_1649_, lean_object* v_a_1650_, lean_object* v_inst_1651_, lean_object* v_next_1652_, lean_object* v_inst_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___f_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_inc_ref(v_inst_1653_);
lean_inc(v_a_1650_);
lean_inc(v_toBind_1649_);
lean_inc(v_inst_1648_);
v___f_1655_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_1655_, 0, v_a_1654_);
lean_closure_set(v___f_1655_, 1, v_toApplicative_1647_);
lean_closure_set(v___f_1655_, 2, v_inst_1648_);
lean_closure_set(v___f_1655_, 3, v_toBind_1649_);
lean_closure_set(v___f_1655_, 4, v_a_1650_);
lean_closure_set(v___f_1655_, 5, v_inst_1651_);
lean_closure_set(v___f_1655_, 6, v_next_1652_);
lean_closure_set(v___f_1655_, 7, v_inst_1653_);
v___x_1656_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_1653_, v_inst_1648_, v_a_1650_);
v___x_1657_ = lean_apply_4(v_toBind_1649_, lean_box(0), lean_box(0), v___x_1656_, v___f_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_next_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_toApplicative_1663_; lean_object* v_toBind_1664_; lean_object* v___f_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v_toApplicative_1663_ = lean_ctor_get(v_inst_1658_, 0);
lean_inc_ref(v_toApplicative_1663_);
v_toBind_1664_ = lean_ctor_get(v_inst_1658_, 1);
lean_inc(v_toBind_1664_);
lean_inc(v_a_1662_);
lean_inc(v_toBind_1664_);
lean_inc(v_inst_1659_);
v___f_1665_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6), 8, 7);
lean_closure_set(v___f_1665_, 0, v_toApplicative_1663_);
lean_closure_set(v___f_1665_, 1, v_inst_1659_);
lean_closure_set(v___f_1665_, 2, v_toBind_1664_);
lean_closure_set(v___f_1665_, 3, v_a_1662_);
lean_closure_set(v___f_1665_, 4, v_inst_1660_);
lean_closure_set(v___f_1665_, 5, v_next_1661_);
lean_closure_set(v___f_1665_, 6, v_inst_1658_);
v___x_1666_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1666_, 0, lean_box(0));
lean_closure_set(v___x_1666_, 1, lean_box(0));
lean_closure_set(v___x_1666_, 2, v_a_1662_);
v___x_1667_ = lean_apply_2(v_inst_1659_, lean_box(0), v___x_1666_);
v___x_1668_ = lean_apply_4(v_toBind_1664_, lean_box(0), lean_box(0), v___x_1667_, v___f_1665_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object* v_m_1669_, lean_object* v_00_u03b1_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_next_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1671_, v_inst_1672_, v_inst_1673_, v_next_1674_, v_a_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_1677_, lean_object* v_k_1678_){
_start:
{
if (lean_obj_tag(v_t_1677_) == 0)
{
lean_object* v_k_1679_; lean_object* v_v_1680_; lean_object* v_l_1681_; lean_object* v_r_1682_; uint8_t v___x_1683_; 
v_k_1679_ = lean_ctor_get(v_t_1677_, 1);
v_v_1680_ = lean_ctor_get(v_t_1677_, 2);
v_l_1681_ = lean_ctor_get(v_t_1677_, 3);
v_r_1682_ = lean_ctor_get(v_t_1677_, 4);
v___x_1683_ = lean_nat_dec_lt(v_k_1678_, v_k_1679_);
if (v___x_1683_ == 0)
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_nat_dec_eq(v_k_1678_, v_k_1679_);
if (v___x_1684_ == 0)
{
v_t_1677_ = v_r_1682_;
goto _start;
}
else
{
lean_object* v___x_1686_; 
lean_inc(v_v_1680_);
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_v_1680_);
return v___x_1686_;
}
}
else
{
v_t_1677_ = v_l_1681_;
goto _start;
}
}
else
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_box(0);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_1689_, lean_object* v_k_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_1689_, v_k_1690_);
lean_dec(v_k_1690_);
lean_dec(v_t_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_1692_, lean_object* v_t_1693_){
_start:
{
if (lean_obj_tag(v_t_1693_) == 0)
{
lean_object* v_k_1694_; lean_object* v_v_1695_; lean_object* v_l_1696_; lean_object* v_r_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_2352_; 
v_k_1694_ = lean_ctor_get(v_t_1693_, 1);
v_v_1695_ = lean_ctor_get(v_t_1693_, 2);
v_l_1696_ = lean_ctor_get(v_t_1693_, 3);
v_r_1697_ = lean_ctor_get(v_t_1693_, 4);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_t_1693_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v_t_1693_, 0);
lean_dec(v_unused_2353_);
v___x_1699_ = v_t_1693_;
v_isShared_1700_ = v_isSharedCheck_2352_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_r_1697_);
lean_inc(v_l_1696_);
lean_inc(v_v_1695_);
lean_inc(v_k_1694_);
lean_dec(v_t_1693_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_2352_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_nat_dec_lt(v_k_1692_, v_k_1694_);
if (v___x_1701_ == 0)
{
uint8_t v___x_1702_; 
v___x_1702_ = lean_nat_dec_eq(v_k_1692_, v_k_1694_);
if (v___x_1702_ == 0)
{
lean_object* v_impl_1703_; lean_object* v___x_1704_; 
v_impl_1703_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1692_, v_r_1697_);
v___x_1704_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1703_) == 0)
{
if (lean_obj_tag(v_l_1696_) == 0)
{
lean_object* v_size_1705_; lean_object* v_size_1706_; lean_object* v_k_1707_; lean_object* v_v_1708_; lean_object* v_l_1709_; lean_object* v_r_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_size_1705_ = lean_ctor_get(v_impl_1703_, 0);
lean_inc(v_size_1705_);
v_size_1706_ = lean_ctor_get(v_l_1696_, 0);
v_k_1707_ = lean_ctor_get(v_l_1696_, 1);
v_v_1708_ = lean_ctor_get(v_l_1696_, 2);
v_l_1709_ = lean_ctor_get(v_l_1696_, 3);
v_r_1710_ = lean_ctor_get(v_l_1696_, 4);
lean_inc(v_r_1710_);
v___x_1711_ = lean_unsigned_to_nat(3u);
v___x_1712_ = lean_nat_mul(v___x_1711_, v_size_1705_);
v___x_1713_ = lean_nat_dec_lt(v___x_1712_, v_size_1706_);
lean_dec(v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
lean_dec(v_r_1710_);
v___x_1714_ = lean_nat_add(v___x_1704_, v_size_1706_);
v___x_1715_ = lean_nat_add(v___x_1714_, v_size_1705_);
lean_dec(v_size_1705_);
lean_dec(v___x_1714_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_impl_1703_);
lean_ctor_set(v___x_1699_, 0, v___x_1715_);
v___x_1717_ = v___x_1699_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_l_1696_);
lean_ctor_set(v_reuseFailAlloc_1718_, 4, v_impl_1703_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
else
{
lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1784_; 
lean_inc(v_l_1709_);
lean_inc(v_v_1708_);
lean_inc(v_k_1707_);
lean_inc(v_size_1706_);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_l_1696_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; lean_object* v_unused_1786_; lean_object* v_unused_1787_; lean_object* v_unused_1788_; lean_object* v_unused_1789_; 
v_unused_1785_ = lean_ctor_get(v_l_1696_, 4);
lean_dec(v_unused_1785_);
v_unused_1786_ = lean_ctor_get(v_l_1696_, 3);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v_l_1696_, 2);
lean_dec(v_unused_1787_);
v_unused_1788_ = lean_ctor_get(v_l_1696_, 1);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v_l_1696_, 0);
lean_dec(v_unused_1789_);
v___x_1720_ = v_l_1696_;
v_isShared_1721_ = v_isSharedCheck_1784_;
goto v_resetjp_1719_;
}
else
{
lean_dec(v_l_1696_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1784_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_size_1722_; lean_object* v_size_1723_; lean_object* v_k_1724_; lean_object* v_v_1725_; lean_object* v_l_1726_; lean_object* v_r_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v_size_1722_ = lean_ctor_get(v_l_1709_, 0);
v_size_1723_ = lean_ctor_get(v_r_1710_, 0);
v_k_1724_ = lean_ctor_get(v_r_1710_, 1);
v_v_1725_ = lean_ctor_get(v_r_1710_, 2);
v_l_1726_ = lean_ctor_get(v_r_1710_, 3);
v_r_1727_ = lean_ctor_get(v_r_1710_, 4);
v___x_1728_ = lean_unsigned_to_nat(2u);
v___x_1729_ = lean_nat_mul(v___x_1728_, v_size_1722_);
v___x_1730_ = lean_nat_dec_lt(v_size_1723_, v___x_1729_);
lean_dec(v___x_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1759_; 
lean_inc(v_r_1727_);
lean_inc(v_l_1726_);
lean_inc(v_v_1725_);
lean_inc(v_k_1724_);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_r_1710_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; lean_object* v_unused_1763_; lean_object* v_unused_1764_; 
v_unused_1760_ = lean_ctor_get(v_r_1710_, 4);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_r_1710_, 3);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_r_1710_, 2);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_r_1710_, 1);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_r_1710_, 0);
lean_dec(v_unused_1764_);
v___x_1732_ = v_r_1710_;
v_isShared_1733_ = v_isSharedCheck_1759_;
goto v_resetjp_1731_;
}
else
{
lean_dec(v_r_1710_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1759_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___x_1747_; lean_object* v___y_1749_; 
v___x_1734_ = lean_nat_add(v___x_1704_, v_size_1706_);
lean_dec(v_size_1706_);
v___x_1735_ = lean_nat_add(v___x_1734_, v_size_1705_);
lean_dec(v___x_1734_);
v___x_1747_ = lean_nat_add(v___x_1704_, v_size_1722_);
if (lean_obj_tag(v_l_1726_) == 0)
{
lean_object* v_size_1757_; 
v_size_1757_ = lean_ctor_get(v_l_1726_, 0);
lean_inc(v_size_1757_);
v___y_1749_ = v_size_1757_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_unsigned_to_nat(0u);
v___y_1749_ = v___x_1758_;
goto v___jp_1748_;
}
v___jp_1736_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_nat_add(v___y_1737_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec(v___y_1737_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 4, v_impl_1703_);
lean_ctor_set(v___x_1732_, 3, v_r_1727_);
lean_ctor_set(v___x_1732_, 2, v_v_1695_);
lean_ctor_set(v___x_1732_, 1, v_k_1694_);
lean_ctor_set(v___x_1732_, 0, v___x_1740_);
v___x_1742_ = v___x_1732_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1746_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1746_, 3, v_r_1727_);
lean_ctor_set(v_reuseFailAlloc_1746_, 4, v_impl_1703_);
v___x_1742_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1744_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v___x_1742_);
lean_ctor_set(v___x_1720_, 3, v___y_1738_);
lean_ctor_set(v___x_1720_, 2, v_v_1725_);
lean_ctor_set(v___x_1720_, 1, v_k_1724_);
lean_ctor_set(v___x_1720_, 0, v___x_1735_);
v___x_1744_ = v___x_1720_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_k_1724_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_v_1725_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v___y_1738_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
v___jp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = lean_nat_add(v___x_1747_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec(v___x_1747_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_l_1726_);
lean_ctor_set(v___x_1699_, 3, v_l_1709_);
lean_ctor_set(v___x_1699_, 2, v_v_1708_);
lean_ctor_set(v___x_1699_, 1, v_k_1707_);
lean_ctor_set(v___x_1699_, 0, v___x_1750_);
v___x_1752_ = v___x_1699_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_l_1709_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_l_1726_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_nat_add(v___x_1704_, v_size_1705_);
lean_dec(v_size_1705_);
if (lean_obj_tag(v_r_1727_) == 0)
{
lean_object* v_size_1754_; 
v_size_1754_ = lean_ctor_get(v_r_1727_, 0);
lean_inc(v_size_1754_);
v___y_1737_ = v___x_1753_;
v___y_1738_ = v___x_1752_;
v___y_1739_ = v_size_1754_;
goto v___jp_1736_;
}
else
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v___y_1737_ = v___x_1753_;
v___y_1738_ = v___x_1752_;
v___y_1739_ = v___x_1755_;
goto v___jp_1736_;
}
}
}
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
lean_del_object(v___x_1699_);
v___x_1765_ = lean_nat_add(v___x_1704_, v_size_1706_);
lean_dec(v_size_1706_);
v___x_1766_ = lean_nat_add(v___x_1765_, v_size_1705_);
lean_dec(v___x_1765_);
v___x_1767_ = lean_nat_add(v___x_1704_, v_size_1705_);
lean_dec(v_size_1705_);
v___x_1768_ = lean_nat_add(v___x_1767_, v_size_1723_);
lean_dec(v___x_1767_);
lean_inc_ref(v_impl_1703_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v_impl_1703_);
lean_ctor_set(v___x_1720_, 3, v_r_1710_);
lean_ctor_set(v___x_1720_, 2, v_v_1695_);
lean_ctor_set(v___x_1720_, 1, v_k_1694_);
lean_ctor_set(v___x_1720_, 0, v___x_1768_);
v___x_1770_ = v___x_1720_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_r_1710_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_impl_1703_);
v___x_1770_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_isSharedCheck_1777_ = !lean_is_exclusive(v_impl_1703_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; lean_object* v_unused_1779_; lean_object* v_unused_1780_; lean_object* v_unused_1781_; lean_object* v_unused_1782_; 
v_unused_1778_ = lean_ctor_get(v_impl_1703_, 4);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v_impl_1703_, 3);
lean_dec(v_unused_1779_);
v_unused_1780_ = lean_ctor_get(v_impl_1703_, 2);
lean_dec(v_unused_1780_);
v_unused_1781_ = lean_ctor_get(v_impl_1703_, 1);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v_impl_1703_, 0);
lean_dec(v_unused_1782_);
v___x_1772_ = v_impl_1703_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v_impl_1703_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 4, v___x_1770_);
lean_ctor_set(v___x_1772_, 3, v_l_1709_);
lean_ctor_set(v___x_1772_, 2, v_v_1708_);
lean_ctor_set(v___x_1772_, 1, v_k_1707_);
lean_ctor_set(v___x_1772_, 0, v___x_1766_);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_k_1707_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_v_1708_);
lean_ctor_set(v_reuseFailAlloc_1776_, 3, v_l_1709_);
lean_ctor_set(v_reuseFailAlloc_1776_, 4, v___x_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v_size_1790_ = lean_ctor_get(v_impl_1703_, 0);
lean_inc(v_size_1790_);
v___x_1791_ = lean_nat_add(v___x_1704_, v_size_1790_);
lean_dec(v_size_1790_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_impl_1703_);
lean_ctor_set(v___x_1699_, 0, v___x_1791_);
v___x_1793_ = v___x_1699_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_l_1696_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_impl_1703_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
if (lean_obj_tag(v_l_1696_) == 0)
{
lean_object* v_l_1795_; 
v_l_1795_ = lean_ctor_get(v_l_1696_, 3);
if (lean_obj_tag(v_l_1795_) == 0)
{
lean_object* v_r_1796_; 
lean_inc_ref(v_l_1795_);
v_r_1796_ = lean_ctor_get(v_l_1696_, 4);
lean_inc(v_r_1796_);
if (lean_obj_tag(v_r_1796_) == 0)
{
lean_object* v_size_1797_; lean_object* v_k_1798_; lean_object* v_v_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1812_; 
v_size_1797_ = lean_ctor_get(v_l_1696_, 0);
v_k_1798_ = lean_ctor_get(v_l_1696_, 1);
v_v_1799_ = lean_ctor_get(v_l_1696_, 2);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_l_1696_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; lean_object* v_unused_1814_; 
v_unused_1813_ = lean_ctor_get(v_l_1696_, 4);
lean_dec(v_unused_1813_);
v_unused_1814_ = lean_ctor_get(v_l_1696_, 3);
lean_dec(v_unused_1814_);
v___x_1801_ = v_l_1696_;
v_isShared_1802_ = v_isSharedCheck_1812_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_v_1799_);
lean_inc(v_k_1798_);
lean_inc(v_size_1797_);
lean_dec(v_l_1696_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1812_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_size_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v_size_1803_ = lean_ctor_get(v_r_1796_, 0);
v___x_1804_ = lean_nat_add(v___x_1704_, v_size_1797_);
lean_dec(v_size_1797_);
v___x_1805_ = lean_nat_add(v___x_1704_, v_size_1803_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 4, v_impl_1703_);
lean_ctor_set(v___x_1801_, 3, v_r_1796_);
lean_ctor_set(v___x_1801_, 2, v_v_1695_);
lean_ctor_set(v___x_1801_, 1, v_k_1694_);
lean_ctor_set(v___x_1801_, 0, v___x_1805_);
v___x_1807_ = v___x_1801_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_r_1796_);
lean_ctor_set(v_reuseFailAlloc_1811_, 4, v_impl_1703_);
v___x_1807_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___x_1807_);
lean_ctor_set(v___x_1699_, 3, v_l_1795_);
lean_ctor_set(v___x_1699_, 2, v_v_1799_);
lean_ctor_set(v___x_1699_, 1, v_k_1798_);
lean_ctor_set(v___x_1699_, 0, v___x_1804_);
v___x_1809_ = v___x_1699_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_k_1798_);
lean_ctor_set(v_reuseFailAlloc_1810_, 2, v_v_1799_);
lean_ctor_set(v_reuseFailAlloc_1810_, 3, v_l_1795_);
lean_ctor_set(v_reuseFailAlloc_1810_, 4, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_k_1815_; lean_object* v_v_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1827_; 
v_k_1815_ = lean_ctor_get(v_l_1696_, 1);
v_v_1816_ = lean_ctor_get(v_l_1696_, 2);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_l_1696_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; lean_object* v_unused_1829_; lean_object* v_unused_1830_; 
v_unused_1828_ = lean_ctor_get(v_l_1696_, 4);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_l_1696_, 3);
lean_dec(v_unused_1829_);
v_unused_1830_ = lean_ctor_get(v_l_1696_, 0);
lean_dec(v_unused_1830_);
v___x_1818_ = v_l_1696_;
v_isShared_1819_ = v_isSharedCheck_1827_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_v_1816_);
lean_inc(v_k_1815_);
lean_dec(v_l_1696_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1827_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_unsigned_to_nat(3u);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 3, v_r_1796_);
lean_ctor_set(v___x_1818_, 2, v_v_1695_);
lean_ctor_set(v___x_1818_, 1, v_k_1694_);
lean_ctor_set(v___x_1818_, 0, v___x_1704_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1826_, 3, v_r_1796_);
lean_ctor_set(v_reuseFailAlloc_1826_, 4, v_r_1796_);
v___x_1822_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___x_1822_);
lean_ctor_set(v___x_1699_, 3, v_l_1795_);
lean_ctor_set(v___x_1699_, 2, v_v_1816_);
lean_ctor_set(v___x_1699_, 1, v_k_1815_);
lean_ctor_set(v___x_1699_, 0, v___x_1820_);
v___x_1824_ = v___x_1699_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_1825_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_1825_, 3, v_l_1795_);
lean_ctor_set(v_reuseFailAlloc_1825_, 4, v___x_1822_);
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
}
else
{
lean_object* v_r_1831_; 
v_r_1831_ = lean_ctor_get(v_l_1696_, 4);
lean_inc(v_r_1831_);
if (lean_obj_tag(v_r_1831_) == 0)
{
lean_object* v_k_1832_; lean_object* v_v_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1856_; 
lean_inc(v_l_1795_);
v_k_1832_ = lean_ctor_get(v_l_1696_, 1);
v_v_1833_ = lean_ctor_get(v_l_1696_, 2);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_l_1696_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; 
v_unused_1857_ = lean_ctor_get(v_l_1696_, 4);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_l_1696_, 3);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_l_1696_, 0);
lean_dec(v_unused_1859_);
v___x_1835_ = v_l_1696_;
v_isShared_1836_ = v_isSharedCheck_1856_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_v_1833_);
lean_inc(v_k_1832_);
lean_dec(v_l_1696_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1856_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_k_1837_; lean_object* v_v_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1852_; 
v_k_1837_ = lean_ctor_get(v_r_1831_, 1);
v_v_1838_ = lean_ctor_get(v_r_1831_, 2);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_r_1831_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; 
v_unused_1853_ = lean_ctor_get(v_r_1831_, 4);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_r_1831_, 3);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_r_1831_, 0);
lean_dec(v_unused_1855_);
v___x_1840_ = v_r_1831_;
v_isShared_1841_ = v_isSharedCheck_1852_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_v_1838_);
lean_inc(v_k_1837_);
lean_dec(v_r_1831_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1852_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_unsigned_to_nat(3u);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 4, v_l_1795_);
lean_ctor_set(v___x_1840_, 3, v_l_1795_);
lean_ctor_set(v___x_1840_, 2, v_v_1833_);
lean_ctor_set(v___x_1840_, 1, v_k_1832_);
lean_ctor_set(v___x_1840_, 0, v___x_1704_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_k_1832_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_v_1833_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_l_1795_);
lean_ctor_set(v_reuseFailAlloc_1851_, 4, v_l_1795_);
v___x_1844_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 4, v_l_1795_);
lean_ctor_set(v___x_1835_, 2, v_v_1695_);
lean_ctor_set(v___x_1835_, 1, v_k_1694_);
lean_ctor_set(v___x_1835_, 0, v___x_1704_);
v___x_1846_ = v___x_1835_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_l_1795_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_l_1795_);
v___x_1846_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___x_1846_);
lean_ctor_set(v___x_1699_, 3, v___x_1844_);
lean_ctor_set(v___x_1699_, 2, v_v_1838_);
lean_ctor_set(v___x_1699_, 1, v_k_1837_);
lean_ctor_set(v___x_1699_, 0, v___x_1842_);
v___x_1848_ = v___x_1699_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_k_1837_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_v_1838_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1849_, 4, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1860_ = lean_unsigned_to_nat(2u);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_r_1831_);
lean_ctor_set(v___x_1699_, 0, v___x_1860_);
v___x_1862_ = v___x_1699_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v_l_1696_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v_r_1831_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v___x_1865_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_l_1696_);
lean_ctor_set(v___x_1699_, 0, v___x_1704_);
v___x_1865_ = v___x_1699_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_l_1696_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_l_1696_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_del_object(v___x_1699_);
lean_dec(v_v_1695_);
lean_dec(v_k_1694_);
if (lean_obj_tag(v_l_1696_) == 0)
{
if (lean_obj_tag(v_r_1697_) == 0)
{
lean_object* v_size_1867_; lean_object* v_k_1868_; lean_object* v_v_1869_; lean_object* v_l_1870_; lean_object* v_r_1871_; lean_object* v_size_1872_; lean_object* v_k_1873_; lean_object* v_v_1874_; lean_object* v_l_1875_; lean_object* v_r_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v_size_1867_ = lean_ctor_get(v_l_1696_, 0);
v_k_1868_ = lean_ctor_get(v_l_1696_, 1);
v_v_1869_ = lean_ctor_get(v_l_1696_, 2);
v_l_1870_ = lean_ctor_get(v_l_1696_, 3);
v_r_1871_ = lean_ctor_get(v_l_1696_, 4);
lean_inc(v_r_1871_);
v_size_1872_ = lean_ctor_get(v_r_1697_, 0);
v_k_1873_ = lean_ctor_get(v_r_1697_, 1);
v_v_1874_ = lean_ctor_get(v_r_1697_, 2);
v_l_1875_ = lean_ctor_get(v_r_1697_, 3);
lean_inc(v_l_1875_);
v_r_1876_ = lean_ctor_get(v_r_1697_, 4);
v___x_1877_ = lean_unsigned_to_nat(1u);
v___x_1878_ = lean_nat_dec_lt(v_size_1867_, v_size_1872_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_2014_; 
lean_inc(v_l_1870_);
lean_inc(v_v_1869_);
lean_inc(v_k_1868_);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_l_1696_);
if (v_isSharedCheck_2014_ == 0)
{
lean_object* v_unused_2015_; lean_object* v_unused_2016_; lean_object* v_unused_2017_; lean_object* v_unused_2018_; lean_object* v_unused_2019_; 
v_unused_2015_ = lean_ctor_get(v_l_1696_, 4);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_l_1696_, 3);
lean_dec(v_unused_2016_);
v_unused_2017_ = lean_ctor_get(v_l_1696_, 2);
lean_dec(v_unused_2017_);
v_unused_2018_ = lean_ctor_get(v_l_1696_, 1);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_l_1696_, 0);
lean_dec(v_unused_2019_);
v___x_1880_ = v_l_1696_;
v_isShared_1881_ = v_isSharedCheck_2014_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v_l_1696_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_2014_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v_tree_1883_; 
v___x_1882_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1868_, v_v_1869_, v_l_1870_, v_r_1871_);
v_tree_1883_ = lean_ctor_get(v___x_1882_, 2);
lean_inc(v_tree_1883_);
if (lean_obj_tag(v_tree_1883_) == 0)
{
lean_object* v_k_1884_; lean_object* v_v_1885_; lean_object* v_size_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v_k_1884_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_k_1884_);
v_v_1885_ = lean_ctor_get(v___x_1882_, 1);
lean_inc(v_v_1885_);
lean_dec_ref(v___x_1882_);
v_size_1886_ = lean_ctor_get(v_tree_1883_, 0);
v___x_1887_ = lean_unsigned_to_nat(3u);
v___x_1888_ = lean_nat_mul(v___x_1887_, v_size_1886_);
v___x_1889_ = lean_nat_dec_lt(v___x_1888_, v_size_1872_);
lean_dec(v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1893_; 
lean_dec(v_l_1875_);
v___x_1890_ = lean_nat_add(v___x_1877_, v_size_1886_);
v___x_1891_ = lean_nat_add(v___x_1890_, v_size_1872_);
lean_dec(v___x_1890_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v_r_1697_);
lean_ctor_set(v___x_1880_, 3, v_tree_1883_);
lean_ctor_set(v___x_1880_, 2, v_v_1885_);
lean_ctor_set(v___x_1880_, 1, v_k_1884_);
lean_ctor_set(v___x_1880_, 0, v___x_1891_);
v___x_1893_ = v___x_1880_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_k_1884_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_v_1885_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_tree_1883_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_r_1697_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1949_; 
lean_inc(v_r_1876_);
lean_inc(v_v_1874_);
lean_inc(v_k_1873_);
lean_inc(v_size_1872_);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_r_1697_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; lean_object* v_unused_1951_; lean_object* v_unused_1952_; lean_object* v_unused_1953_; lean_object* v_unused_1954_; 
v_unused_1950_ = lean_ctor_get(v_r_1697_, 4);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_r_1697_, 3);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_r_1697_, 2);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_r_1697_, 1);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_r_1697_, 0);
lean_dec(v_unused_1954_);
v___x_1896_ = v_r_1697_;
v_isShared_1897_ = v_isSharedCheck_1949_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v_r_1697_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1949_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_size_1898_; lean_object* v_k_1899_; lean_object* v_v_1900_; lean_object* v_l_1901_; lean_object* v_r_1902_; lean_object* v_size_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v_size_1898_ = lean_ctor_get(v_l_1875_, 0);
v_k_1899_ = lean_ctor_get(v_l_1875_, 1);
v_v_1900_ = lean_ctor_get(v_l_1875_, 2);
v_l_1901_ = lean_ctor_get(v_l_1875_, 3);
v_r_1902_ = lean_ctor_get(v_l_1875_, 4);
v_size_1903_ = lean_ctor_get(v_r_1876_, 0);
v___x_1904_ = lean_unsigned_to_nat(2u);
v___x_1905_ = lean_nat_mul(v___x_1904_, v_size_1903_);
v___x_1906_ = lean_nat_dec_lt(v_size_1898_, v___x_1905_);
lean_dec(v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1934_; 
lean_inc(v_r_1902_);
lean_inc(v_l_1901_);
lean_inc(v_v_1900_);
lean_inc(v_k_1899_);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_l_1875_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; lean_object* v_unused_1936_; lean_object* v_unused_1937_; lean_object* v_unused_1938_; lean_object* v_unused_1939_; 
v_unused_1935_ = lean_ctor_get(v_l_1875_, 4);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_l_1875_, 3);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_l_1875_, 2);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_l_1875_, 1);
lean_dec(v_unused_1938_);
v_unused_1939_ = lean_ctor_get(v_l_1875_, 0);
lean_dec(v_unused_1939_);
v___x_1908_ = v_l_1875_;
v_isShared_1909_ = v_isSharedCheck_1934_;
goto v_resetjp_1907_;
}
else
{
lean_dec(v_l_1875_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1934_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1924_; 
v___x_1910_ = lean_nat_add(v___x_1877_, v_size_1886_);
v___x_1911_ = lean_nat_add(v___x_1910_, v_size_1872_);
lean_dec(v_size_1872_);
if (lean_obj_tag(v_l_1901_) == 0)
{
lean_object* v_size_1932_; 
v_size_1932_ = lean_ctor_get(v_l_1901_, 0);
lean_inc(v_size_1932_);
v___y_1924_ = v_size_1932_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_unsigned_to_nat(0u);
v___y_1924_ = v___x_1933_;
goto v___jp_1923_;
}
v___jp_1912_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = lean_nat_add(v___y_1913_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec(v___y_1913_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 4, v_r_1876_);
lean_ctor_set(v___x_1908_, 3, v_r_1902_);
lean_ctor_set(v___x_1908_, 2, v_v_1874_);
lean_ctor_set(v___x_1908_, 1, v_k_1873_);
lean_ctor_set(v___x_1908_, 0, v___x_1916_);
v___x_1918_ = v___x_1908_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_k_1873_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_v_1874_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_r_1902_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v_r_1876_);
v___x_1918_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 4, v___x_1918_);
lean_ctor_set(v___x_1896_, 3, v___y_1914_);
lean_ctor_set(v___x_1896_, 2, v_v_1900_);
lean_ctor_set(v___x_1896_, 1, v_k_1899_);
lean_ctor_set(v___x_1896_, 0, v___x_1911_);
v___x_1920_ = v___x_1896_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1899_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1900_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v___y_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
v___jp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_nat_add(v___x_1910_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec(v___x_1910_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v_l_1901_);
lean_ctor_set(v___x_1880_, 3, v_tree_1883_);
lean_ctor_set(v___x_1880_, 2, v_v_1885_);
lean_ctor_set(v___x_1880_, 1, v_k_1884_);
lean_ctor_set(v___x_1880_, 0, v___x_1925_);
v___x_1927_ = v___x_1880_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_k_1884_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_v_1885_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_tree_1883_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_l_1901_);
v___x_1927_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_nat_add(v___x_1877_, v_size_1903_);
if (lean_obj_tag(v_r_1902_) == 0)
{
lean_object* v_size_1929_; 
v_size_1929_ = lean_ctor_get(v_r_1902_, 0);
lean_inc(v_size_1929_);
v___y_1913_ = v___x_1928_;
v___y_1914_ = v___x_1927_;
v___y_1915_ = v_size_1929_;
goto v___jp_1912_;
}
else
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_unsigned_to_nat(0u);
v___y_1913_ = v___x_1928_;
v___y_1914_ = v___x_1927_;
v___y_1915_ = v___x_1930_;
goto v___jp_1912_;
}
}
}
}
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1940_ = lean_nat_add(v___x_1877_, v_size_1886_);
v___x_1941_ = lean_nat_add(v___x_1940_, v_size_1872_);
lean_dec(v_size_1872_);
v___x_1942_ = lean_nat_add(v___x_1940_, v_size_1898_);
lean_dec(v___x_1940_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 4, v_l_1875_);
lean_ctor_set(v___x_1896_, 3, v_tree_1883_);
lean_ctor_set(v___x_1896_, 2, v_v_1885_);
lean_ctor_set(v___x_1896_, 1, v_k_1884_);
lean_ctor_set(v___x_1896_, 0, v___x_1942_);
v___x_1944_ = v___x_1896_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_k_1884_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_v_1885_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_tree_1883_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_l_1875_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v_r_1876_);
lean_ctor_set(v___x_1880_, 3, v___x_1944_);
lean_ctor_set(v___x_1880_, 2, v_v_1874_);
lean_ctor_set(v___x_1880_, 1, v_k_1873_);
lean_ctor_set(v___x_1880_, 0, v___x_1941_);
v___x_1946_ = v___x_1880_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1873_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1874_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_r_1876_);
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
}
}
else
{
lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2008_; 
lean_inc(v_r_1876_);
lean_inc(v_v_1874_);
lean_inc(v_k_1873_);
lean_inc(v_size_1872_);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_r_1697_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; lean_object* v_unused_2010_; lean_object* v_unused_2011_; lean_object* v_unused_2012_; lean_object* v_unused_2013_; 
v_unused_2009_ = lean_ctor_get(v_r_1697_, 4);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_r_1697_, 3);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_r_1697_, 2);
lean_dec(v_unused_2011_);
v_unused_2012_ = lean_ctor_get(v_r_1697_, 1);
lean_dec(v_unused_2012_);
v_unused_2013_ = lean_ctor_get(v_r_1697_, 0);
lean_dec(v_unused_2013_);
v___x_1956_ = v_r_1697_;
v_isShared_1957_ = v_isSharedCheck_2008_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v_r_1697_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2008_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
if (lean_obj_tag(v_l_1875_) == 0)
{
if (lean_obj_tag(v_r_1876_) == 0)
{
lean_object* v_k_1958_; lean_object* v_v_1959_; lean_object* v_size_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v_k_1958_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_k_1958_);
v_v_1959_ = lean_ctor_get(v___x_1882_, 1);
lean_inc(v_v_1959_);
lean_dec_ref(v___x_1882_);
v_size_1960_ = lean_ctor_get(v_l_1875_, 0);
v___x_1961_ = lean_nat_add(v___x_1877_, v_size_1872_);
lean_dec(v_size_1872_);
v___x_1962_ = lean_nat_add(v___x_1877_, v_size_1960_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 4, v_l_1875_);
lean_ctor_set(v___x_1956_, 3, v_tree_1883_);
lean_ctor_set(v___x_1956_, 2, v_v_1959_);
lean_ctor_set(v___x_1956_, 1, v_k_1958_);
lean_ctor_set(v___x_1956_, 0, v___x_1962_);
v___x_1964_ = v___x_1956_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_k_1958_);
lean_ctor_set(v_reuseFailAlloc_1968_, 2, v_v_1959_);
lean_ctor_set(v_reuseFailAlloc_1968_, 3, v_tree_1883_);
lean_ctor_set(v_reuseFailAlloc_1968_, 4, v_l_1875_);
v___x_1964_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v_r_1876_);
lean_ctor_set(v___x_1880_, 3, v___x_1964_);
lean_ctor_set(v___x_1880_, 2, v_v_1874_);
lean_ctor_set(v___x_1880_, 1, v_k_1873_);
lean_ctor_set(v___x_1880_, 0, v___x_1961_);
v___x_1966_ = v___x_1880_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_k_1873_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_v_1874_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_r_1876_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
else
{
lean_object* v_k_1969_; lean_object* v_v_1970_; lean_object* v_k_1971_; lean_object* v_v_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v_size_1872_);
v_k_1969_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_k_1969_);
v_v_1970_ = lean_ctor_get(v___x_1882_, 1);
lean_inc(v_v_1970_);
lean_dec_ref(v___x_1882_);
v_k_1971_ = lean_ctor_get(v_l_1875_, 1);
v_v_1972_ = lean_ctor_get(v_l_1875_, 2);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_l_1875_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; lean_object* v_unused_1989_; 
v_unused_1987_ = lean_ctor_get(v_l_1875_, 4);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_l_1875_, 3);
lean_dec(v_unused_1988_);
v_unused_1989_ = lean_ctor_get(v_l_1875_, 0);
lean_dec(v_unused_1989_);
v___x_1974_ = v_l_1875_;
v_isShared_1975_ = v_isSharedCheck_1986_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_v_1972_);
lean_inc(v_k_1971_);
lean_dec(v_l_1875_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1986_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_unsigned_to_nat(3u);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 4, v_r_1876_);
lean_ctor_set(v___x_1974_, 3, v_r_1876_);
lean_ctor_set(v___x_1974_, 2, v_v_1970_);
lean_ctor_set(v___x_1974_, 1, v_k_1969_);
lean_ctor_set(v___x_1974_, 0, v___x_1877_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_k_1969_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_v_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_r_1876_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v_r_1876_);
v___x_1978_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1980_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 3, v_r_1876_);
lean_ctor_set(v___x_1956_, 0, v___x_1877_);
v___x_1980_ = v___x_1956_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_k_1873_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_v_1874_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v_r_1876_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v_r_1876_);
v___x_1980_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v___x_1980_);
lean_ctor_set(v___x_1880_, 3, v___x_1978_);
lean_ctor_set(v___x_1880_, 2, v_v_1972_);
lean_ctor_set(v___x_1880_, 1, v_k_1971_);
lean_ctor_set(v___x_1880_, 0, v___x_1976_);
v___x_1982_ = v___x_1880_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_k_1971_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_v_1972_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1876_) == 0)
{
lean_object* v_k_1990_; lean_object* v_v_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
lean_dec(v_size_1872_);
v_k_1990_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_k_1990_);
v_v_1991_ = lean_ctor_get(v___x_1882_, 1);
lean_inc(v_v_1991_);
lean_dec_ref(v___x_1882_);
v___x_1992_ = lean_unsigned_to_nat(3u);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 4, v_l_1875_);
lean_ctor_set(v___x_1956_, 2, v_v_1991_);
lean_ctor_set(v___x_1956_, 1, v_k_1990_);
lean_ctor_set(v___x_1956_, 0, v___x_1877_);
v___x_1994_ = v___x_1956_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_k_1990_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_v_1991_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v_l_1875_);
lean_ctor_set(v_reuseFailAlloc_1998_, 4, v_l_1875_);
v___x_1994_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v_r_1876_);
lean_ctor_set(v___x_1880_, 3, v___x_1994_);
lean_ctor_set(v___x_1880_, 2, v_v_1874_);
lean_ctor_set(v___x_1880_, 1, v_k_1873_);
lean_ctor_set(v___x_1880_, 0, v___x_1992_);
v___x_1996_ = v___x_1880_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_k_1873_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v_v_1874_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1997_, 4, v_r_1876_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
else
{
lean_object* v_k_1999_; lean_object* v_v_2000_; lean_object* v___x_2002_; 
v_k_1999_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_k_1999_);
v_v_2000_ = lean_ctor_get(v___x_1882_, 1);
lean_inc(v_v_2000_);
lean_dec_ref(v___x_1882_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 3, v_r_1876_);
v___x_2002_ = v___x_1956_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_size_1872_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_k_1873_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_v_1874_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_r_1876_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_r_1876_);
v___x_2002_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_unsigned_to_nat(2u);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v___x_2002_);
lean_ctor_set(v___x_1880_, 3, v_r_1876_);
lean_ctor_set(v___x_1880_, 2, v_v_2000_);
lean_ctor_set(v___x_1880_, 1, v_k_1999_);
lean_ctor_set(v___x_1880_, 0, v___x_2003_);
v___x_2005_ = v___x_1880_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_k_1999_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_v_2000_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v_r_1876_);
lean_ctor_set(v_reuseFailAlloc_2006_, 4, v___x_2002_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
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
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2172_; 
lean_inc(v_r_1876_);
lean_inc(v_v_1874_);
lean_inc(v_k_1873_);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_r_1697_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; 
v_unused_2173_ = lean_ctor_get(v_r_1697_, 4);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_r_1697_, 3);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_r_1697_, 2);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_r_1697_, 1);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_r_1697_, 0);
lean_dec(v_unused_2177_);
v___x_2021_ = v_r_1697_;
v_isShared_2022_ = v_isSharedCheck_2172_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v_r_1697_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2172_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v_tree_2024_; 
v___x_2023_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1873_, v_v_1874_, v_l_1875_, v_r_1876_);
v_tree_2024_ = lean_ctor_get(v___x_2023_, 2);
lean_inc(v_tree_2024_);
if (lean_obj_tag(v_tree_2024_) == 0)
{
lean_object* v_k_2025_; lean_object* v_v_2026_; lean_object* v_size_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_k_2025_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_k_2025_);
v_v_2026_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_v_2026_);
lean_dec_ref(v___x_2023_);
v_size_2027_ = lean_ctor_get(v_tree_2024_, 0);
v___x_2028_ = lean_unsigned_to_nat(3u);
v___x_2029_ = lean_nat_mul(v___x_2028_, v_size_2027_);
v___x_2030_ = lean_nat_dec_lt(v___x_2029_, v_size_1867_);
lean_dec(v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
lean_dec(v_r_1871_);
v___x_2031_ = lean_nat_add(v___x_1877_, v_size_1867_);
v___x_2032_ = lean_nat_add(v___x_2031_, v_size_2027_);
lean_dec(v___x_2031_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v_tree_2024_);
lean_ctor_set(v___x_2021_, 3, v_l_1696_);
lean_ctor_set(v___x_2021_, 2, v_v_2026_);
lean_ctor_set(v___x_2021_, 1, v_k_2025_);
lean_ctor_set(v___x_2021_, 0, v___x_2032_);
v___x_2034_ = v___x_2021_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_k_2025_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_v_2026_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v_l_1696_);
lean_ctor_set(v_reuseFailAlloc_2035_, 4, v_tree_2024_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
else
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2101_; 
lean_inc(v_l_1870_);
lean_inc(v_v_1869_);
lean_inc(v_k_1868_);
lean_inc(v_size_1867_);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_l_1696_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; lean_object* v_unused_2103_; lean_object* v_unused_2104_; lean_object* v_unused_2105_; lean_object* v_unused_2106_; 
v_unused_2102_ = lean_ctor_get(v_l_1696_, 4);
lean_dec(v_unused_2102_);
v_unused_2103_ = lean_ctor_get(v_l_1696_, 3);
lean_dec(v_unused_2103_);
v_unused_2104_ = lean_ctor_get(v_l_1696_, 2);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_l_1696_, 1);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_l_1696_, 0);
lean_dec(v_unused_2106_);
v___x_2037_ = v_l_1696_;
v_isShared_2038_ = v_isSharedCheck_2101_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v_l_1696_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2101_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_size_2039_; lean_object* v_size_2040_; lean_object* v_k_2041_; lean_object* v_v_2042_; lean_object* v_l_2043_; lean_object* v_r_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_size_2039_ = lean_ctor_get(v_l_1870_, 0);
v_size_2040_ = lean_ctor_get(v_r_1871_, 0);
v_k_2041_ = lean_ctor_get(v_r_1871_, 1);
v_v_2042_ = lean_ctor_get(v_r_1871_, 2);
v_l_2043_ = lean_ctor_get(v_r_1871_, 3);
v_r_2044_ = lean_ctor_get(v_r_1871_, 4);
v___x_2045_ = lean_unsigned_to_nat(2u);
v___x_2046_ = lean_nat_mul(v___x_2045_, v_size_2039_);
v___x_2047_ = lean_nat_dec_lt(v_size_2040_, v___x_2046_);
lean_dec(v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2085_; 
lean_inc(v_r_2044_);
lean_inc(v_l_2043_);
lean_inc(v_v_2042_);
lean_inc(v_k_2041_);
lean_del_object(v___x_2037_);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_r_1871_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; lean_object* v_unused_2087_; lean_object* v_unused_2088_; lean_object* v_unused_2089_; lean_object* v_unused_2090_; 
v_unused_2086_ = lean_ctor_get(v_r_1871_, 4);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v_r_1871_, 3);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_r_1871_, 2);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_r_1871_, 1);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_r_1871_, 0);
lean_dec(v_unused_2090_);
v___x_2049_ = v_r_1871_;
v_isShared_2050_ = v_isSharedCheck_2085_;
goto v_resetjp_2048_;
}
else
{
lean_dec(v_r_1871_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2085_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___x_2073_; lean_object* v___y_2075_; 
v___x_2051_ = lean_nat_add(v___x_1877_, v_size_1867_);
lean_dec(v_size_1867_);
v___x_2052_ = lean_nat_add(v___x_2051_, v_size_2027_);
lean_dec(v___x_2051_);
v___x_2073_ = lean_nat_add(v___x_1877_, v_size_2039_);
if (lean_obj_tag(v_l_2043_) == 0)
{
lean_object* v_size_2083_; 
v_size_2083_ = lean_ctor_get(v_l_2043_, 0);
lean_inc(v_size_2083_);
v___y_2075_ = v_size_2083_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___y_2075_ = v___x_2084_;
goto v___jp_2074_;
}
v___jp_2053_:
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2057_ = lean_nat_add(v___y_2054_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec(v___y_2054_);
lean_inc_ref(v_tree_2024_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 4, v_tree_2024_);
lean_ctor_set(v___x_2049_, 3, v_r_2044_);
lean_ctor_set(v___x_2049_, 2, v_v_2026_);
lean_ctor_set(v___x_2049_, 1, v_k_2025_);
lean_ctor_set(v___x_2049_, 0, v___x_2057_);
v___x_2059_ = v___x_2049_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_k_2025_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_v_2026_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v_r_2044_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v_tree_2024_);
v___x_2059_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_isSharedCheck_2066_ = !lean_is_exclusive(v_tree_2024_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; lean_object* v_unused_2068_; lean_object* v_unused_2069_; lean_object* v_unused_2070_; lean_object* v_unused_2071_; 
v_unused_2067_ = lean_ctor_get(v_tree_2024_, 4);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v_tree_2024_, 3);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v_tree_2024_, 2);
lean_dec(v_unused_2069_);
v_unused_2070_ = lean_ctor_get(v_tree_2024_, 1);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_tree_2024_, 0);
lean_dec(v_unused_2071_);
v___x_2061_ = v_tree_2024_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v_tree_2024_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v___x_2059_);
lean_ctor_set(v___x_2061_, 3, v___y_2055_);
lean_ctor_set(v___x_2061_, 2, v_v_2042_);
lean_ctor_set(v___x_2061_, 1, v_k_2041_);
lean_ctor_set(v___x_2061_, 0, v___x_2052_);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_k_2041_);
lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_v_2042_);
lean_ctor_set(v_reuseFailAlloc_2065_, 3, v___y_2055_);
lean_ctor_set(v_reuseFailAlloc_2065_, 4, v___x_2059_);
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
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_nat_add(v___x_2073_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec(v___x_2073_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v_l_2043_);
lean_ctor_set(v___x_2021_, 3, v_l_1870_);
lean_ctor_set(v___x_2021_, 2, v_v_1869_);
lean_ctor_set(v___x_2021_, 1, v_k_1868_);
lean_ctor_set(v___x_2021_, 0, v___x_2076_);
v___x_2078_ = v___x_2021_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_k_1868_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_v_1869_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_l_1870_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_l_2043_);
v___x_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_nat_add(v___x_1877_, v_size_2027_);
if (lean_obj_tag(v_r_2044_) == 0)
{
lean_object* v_size_2080_; 
v_size_2080_ = lean_ctor_get(v_r_2044_, 0);
lean_inc(v_size_2080_);
v___y_2054_ = v___x_2079_;
v___y_2055_ = v___x_2078_;
v___y_2056_ = v_size_2080_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_unsigned_to_nat(0u);
v___y_2054_ = v___x_2079_;
v___y_2055_ = v___x_2078_;
v___y_2056_ = v___x_2081_;
goto v___jp_2053_;
}
}
}
}
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2091_ = lean_nat_add(v___x_1877_, v_size_1867_);
lean_dec(v_size_1867_);
v___x_2092_ = lean_nat_add(v___x_2091_, v_size_2027_);
lean_dec(v___x_2091_);
v___x_2093_ = lean_nat_add(v___x_1877_, v_size_2027_);
v___x_2094_ = lean_nat_add(v___x_2093_, v_size_2040_);
lean_dec(v___x_2093_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v_tree_2024_);
lean_ctor_set(v___x_2021_, 3, v_r_1871_);
lean_ctor_set(v___x_2021_, 2, v_v_2026_);
lean_ctor_set(v___x_2021_, 1, v_k_2025_);
lean_ctor_set(v___x_2021_, 0, v___x_2094_);
v___x_2096_ = v___x_2021_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_k_2025_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_v_2026_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v_r_1871_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v_tree_2024_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2098_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 4, v___x_2096_);
lean_ctor_set(v___x_2037_, 0, v___x_2092_);
v___x_2098_ = v___x_2037_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_k_1868_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_v_1869_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_l_1870_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1870_) == 0)
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2130_; 
lean_inc_ref(v_l_1870_);
lean_inc(v_v_1869_);
lean_inc(v_k_1868_);
lean_inc(v_size_1867_);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_l_1696_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; lean_object* v_unused_2132_; lean_object* v_unused_2133_; lean_object* v_unused_2134_; lean_object* v_unused_2135_; 
v_unused_2131_ = lean_ctor_get(v_l_1696_, 4);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_l_1696_, 3);
lean_dec(v_unused_2132_);
v_unused_2133_ = lean_ctor_get(v_l_1696_, 2);
lean_dec(v_unused_2133_);
v_unused_2134_ = lean_ctor_get(v_l_1696_, 1);
lean_dec(v_unused_2134_);
v_unused_2135_ = lean_ctor_get(v_l_1696_, 0);
lean_dec(v_unused_2135_);
v___x_2108_ = v_l_1696_;
v_isShared_2109_ = v_isSharedCheck_2130_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v_l_1696_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2130_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
if (lean_obj_tag(v_r_1871_) == 0)
{
lean_object* v_k_2110_; lean_object* v_v_2111_; lean_object* v_size_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v_k_2110_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_k_2110_);
v_v_2111_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_v_2111_);
lean_dec_ref(v___x_2023_);
v_size_2112_ = lean_ctor_get(v_r_1871_, 0);
v___x_2113_ = lean_nat_add(v___x_1877_, v_size_1867_);
lean_dec(v_size_1867_);
v___x_2114_ = lean_nat_add(v___x_1877_, v_size_2112_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v_tree_2024_);
lean_ctor_set(v___x_2021_, 3, v_r_1871_);
lean_ctor_set(v___x_2021_, 2, v_v_2111_);
lean_ctor_set(v___x_2021_, 1, v_k_2110_);
lean_ctor_set(v___x_2021_, 0, v___x_2114_);
v___x_2116_ = v___x_2021_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_k_2110_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_v_2111_);
lean_ctor_set(v_reuseFailAlloc_2120_, 3, v_r_1871_);
lean_ctor_set(v_reuseFailAlloc_2120_, 4, v_tree_2024_);
v___x_2116_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2118_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 4, v___x_2116_);
lean_ctor_set(v___x_2108_, 0, v___x_2113_);
v___x_2118_ = v___x_2108_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_k_1868_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_v_1869_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_l_1870_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_object* v_k_2121_; lean_object* v_v_2122_; lean_object* v___x_2123_; lean_object* v___x_2125_; 
lean_dec(v_size_1867_);
v_k_2121_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_k_2121_);
v_v_2122_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_v_2122_);
lean_dec_ref(v___x_2023_);
v___x_2123_ = lean_unsigned_to_nat(3u);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v_r_1871_);
lean_ctor_set(v___x_2021_, 3, v_r_1871_);
lean_ctor_set(v___x_2021_, 2, v_v_2122_);
lean_ctor_set(v___x_2021_, 1, v_k_2121_);
lean_ctor_set(v___x_2021_, 0, v___x_1877_);
v___x_2125_ = v___x_2021_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_r_1871_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_r_1871_);
v___x_2125_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2127_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 4, v___x_2125_);
lean_ctor_set(v___x_2108_, 0, v___x_2123_);
v___x_2127_ = v___x_2108_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_k_1868_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_1869_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_l_1870_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1871_) == 0)
{
lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2160_; 
lean_inc(v_l_1870_);
lean_inc(v_v_1869_);
lean_inc(v_k_1868_);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_l_1696_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; lean_object* v_unused_2163_; lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2161_ = lean_ctor_get(v_l_1696_, 4);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_l_1696_, 3);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_l_1696_, 2);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_l_1696_, 1);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_l_1696_, 0);
lean_dec(v_unused_2165_);
v___x_2137_ = v_l_1696_;
v_isShared_2138_ = v_isSharedCheck_2160_;
goto v_resetjp_2136_;
}
else
{
lean_dec(v_l_1696_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2160_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_k_2139_; lean_object* v_v_2140_; lean_object* v_k_2141_; lean_object* v_v_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2156_; 
v_k_2139_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_k_2139_);
v_v_2140_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_v_2140_);
lean_dec_ref(v___x_2023_);
v_k_2141_ = lean_ctor_get(v_r_1871_, 1);
v_v_2142_ = lean_ctor_get(v_r_1871_, 2);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_r_1871_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; lean_object* v_unused_2158_; lean_object* v_unused_2159_; 
v_unused_2157_ = lean_ctor_get(v_r_1871_, 4);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_r_1871_, 3);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_r_1871_, 0);
lean_dec(v_unused_2159_);
v___x_2144_ = v_r_1871_;
v_isShared_2145_ = v_isSharedCheck_2156_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_v_2142_);
lean_inc(v_k_2141_);
lean_dec(v_r_1871_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2156_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_unsigned_to_nat(3u);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v_l_1870_);
lean_ctor_set(v___x_2144_, 3, v_l_1870_);
lean_ctor_set(v___x_2144_, 2, v_v_1869_);
lean_ctor_set(v___x_2144_, 1, v_k_1868_);
lean_ctor_set(v___x_2144_, 0, v___x_1877_);
v___x_2148_ = v___x_2144_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_1868_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_1869_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_l_1870_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_l_1870_);
v___x_2148_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v_l_1870_);
lean_ctor_set(v___x_2021_, 3, v_l_1870_);
lean_ctor_set(v___x_2021_, 2, v_v_2140_);
lean_ctor_set(v___x_2021_, 1, v_k_2139_);
lean_ctor_set(v___x_2021_, 0, v___x_1877_);
v___x_2150_ = v___x_2021_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_l_1870_);
lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_l_1870_);
v___x_2150_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 4, v___x_2150_);
lean_ctor_set(v___x_2137_, 3, v___x_2148_);
lean_ctor_set(v___x_2137_, 2, v_v_2142_);
lean_ctor_set(v___x_2137_, 1, v_k_2141_);
lean_ctor_set(v___x_2137_, 0, v___x_2146_);
v___x_2152_ = v___x_2137_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
}
else
{
lean_object* v_k_2166_; lean_object* v_v_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v_k_2166_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_k_2166_);
v_v_2167_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_v_2167_);
lean_dec_ref(v___x_2023_);
v___x_2168_ = lean_unsigned_to_nat(2u);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v_r_1871_);
lean_ctor_set(v___x_2021_, 3, v_l_1696_);
lean_ctor_set(v___x_2021_, 2, v_v_2167_);
lean_ctor_set(v___x_2021_, 1, v_k_2166_);
lean_ctor_set(v___x_2021_, 0, v___x_2168_);
v___x_2170_ = v___x_2021_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_2166_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_2167_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_l_1696_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v_r_1871_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
}
}
else
{
return v_l_1696_;
}
}
else
{
return v_r_1697_;
}
}
}
else
{
lean_object* v_impl_2178_; lean_object* v___x_2179_; 
v_impl_2178_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1692_, v_l_1696_);
v___x_2179_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2178_) == 0)
{
if (lean_obj_tag(v_r_1697_) == 0)
{
lean_object* v_size_2180_; lean_object* v_size_2181_; lean_object* v_k_2182_; lean_object* v_v_2183_; lean_object* v_l_2184_; lean_object* v_r_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v_size_2180_ = lean_ctor_get(v_impl_2178_, 0);
lean_inc(v_size_2180_);
v_size_2181_ = lean_ctor_get(v_r_1697_, 0);
v_k_2182_ = lean_ctor_get(v_r_1697_, 1);
v_v_2183_ = lean_ctor_get(v_r_1697_, 2);
v_l_2184_ = lean_ctor_get(v_r_1697_, 3);
lean_inc(v_l_2184_);
v_r_2185_ = lean_ctor_get(v_r_1697_, 4);
v___x_2186_ = lean_unsigned_to_nat(3u);
v___x_2187_ = lean_nat_mul(v___x_2186_, v_size_2180_);
v___x_2188_ = lean_nat_dec_lt(v___x_2187_, v_size_2181_);
lean_dec(v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec(v_l_2184_);
v___x_2189_ = lean_nat_add(v___x_2179_, v_size_2180_);
lean_dec(v_size_2180_);
v___x_2190_ = lean_nat_add(v___x_2189_, v_size_2181_);
lean_dec(v___x_2189_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 3, v_impl_2178_);
lean_ctor_set(v___x_1699_, 0, v___x_2190_);
v___x_2192_ = v___x_1699_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2193_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2193_, 3, v_impl_2178_);
lean_ctor_set(v_reuseFailAlloc_2193_, 4, v_r_1697_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2257_; 
lean_inc(v_r_2185_);
lean_inc(v_v_2183_);
lean_inc(v_k_2182_);
lean_inc(v_size_2181_);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_r_1697_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; lean_object* v_unused_2259_; lean_object* v_unused_2260_; lean_object* v_unused_2261_; lean_object* v_unused_2262_; 
v_unused_2258_ = lean_ctor_get(v_r_1697_, 4);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_r_1697_, 3);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_r_1697_, 2);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_r_1697_, 1);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_r_1697_, 0);
lean_dec(v_unused_2262_);
v___x_2195_ = v_r_1697_;
v_isShared_2196_ = v_isSharedCheck_2257_;
goto v_resetjp_2194_;
}
else
{
lean_dec(v_r_1697_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2257_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_size_2197_; lean_object* v_k_2198_; lean_object* v_v_2199_; lean_object* v_l_2200_; lean_object* v_r_2201_; lean_object* v_size_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v_size_2197_ = lean_ctor_get(v_l_2184_, 0);
v_k_2198_ = lean_ctor_get(v_l_2184_, 1);
v_v_2199_ = lean_ctor_get(v_l_2184_, 2);
v_l_2200_ = lean_ctor_get(v_l_2184_, 3);
v_r_2201_ = lean_ctor_get(v_l_2184_, 4);
v_size_2202_ = lean_ctor_get(v_r_2185_, 0);
v___x_2203_ = lean_unsigned_to_nat(2u);
v___x_2204_ = lean_nat_mul(v___x_2203_, v_size_2202_);
v___x_2205_ = lean_nat_dec_lt(v_size_2197_, v___x_2204_);
lean_dec(v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2233_; 
lean_inc(v_r_2201_);
lean_inc(v_l_2200_);
lean_inc(v_v_2199_);
lean_inc(v_k_2198_);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_l_2184_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; lean_object* v_unused_2235_; lean_object* v_unused_2236_; lean_object* v_unused_2237_; lean_object* v_unused_2238_; 
v_unused_2234_ = lean_ctor_get(v_l_2184_, 4);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_l_2184_, 3);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v_l_2184_, 2);
lean_dec(v_unused_2236_);
v_unused_2237_ = lean_ctor_get(v_l_2184_, 1);
lean_dec(v_unused_2237_);
v_unused_2238_ = lean_ctor_get(v_l_2184_, 0);
lean_dec(v_unused_2238_);
v___x_2207_ = v_l_2184_;
v_isShared_2208_ = v_isSharedCheck_2233_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v_l_2184_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2233_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2223_; 
v___x_2209_ = lean_nat_add(v___x_2179_, v_size_2180_);
lean_dec(v_size_2180_);
v___x_2210_ = lean_nat_add(v___x_2209_, v_size_2181_);
lean_dec(v_size_2181_);
if (lean_obj_tag(v_l_2200_) == 0)
{
lean_object* v_size_2231_; 
v_size_2231_ = lean_ctor_get(v_l_2200_, 0);
lean_inc(v_size_2231_);
v___y_2223_ = v_size_2231_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_unsigned_to_nat(0u);
v___y_2223_ = v___x_2232_;
goto v___jp_2222_;
}
v___jp_2211_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2215_ = lean_nat_add(v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec(v___y_2213_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 4, v_r_2185_);
lean_ctor_set(v___x_2207_, 3, v_r_2201_);
lean_ctor_set(v___x_2207_, 2, v_v_2183_);
lean_ctor_set(v___x_2207_, 1, v_k_2182_);
lean_ctor_set(v___x_2207_, 0, v___x_2215_);
v___x_2217_ = v___x_2207_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_k_2182_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_v_2183_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_r_2201_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_r_2185_);
v___x_2217_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v___x_2217_);
lean_ctor_set(v___x_2195_, 3, v___y_2212_);
lean_ctor_set(v___x_2195_, 2, v_v_2199_);
lean_ctor_set(v___x_2195_, 1, v_k_2198_);
lean_ctor_set(v___x_2195_, 0, v___x_2210_);
v___x_2219_ = v___x_2195_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_k_2198_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_v_2199_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v___y_2212_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
v___jp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_nat_add(v___x_2209_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec(v___x_2209_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_l_2200_);
lean_ctor_set(v___x_1699_, 3, v_impl_2178_);
lean_ctor_set(v___x_1699_, 0, v___x_2224_);
v___x_2226_ = v___x_1699_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_impl_2178_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_l_2200_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_nat_add(v___x_2179_, v_size_2202_);
if (lean_obj_tag(v_r_2201_) == 0)
{
lean_object* v_size_2228_; 
v_size_2228_ = lean_ctor_get(v_r_2201_, 0);
lean_inc(v_size_2228_);
v___y_2212_ = v___x_2226_;
v___y_2213_ = v___x_2227_;
v___y_2214_ = v_size_2228_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_unsigned_to_nat(0u);
v___y_2212_ = v___x_2226_;
v___y_2213_ = v___x_2227_;
v___y_2214_ = v___x_2229_;
goto v___jp_2211_;
}
}
}
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
lean_del_object(v___x_1699_);
v___x_2239_ = lean_nat_add(v___x_2179_, v_size_2180_);
lean_dec(v_size_2180_);
v___x_2240_ = lean_nat_add(v___x_2239_, v_size_2181_);
lean_dec(v_size_2181_);
v___x_2241_ = lean_nat_add(v___x_2239_, v_size_2197_);
lean_dec(v___x_2239_);
lean_inc_ref(v_impl_2178_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v_l_2184_);
lean_ctor_set(v___x_2195_, 3, v_impl_2178_);
lean_ctor_set(v___x_2195_, 2, v_v_1695_);
lean_ctor_set(v___x_2195_, 1, v_k_1694_);
lean_ctor_set(v___x_2195_, 0, v___x_2241_);
v___x_2243_ = v___x_2195_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_impl_2178_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v_l_2184_);
v___x_2243_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_isSharedCheck_2250_ = !lean_is_exclusive(v_impl_2178_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; lean_object* v_unused_2252_; lean_object* v_unused_2253_; lean_object* v_unused_2254_; lean_object* v_unused_2255_; 
v_unused_2251_ = lean_ctor_get(v_impl_2178_, 4);
lean_dec(v_unused_2251_);
v_unused_2252_ = lean_ctor_get(v_impl_2178_, 3);
lean_dec(v_unused_2252_);
v_unused_2253_ = lean_ctor_get(v_impl_2178_, 2);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_impl_2178_, 1);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_impl_2178_, 0);
lean_dec(v_unused_2255_);
v___x_2245_ = v_impl_2178_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_dec(v_impl_2178_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_r_2185_);
lean_ctor_set(v___x_2245_, 3, v___x_2243_);
lean_ctor_set(v___x_2245_, 2, v_v_2183_);
lean_ctor_set(v___x_2245_, 1, v_k_2182_);
lean_ctor_set(v___x_2245_, 0, v___x_2240_);
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_k_2182_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_v_2183_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_r_2185_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v_size_2263_ = lean_ctor_get(v_impl_2178_, 0);
lean_inc(v_size_2263_);
v___x_2264_ = lean_nat_add(v___x_2179_, v_size_2263_);
lean_dec(v_size_2263_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 3, v_impl_2178_);
lean_ctor_set(v___x_1699_, 0, v___x_2264_);
v___x_2266_ = v___x_1699_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2267_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2267_, 3, v_impl_2178_);
lean_ctor_set(v_reuseFailAlloc_2267_, 4, v_r_1697_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
else
{
if (lean_obj_tag(v_r_1697_) == 0)
{
lean_object* v_l_2268_; 
v_l_2268_ = lean_ctor_get(v_r_1697_, 3);
lean_inc(v_l_2268_);
if (lean_obj_tag(v_l_2268_) == 0)
{
lean_object* v_r_2269_; 
v_r_2269_ = lean_ctor_get(v_r_1697_, 4);
lean_inc(v_r_2269_);
if (lean_obj_tag(v_r_2269_) == 0)
{
lean_object* v_size_2270_; lean_object* v_k_2271_; lean_object* v_v_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2285_; 
v_size_2270_ = lean_ctor_get(v_r_1697_, 0);
v_k_2271_ = lean_ctor_get(v_r_1697_, 1);
v_v_2272_ = lean_ctor_get(v_r_1697_, 2);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_r_1697_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; lean_object* v_unused_2287_; 
v_unused_2286_ = lean_ctor_get(v_r_1697_, 4);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_r_1697_, 3);
lean_dec(v_unused_2287_);
v___x_2274_ = v_r_1697_;
v_isShared_2275_ = v_isSharedCheck_2285_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_v_2272_);
lean_inc(v_k_2271_);
lean_inc(v_size_2270_);
lean_dec(v_r_1697_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2285_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v_size_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
v_size_2276_ = lean_ctor_get(v_l_2268_, 0);
v___x_2277_ = lean_nat_add(v___x_2179_, v_size_2270_);
lean_dec(v_size_2270_);
v___x_2278_ = lean_nat_add(v___x_2179_, v_size_2276_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_l_2268_);
lean_ctor_set(v___x_2274_, 3, v_impl_2178_);
lean_ctor_set(v___x_2274_, 2, v_v_1695_);
lean_ctor_set(v___x_2274_, 1, v_k_1694_);
lean_ctor_set(v___x_2274_, 0, v___x_2278_);
v___x_2280_ = v___x_2274_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_impl_2178_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v_l_2268_);
v___x_2280_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2282_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_r_2269_);
lean_ctor_set(v___x_1699_, 3, v___x_2280_);
lean_ctor_set(v___x_1699_, 2, v_v_2272_);
lean_ctor_set(v___x_1699_, 1, v_k_2271_);
lean_ctor_set(v___x_1699_, 0, v___x_2277_);
v___x_2282_ = v___x_1699_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2277_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_k_2271_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_v_2272_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v_r_2269_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_k_2288_; lean_object* v_v_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2312_; 
v_k_2288_ = lean_ctor_get(v_r_1697_, 1);
v_v_2289_ = lean_ctor_get(v_r_1697_, 2);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_r_1697_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2313_ = lean_ctor_get(v_r_1697_, 4);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_r_1697_, 3);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_r_1697_, 0);
lean_dec(v_unused_2315_);
v___x_2291_ = v_r_1697_;
v_isShared_2292_ = v_isSharedCheck_2312_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_v_2289_);
lean_inc(v_k_2288_);
lean_dec(v_r_1697_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2312_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v_k_2293_; lean_object* v_v_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2308_; 
v_k_2293_ = lean_ctor_get(v_l_2268_, 1);
v_v_2294_ = lean_ctor_get(v_l_2268_, 2);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_l_2268_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; lean_object* v_unused_2310_; lean_object* v_unused_2311_; 
v_unused_2309_ = lean_ctor_get(v_l_2268_, 4);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_l_2268_, 3);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_l_2268_, 0);
lean_dec(v_unused_2311_);
v___x_2296_ = v_l_2268_;
v_isShared_2297_ = v_isSharedCheck_2308_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_v_2294_);
lean_inc(v_k_2293_);
lean_dec(v_l_2268_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2308_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_unsigned_to_nat(3u);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 4, v_r_2269_);
lean_ctor_set(v___x_2296_, 3, v_r_2269_);
lean_ctor_set(v___x_2296_, 2, v_v_1695_);
lean_ctor_set(v___x_2296_, 1, v_k_1694_);
lean_ctor_set(v___x_2296_, 0, v___x_2179_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_r_2269_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_r_2269_);
v___x_2300_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 3, v_r_2269_);
lean_ctor_set(v___x_2291_, 0, v___x_2179_);
v___x_2302_ = v___x_2291_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_k_2288_);
lean_ctor_set(v_reuseFailAlloc_2306_, 2, v_v_2289_);
lean_ctor_set(v_reuseFailAlloc_2306_, 3, v_r_2269_);
lean_ctor_set(v_reuseFailAlloc_2306_, 4, v_r_2269_);
v___x_2302_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2304_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___x_2302_);
lean_ctor_set(v___x_1699_, 3, v___x_2300_);
lean_ctor_set(v___x_1699_, 2, v_v_2294_);
lean_ctor_set(v___x_1699_, 1, v_k_2293_);
lean_ctor_set(v___x_1699_, 0, v___x_2298_);
v___x_2304_ = v___x_1699_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_k_2293_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_v_2294_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v___x_2302_);
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
}
}
}
else
{
lean_object* v_r_2316_; 
v_r_2316_ = lean_ctor_get(v_r_1697_, 4);
lean_inc(v_r_2316_);
if (lean_obj_tag(v_r_2316_) == 0)
{
lean_object* v_k_2317_; lean_object* v_v_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2329_; 
v_k_2317_ = lean_ctor_get(v_r_1697_, 1);
v_v_2318_ = lean_ctor_get(v_r_1697_, 2);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_r_1697_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; lean_object* v_unused_2331_; lean_object* v_unused_2332_; 
v_unused_2330_ = lean_ctor_get(v_r_1697_, 4);
lean_dec(v_unused_2330_);
v_unused_2331_ = lean_ctor_get(v_r_1697_, 3);
lean_dec(v_unused_2331_);
v_unused_2332_ = lean_ctor_get(v_r_1697_, 0);
lean_dec(v_unused_2332_);
v___x_2320_ = v_r_1697_;
v_isShared_2321_ = v_isSharedCheck_2329_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_v_2318_);
lean_inc(v_k_2317_);
lean_dec(v_r_1697_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2329_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = lean_unsigned_to_nat(3u);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 4, v_l_2268_);
lean_ctor_set(v___x_2320_, 2, v_v_1695_);
lean_ctor_set(v___x_2320_, 1, v_k_1694_);
lean_ctor_set(v___x_2320_, 0, v___x_2179_);
v___x_2324_ = v___x_2320_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_l_2268_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_l_2268_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v_r_2316_);
lean_ctor_set(v___x_1699_, 3, v___x_2324_);
lean_ctor_set(v___x_1699_, 2, v_v_2318_);
lean_ctor_set(v___x_1699_, 1, v_k_2317_);
lean_ctor_set(v___x_1699_, 0, v___x_2322_);
v___x_2326_ = v___x_1699_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_k_2317_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_v_2318_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_r_2316_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_size_2333_; lean_object* v_k_2334_; lean_object* v_v_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2346_; 
v_size_2333_ = lean_ctor_get(v_r_1697_, 0);
v_k_2334_ = lean_ctor_get(v_r_1697_, 1);
v_v_2335_ = lean_ctor_get(v_r_1697_, 2);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_r_1697_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; lean_object* v_unused_2348_; 
v_unused_2347_ = lean_ctor_get(v_r_1697_, 4);
lean_dec(v_unused_2347_);
v_unused_2348_ = lean_ctor_get(v_r_1697_, 3);
lean_dec(v_unused_2348_);
v___x_2337_ = v_r_1697_;
v_isShared_2338_ = v_isSharedCheck_2346_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_v_2335_);
lean_inc(v_k_2334_);
lean_inc(v_size_2333_);
lean_dec(v_r_1697_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2346_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 3, v_r_2316_);
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_size_2333_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_k_2334_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_v_2335_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_r_2316_);
lean_ctor_set(v_reuseFailAlloc_2345_, 4, v_r_2316_);
v___x_2340_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_unsigned_to_nat(2u);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___x_2340_);
lean_ctor_set(v___x_1699_, 3, v_r_2316_);
lean_ctor_set(v___x_1699_, 0, v___x_2341_);
v___x_2343_ = v___x_1699_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_r_2316_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v___x_2340_);
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
lean_object* v___x_2350_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 3, v_r_1697_);
lean_ctor_set(v___x_1699_, 0, v___x_2179_);
v___x_2350_ = v___x_1699_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_k_1694_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_v_1695_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v_r_1697_);
lean_ctor_set(v_reuseFailAlloc_2351_, 4, v_r_1697_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
else
{
return v_t_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2354_, lean_object* v_t_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2354_, v_t_2355_);
lean_dec(v_k_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v_capacity_2361_; lean_object* v_buffer_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2360_ = lean_st_ref_get(v_a_2358_);
v_capacity_2361_ = lean_ctor_get(v___x_2360_, 2);
lean_inc(v_capacity_2361_);
v_buffer_2362_ = lean_ctor_get(v___x_2360_, 4);
lean_inc_ref(v_buffer_2362_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_nat_mod(v_place_2357_, v_capacity_2361_);
lean_dec(v_capacity_2361_);
v___x_2364_ = lean_array_fget(v_buffer_2362_, v___x_2363_);
lean_dec(v___x_2363_);
lean_dec_ref(v_buffer_2362_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_2366_, lean_object* v_a_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec(v_place_2366_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2372_; lean_object* v_size_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2372_ = lean_st_ref_get(v_a_2370_);
v_size_2373_ = lean_ctor_get(v___x_2372_, 3);
lean_inc(v_size_2373_);
lean_dec(v___x_2372_);
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = lean_nat_dec_eq(v_size_2373_, v___x_2374_);
lean_dec(v_size_2373_);
v___x_2376_ = lean_box(v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2378_);
lean_dec(v_a_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_2381_, lean_object* v_next_2382_){
_start:
{
lean_object* v___x_2384_; lean_object* v_fst_2386_; lean_object* v_snd_2387_; lean_object* v_value_2390_; lean_object* v_pos_2391_; lean_object* v_remaining_2392_; uint8_t v___x_2393_; 
v___x_2384_ = lean_st_ref_take(v_slot_2381_);
v_value_2390_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_value_2390_);
v_pos_2391_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_pos_2391_);
v_remaining_2392_ = lean_ctor_get(v___x_2384_, 2);
lean_inc(v_remaining_2392_);
v___x_2393_ = lean_nat_dec_eq(v_next_2382_, v_pos_2391_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_dec(v_remaining_2392_);
lean_dec(v_pos_2391_);
lean_dec(v_value_2390_);
v___x_2394_ = lean_box(0);
v___x_2395_ = lean_box(v___x_2393_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v_fst_2386_ = v___x_2396_;
v_snd_2387_ = v___x_2384_;
goto v___jp_2385_;
}
else
{
lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2415_; 
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2416_ = lean_ctor_get(v___x_2384_, 2);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v___x_2384_, 1);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v___x_2384_, 0);
lean_dec(v_unused_2418_);
v___x_2398_ = v___x_2384_;
v_isShared_2399_ = v_isSharedCheck_2415_;
goto v_resetjp_2397_;
}
else
{
lean_dec(v___x_2384_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2415_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; uint8_t v___x_2401_; 
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = lean_nat_dec_eq(v_remaining_2392_, v___x_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2402_ = lean_box(v___x_2401_);
lean_inc(v_value_2390_);
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v_value_2390_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_nat_sub(v_remaining_2392_, v___x_2400_);
lean_dec(v_remaining_2392_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 2, v___x_2404_);
v___x_2406_ = v___x_2398_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_value_2390_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_pos_2391_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
v_fst_2386_ = v___x_2403_;
v_snd_2387_ = v___x_2406_;
goto v___jp_2385_;
}
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
lean_dec(v_remaining_2392_);
v___x_2408_ = lean_box(v___x_2393_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_value_2390_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_unsigned_to_nat(0u);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 2, v___x_2411_);
lean_ctor_set(v___x_2398_, 0, v___x_2410_);
v___x_2413_ = v___x_2398_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2410_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_pos_2391_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
v_fst_2386_ = v___x_2409_;
v_snd_2387_ = v___x_2413_;
goto v___jp_2385_;
}
}
}
}
v___jp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_st_ref_set(v_slot_2381_, v_snd_2387_);
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v_fst_2386_);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_2419_, lean_object* v_next_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2419_, v_next_2420_);
lean_dec(v_next_2420_);
lean_dec(v_slot_2419_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2499_; 
v___x_2426_ = lean_st_ref_get(v_a_2424_);
v___x_2427_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2424_);
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2430_ = v___x_2427_;
v_isShared_2431_ = v_isSharedCheck_2499_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2499_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_unbox(v_a_2428_);
lean_dec(v_a_2428_);
if (v___x_2432_ == 0)
{
lean_object* v_capacity_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2494_; 
lean_del_object(v___x_2430_);
v_capacity_2433_ = lean_ctor_get(v___x_2426_, 2);
lean_inc(v_capacity_2433_);
v___x_2434_ = lean_nat_mod(v_next_2423_, v_capacity_2433_);
lean_dec(v_capacity_2433_);
v___x_2435_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_2434_, v_a_2424_);
lean_dec(v___x_2434_);
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2494_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2494_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2493_; 
v___x_2440_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_2436_, v_next_2423_);
lean_dec(v_a_2436_);
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2493_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2493_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v_fst_2445_; lean_object* v_snd_2446_; lean_object* v_st_2448_; lean_object* v___y_2449_; 
v_fst_2445_ = lean_ctor_get(v_a_2441_, 0);
lean_inc(v_fst_2445_);
v_snd_2446_ = lean_ctor_get(v_a_2441_, 1);
lean_inc(v_snd_2446_);
lean_dec(v_a_2441_);
if (lean_obj_tag(v_fst_2445_) == 1)
{
uint8_t v___x_2454_; 
lean_del_object(v___x_2438_);
v___x_2454_ = lean_unbox(v_snd_2446_);
if (v___x_2454_ == 0)
{
lean_dec(v_snd_2446_);
v_st_2448_ = v___x_2426_;
v___y_2449_ = v_a_2424_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2455_; lean_object* v_producers_2456_; lean_object* v_waiters_2457_; lean_object* v_capacity_2458_; lean_object* v_size_2459_; lean_object* v_buffer_2460_; lean_object* v_write_2461_; lean_object* v_read_2462_; lean_object* v_receivers_2463_; lean_object* v_nextId_2464_; uint8_t v_closed_2465_; lean_object* v_pos_2466_; lean_object* v___x_2467_; 
v___x_2455_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_2426_);
v_producers_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc_ref(v_producers_2456_);
v_waiters_2457_ = lean_ctor_get(v___x_2455_, 1);
lean_inc_ref(v_waiters_2457_);
v_capacity_2458_ = lean_ctor_get(v___x_2455_, 2);
lean_inc(v_capacity_2458_);
v_size_2459_ = lean_ctor_get(v___x_2455_, 3);
lean_inc(v_size_2459_);
v_buffer_2460_ = lean_ctor_get(v___x_2455_, 4);
lean_inc_ref(v_buffer_2460_);
v_write_2461_ = lean_ctor_get(v___x_2455_, 5);
lean_inc(v_write_2461_);
v_read_2462_ = lean_ctor_get(v___x_2455_, 6);
lean_inc(v_read_2462_);
v_receivers_2463_ = lean_ctor_get(v___x_2455_, 7);
lean_inc(v_receivers_2463_);
v_nextId_2464_ = lean_ctor_get(v___x_2455_, 8);
lean_inc(v_nextId_2464_);
v_closed_2465_ = lean_ctor_get_uint8(v___x_2455_, sizeof(void*)*10);
v_pos_2466_ = lean_ctor_get(v___x_2455_, 9);
lean_inc(v_pos_2466_);
v___x_2467_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2456_);
if (lean_obj_tag(v___x_2467_) == 1)
{
lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2478_; 
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; lean_object* v_unused_2480_; lean_object* v_unused_2481_; lean_object* v_unused_2482_; lean_object* v_unused_2483_; lean_object* v_unused_2484_; lean_object* v_unused_2485_; lean_object* v_unused_2486_; lean_object* v_unused_2487_; lean_object* v_unused_2488_; 
v_unused_2479_ = lean_ctor_get(v___x_2455_, 9);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v___x_2455_, 8);
lean_dec(v_unused_2480_);
v_unused_2481_ = lean_ctor_get(v___x_2455_, 7);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v___x_2455_, 6);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v___x_2455_, 5);
lean_dec(v_unused_2483_);
v_unused_2484_ = lean_ctor_get(v___x_2455_, 4);
lean_dec(v_unused_2484_);
v_unused_2485_ = lean_ctor_get(v___x_2455_, 3);
lean_dec(v_unused_2485_);
v_unused_2486_ = lean_ctor_get(v___x_2455_, 2);
lean_dec(v_unused_2486_);
v_unused_2487_ = lean_ctor_get(v___x_2455_, 1);
lean_dec(v_unused_2487_);
v_unused_2488_ = lean_ctor_get(v___x_2455_, 0);
lean_dec(v_unused_2488_);
v___x_2469_ = v___x_2455_;
v_isShared_2470_ = v_isSharedCheck_2478_;
goto v_resetjp_2468_;
}
else
{
lean_dec(v___x_2455_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2478_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v_val_2471_; lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v_val_2471_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2471_);
lean_dec_ref(v___x_2467_);
v_fst_2472_ = lean_ctor_get(v_val_2471_, 0);
lean_inc(v_fst_2472_);
v_snd_2473_ = lean_ctor_get(v_val_2471_, 1);
lean_inc(v_snd_2473_);
lean_dec(v_val_2471_);
v___x_2474_ = lean_io_promise_resolve(v_snd_2446_, v_fst_2472_);
lean_dec(v_fst_2472_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v_snd_2473_);
v___x_2476_ = v___x_2469_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_snd_2473_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_waiters_2457_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_capacity_2458_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_size_2459_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_buffer_2460_);
lean_ctor_set(v_reuseFailAlloc_2477_, 5, v_write_2461_);
lean_ctor_set(v_reuseFailAlloc_2477_, 6, v_read_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 7, v_receivers_2463_);
lean_ctor_set(v_reuseFailAlloc_2477_, 8, v_nextId_2464_);
lean_ctor_set(v_reuseFailAlloc_2477_, 9, v_pos_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2477_, sizeof(void*)*10, v_closed_2465_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
v_st_2448_ = v___x_2476_;
v___y_2449_ = v_a_2424_;
goto v___jp_2447_;
}
}
}
else
{
lean_dec(v___x_2467_);
lean_dec(v_pos_2466_);
lean_dec(v_nextId_2464_);
lean_dec(v_receivers_2463_);
lean_dec(v_read_2462_);
lean_dec(v_write_2461_);
lean_dec_ref(v_buffer_2460_);
lean_dec(v_size_2459_);
lean_dec(v_capacity_2458_);
lean_dec_ref(v_waiters_2457_);
lean_dec(v_snd_2446_);
v_st_2448_ = v___x_2455_;
v___y_2449_ = v_a_2424_;
goto v___jp_2447_;
}
}
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
lean_dec(v_snd_2446_);
lean_dec(v_fst_2445_);
lean_del_object(v___x_2443_);
lean_dec(v___x_2426_);
v___x_2489_ = lean_box(0);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2489_);
v___x_2491_ = v___x_2438_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
v___jp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_st_ref_set(v___y_2449_, v_st_2448_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v_fst_2445_);
v___x_2452_ = v___x_2443_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_fst_2445_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
lean_dec(v___x_2426_);
v___x_2495_ = lean_box(0);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2495_);
v___x_2497_ = v___x_2430_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_2500_, lean_object* v_a_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2500_, v_a_2501_);
lean_dec(v_a_2501_);
lean_dec(v_next_2500_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_b_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_fst_2507_; lean_object* v_snd_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2545_; 
v_fst_2507_ = lean_ctor_get(v_b_2504_, 0);
v_snd_2508_ = lean_ctor_get(v_b_2504_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_b_2504_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2510_ = v_b_2504_;
v_isShared_2511_ = v_isSharedCheck_2545_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_snd_2508_);
lean_inc(v_fst_2507_);
lean_dec(v_b_2504_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2545_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_size_2517_; lean_object* v_pos_2518_; uint8_t v___x_2519_; 
v_size_2517_ = lean_ctor_get(v_fst_2507_, 3);
v_pos_2518_ = lean_ctor_get(v_fst_2507_, 9);
v___x_2519_ = lean_nat_dec_lt(v_snd_2508_, v_pos_2518_);
if (v___x_2519_ == 0)
{
goto v___jp_2512_;
}
else
{
lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_nat_dec_lt(v___x_2520_, v_size_2517_);
if (v___x_2521_ == 0)
{
goto v___jp_2512_;
}
else
{
lean_object* v___x_2522_; 
lean_del_object(v___x_2510_);
v___x_2522_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_2508_, v___y_2505_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2536_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2536_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2536_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
if (lean_obj_tag(v_a_2523_) == 1)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec_ref(v_a_2523_);
lean_del_object(v___x_2525_);
lean_dec(v_fst_2507_);
v___x_2527_ = lean_st_ref_get(v___y_2505_);
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = lean_nat_add(v_snd_2508_, v___x_2528_);
lean_dec(v_snd_2508_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2527_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v_b_2504_ = v___x_2530_;
goto _start;
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
lean_dec(v_a_2523_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v_fst_2507_);
lean_ctor_set(v___x_2532_, 1, v_snd_2508_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2532_);
v___x_2534_ = v___x_2525_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_snd_2508_);
lean_dec(v_fst_2507_);
v_a_2537_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2522_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2522_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
v___jp_2512_:
{
lean_object* v___x_2514_; 
if (v_isShared_2511_ == 0)
{
v___x_2514_ = v___x_2510_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_fst_2507_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_snd_2508_);
v___x_2514_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
return v___x_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_b_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_b_2546_, v___y_2547_);
lean_dec(v___y_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object* v_id_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; lean_object* v_receivers_2559_; lean_object* v___x_2560_; 
v___x_2558_ = lean_st_ref_get(v___y_2556_);
v_receivers_2559_ = lean_ctor_get(v___x_2558_, 7);
lean_inc(v_receivers_2559_);
v___x_2560_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2559_, v_id_2555_);
lean_dec(v_receivers_2559_);
if (lean_obj_tag(v___x_2560_) == 1)
{
lean_object* v_val_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v_val_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_val_2561_);
lean_dec_ref(v___x_2560_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2558_);
lean_ctor_set(v___x_2562_, 1, v_val_2561_);
v___x_2563_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2562_, v___y_2556_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2593_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2593_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2593_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_fst_2568_; lean_object* v_producers_2569_; lean_object* v_waiters_2570_; lean_object* v_capacity_2571_; lean_object* v_size_2572_; lean_object* v_buffer_2573_; lean_object* v_write_2574_; lean_object* v_read_2575_; lean_object* v_receivers_2576_; lean_object* v_nextId_2577_; uint8_t v_closed_2578_; lean_object* v_pos_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2592_; 
v_fst_2568_ = lean_ctor_get(v_a_2564_, 0);
lean_inc(v_fst_2568_);
lean_dec(v_a_2564_);
v_producers_2569_ = lean_ctor_get(v_fst_2568_, 0);
v_waiters_2570_ = lean_ctor_get(v_fst_2568_, 1);
v_capacity_2571_ = lean_ctor_get(v_fst_2568_, 2);
v_size_2572_ = lean_ctor_get(v_fst_2568_, 3);
v_buffer_2573_ = lean_ctor_get(v_fst_2568_, 4);
v_write_2574_ = lean_ctor_get(v_fst_2568_, 5);
v_read_2575_ = lean_ctor_get(v_fst_2568_, 6);
v_receivers_2576_ = lean_ctor_get(v_fst_2568_, 7);
v_nextId_2577_ = lean_ctor_get(v_fst_2568_, 8);
v_closed_2578_ = lean_ctor_get_uint8(v_fst_2568_, sizeof(void*)*10);
v_pos_2579_ = lean_ctor_get(v_fst_2568_, 9);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_fst_2568_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2581_ = v_fst_2568_;
v_isShared_2582_ = v_isSharedCheck_2592_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_pos_2579_);
lean_inc(v_nextId_2577_);
lean_inc(v_receivers_2576_);
lean_inc(v_read_2575_);
lean_inc(v_write_2574_);
lean_inc(v_buffer_2573_);
lean_inc(v_size_2572_);
lean_inc(v_capacity_2571_);
lean_inc(v_waiters_2570_);
lean_inc(v_producers_2569_);
lean_dec(v_fst_2568_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2592_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
v___x_2583_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_id_2555_, v_receivers_2576_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 7, v___x_2583_);
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_producers_2569_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_waiters_2570_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_capacity_2571_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_size_2572_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_buffer_2573_);
lean_ctor_set(v_reuseFailAlloc_2591_, 5, v_write_2574_);
lean_ctor_set(v_reuseFailAlloc_2591_, 6, v_read_2575_);
lean_ctor_set(v_reuseFailAlloc_2591_, 7, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2591_, 8, v_nextId_2577_);
lean_ctor_set(v_reuseFailAlloc_2591_, 9, v_pos_2579_);
lean_ctor_set_uint8(v_reuseFailAlloc_2591_, sizeof(void*)*10, v_closed_2578_);
v___x_2585_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2586_ = lean_st_ref_set(v___y_2556_, v___x_2585_);
v___x_2587_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0));
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2587_);
v___x_2589_ = v___x_2566_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
v_a_2594_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2563_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2563_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_dec(v___x_2560_);
lean_dec(v___x_2558_);
v___x_2602_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1));
v___x_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object* v_id_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec(v_id_2604_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object* v_bd_2608_){
_start:
{
lean_object* v_state_2610_; lean_object* v_id_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; 
v_state_2610_ = lean_ctor_get(v_bd_2608_, 0);
lean_inc_ref(v_state_2610_);
v_id_2611_ = lean_ctor_get(v_bd_2608_, 1);
lean_inc(v_id_2611_);
lean_dec_ref(v_bd_2608_);
v___f_2612_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2612_, 0, v_id_2611_);
v___x_2613_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_2610_, v___f_2612_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2638_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2638_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2638_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___y_2619_; 
if (lean_obj_tag(v_a_2614_) == 0)
{
lean_object* v_a_2624_; uint8_t v___x_2625_; 
v_a_2624_ = lean_ctor_get(v_a_2614_, 0);
lean_inc(v_a_2624_);
lean_dec_ref(v_a_2614_);
v___x_2625_ = lean_unbox(v_a_2624_);
lean_dec(v_a_2624_);
switch(v___x_2625_)
{
case 0:
{
lean_object* v___x_2626_; 
v___x_2626_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_2619_ = v___x_2626_;
goto v___jp_2618_;
}
case 1:
{
lean_object* v___x_2627_; 
v___x_2627_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_2619_ = v___x_2627_;
goto v___jp_2618_;
}
default: 
{
lean_object* v___x_2628_; 
v___x_2628_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_2619_ = v___x_2628_;
goto v___jp_2618_;
}
}
}
else
{
lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2636_; 
lean_del_object(v___x_2616_);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_a_2614_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v_a_2614_, 0);
lean_dec(v_unused_2637_);
v___x_2630_ = v_a_2614_;
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
else
{
lean_dec(v_a_2614_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_box(0);
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
v___jp_2618_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___y_2619_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 1);
lean_ctor_set(v___x_2616_, 0, v___x_2620_);
v___x_2622_ = v___x_2616_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v_a_2639_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2613_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2613_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object* v_bd_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2647_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object* v_00_u03b1_2650_, lean_object* v_bd_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2651_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_2654_, lean_object* v_bd_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(v_00_u03b1_2654_, v_bd_2655_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object* v_00_u03b1_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_a_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(v_00_u03b1_2662_, v_a_2663_);
lean_dec(v_a_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object* v_00_u03b1_2666_, lean_object* v_place_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2667_, v_a_2668_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2671_, lean_object* v_place_2672_, lean_object* v_a_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(v_00_u03b1_2671_, v_place_2672_, v_a_2673_);
lean_dec(v_a_2673_);
lean_dec(v_place_2672_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object* v_00_u03b1_2676_, lean_object* v_slot_2677_, lean_object* v_next_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2677_, v_next_2678_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2682_, lean_object* v_slot_2683_, lean_object* v_next_2684_, lean_object* v_a_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(v_00_u03b1_2682_, v_slot_2683_, v_next_2684_, v_a_2685_);
lean_dec(v_a_2685_);
lean_dec(v_next_2684_);
lean_dec(v_slot_2683_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object* v_00_u03b1_2688_, lean_object* v_next_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2689_, v_a_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object* v_00_u03b1_2693_, lean_object* v_next_2694_, lean_object* v_a_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(v_00_u03b1_2693_, v_next_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec(v_next_2694_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object* v_00_u03b4_2698_, lean_object* v_t_2699_, lean_object* v_k_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2699_, v_k_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object* v_00_u03b4_2702_, lean_object* v_t_2703_, lean_object* v_k_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(v_00_u03b4_2702_, v_t_2703_, v_k_2704_);
lean_dec(v_k_2704_);
lean_dec(v_t_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2706_, lean_object* v_b_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_b_2707_, v___y_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2711_, lean_object* v_b_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2711_, v_b_2712_, v___y_2713_);
lean_dec(v___y_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2716_, lean_object* v_k_2717_, lean_object* v_t_2718_, lean_object* v_h_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2717_, v_t_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2721_, lean_object* v_k_2722_, lean_object* v_t_2723_, lean_object* v_h_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2721_, v_k_2722_, v_t_2723_, v_h_2724_);
lean_dec(v_k_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2726_, lean_object* v_y_2727_){
_start:
{
uint8_t v___x_2728_; 
v___x_2728_ = lean_nat_dec_lt(v_x_2726_, v_y_2727_);
if (v___x_2728_ == 0)
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_nat_dec_eq(v_x_2726_, v_y_2727_);
if (v___x_2729_ == 0)
{
uint8_t v___x_2730_; 
v___x_2730_ = 2;
return v___x_2730_;
}
else
{
uint8_t v___x_2731_; 
v___x_2731_ = 1;
return v___x_2731_;
}
}
else
{
uint8_t v___x_2732_; 
v___x_2732_ = 0;
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2733_, lean_object* v_y_2734_){
_start:
{
uint8_t v_res_2735_; lean_object* v_r_2736_; 
v_res_2735_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2733_, v_y_2734_);
lean_dec(v_y_2734_);
lean_dec(v_x_2733_);
v_r_2736_ = lean_box(v_res_2735_);
return v_r_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2737_){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = lean_unsigned_to_nat(1u);
v___x_2739_ = lean_nat_add(v_x_2737_, v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2740_);
lean_dec(v_x_2740_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2742_, lean_object* v_receiverId_2743_, lean_object* v___f_2744_, lean_object* v_receivers_2745_, lean_object* v_s_2746_){
_start:
{
lean_object* v_producers_2747_; lean_object* v_waiters_2748_; lean_object* v_capacity_2749_; lean_object* v_size_2750_; lean_object* v_buffer_2751_; lean_object* v_write_2752_; lean_object* v_read_2753_; lean_object* v_nextId_2754_; uint8_t v_closed_2755_; lean_object* v_pos_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2766_; 
v_producers_2747_ = lean_ctor_get(v_s_2746_, 0);
v_waiters_2748_ = lean_ctor_get(v_s_2746_, 1);
v_capacity_2749_ = lean_ctor_get(v_s_2746_, 2);
v_size_2750_ = lean_ctor_get(v_s_2746_, 3);
v_buffer_2751_ = lean_ctor_get(v_s_2746_, 4);
v_write_2752_ = lean_ctor_get(v_s_2746_, 5);
v_read_2753_ = lean_ctor_get(v_s_2746_, 6);
v_nextId_2754_ = lean_ctor_get(v_s_2746_, 8);
v_closed_2755_ = lean_ctor_get_uint8(v_s_2746_, sizeof(void*)*10);
v_pos_2756_ = lean_ctor_get(v_s_2746_, 9);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_s_2746_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v_s_2746_, 7);
lean_dec(v_unused_2767_);
v___x_2758_ = v_s_2746_;
v_isShared_2759_ = v_isSharedCheck_2766_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_pos_2756_);
lean_inc(v_nextId_2754_);
lean_inc(v_read_2753_);
lean_inc(v_write_2752_);
lean_inc(v_buffer_2751_);
lean_inc(v_size_2750_);
lean_inc(v_capacity_2749_);
lean_inc(v_waiters_2748_);
lean_inc(v_producers_2747_);
lean_dec(v_s_2746_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2766_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2760_ = lean_box(0);
v___x_2761_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2742_, v_receiverId_2743_, v___f_2744_, v_receivers_2745_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 7, v___x_2761_);
v___x_2763_ = v___x_2758_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_producers_2747_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_waiters_2748_);
lean_ctor_set(v_reuseFailAlloc_2765_, 2, v_capacity_2749_);
lean_ctor_set(v_reuseFailAlloc_2765_, 3, v_size_2750_);
lean_ctor_set(v_reuseFailAlloc_2765_, 4, v_buffer_2751_);
lean_ctor_set(v_reuseFailAlloc_2765_, 5, v_write_2752_);
lean_ctor_set(v_reuseFailAlloc_2765_, 6, v_read_2753_);
lean_ctor_set(v_reuseFailAlloc_2765_, 7, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2765_, 8, v_nextId_2754_);
lean_ctor_set(v_reuseFailAlloc_2765_, 9, v_pos_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2765_, sizeof(void*)*10, v_closed_2755_);
v___x_2763_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2760_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
return v___x_2764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_toPure_2771_; lean_object* v___x_2772_; 
v_toPure_2771_ = lean_ctor_get(v_toApplicative_2768_, 1);
lean_inc(v_toPure_2771_);
lean_dec_ref(v_toApplicative_2768_);
v___x_2772_ = lean_apply_2(v_toPure_2771_, lean_box(0), v_a_2769_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2773_, lean_object* v_a_2774_, lean_object* v___f_2775_, lean_object* v_inst_2776_, lean_object* v_toBind_2777_, lean_object* v_a_2778_){
_start:
{
if (lean_obj_tag(v_a_2778_) == 1)
{
lean_object* v___f_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___f_2779_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2779_, 0, v_toApplicative_2773_);
lean_closure_set(v___f_2779_, 1, v_a_2778_);
v___x_2780_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2780_, 0, lean_box(0));
lean_closure_set(v___x_2780_, 1, lean_box(0));
lean_closure_set(v___x_2780_, 2, lean_box(0));
lean_closure_set(v___x_2780_, 3, v_a_2774_);
lean_closure_set(v___x_2780_, 4, v___f_2775_);
v___x_2781_ = lean_apply_2(v_inst_2776_, lean_box(0), v___x_2780_);
v___x_2782_ = lean_apply_4(v_toBind_2777_, lean_box(0), lean_box(0), v___x_2781_, v___f_2779_);
return v___x_2782_;
}
else
{
lean_object* v_toPure_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec(v_a_2778_);
lean_dec(v_toBind_2777_);
lean_dec(v_inst_2776_);
lean_dec_ref(v___f_2775_);
lean_dec(v_a_2774_);
v_toPure_2783_ = lean_ctor_get(v_toApplicative_2773_, 1);
lean_inc(v_toPure_2783_);
lean_dec_ref(v_toApplicative_2773_);
v___x_2784_ = lean_box(0);
v___x_2785_ = lean_apply_2(v_toPure_2783_, lean_box(0), v___x_2784_);
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2786_, lean_object* v_receiverId_2787_, lean_object* v___f_2788_, lean_object* v___f_2789_, lean_object* v_toApplicative_2790_, lean_object* v_a_2791_, lean_object* v_inst_2792_, lean_object* v_toBind_2793_, lean_object* v_inst_2794_, lean_object* v_inst_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_receivers_2797_; lean_object* v___x_2798_; 
v_receivers_2797_ = lean_ctor_get(v_a_2796_, 7);
lean_inc(v_receivers_2797_);
lean_dec_ref(v_a_2796_);
lean_inc(v_receiverId_2787_);
lean_inc(v_receivers_2797_);
v___x_2798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2786_, v_receivers_2797_, v_receiverId_2787_);
if (lean_obj_tag(v___x_2798_) == 1)
{
lean_object* v_val_2799_; lean_object* v___f_2800_; lean_object* v___f_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v_val_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_val_2799_);
lean_dec_ref(v___x_2798_);
v___f_2800_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2800_, 0, v___f_2788_);
lean_closure_set(v___f_2800_, 1, v_receiverId_2787_);
lean_closure_set(v___f_2800_, 2, v___f_2789_);
lean_closure_set(v___f_2800_, 3, v_receivers_2797_);
lean_inc(v_toBind_2793_);
lean_inc(v_inst_2792_);
lean_inc(v_a_2791_);
v___f_2801_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4), 6, 5);
lean_closure_set(v___f_2801_, 0, v_toApplicative_2790_);
lean_closure_set(v___f_2801_, 1, v_a_2791_);
lean_closure_set(v___f_2801_, 2, v___f_2800_);
lean_closure_set(v___f_2801_, 3, v_inst_2792_);
lean_closure_set(v___f_2801_, 4, v_toBind_2793_);
v___x_2802_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2794_, v_inst_2792_, v_inst_2795_, v_val_2799_, v_a_2791_);
v___x_2803_ = lean_apply_4(v_toBind_2793_, lean_box(0), lean_box(0), v___x_2802_, v___f_2801_);
return v___x_2803_;
}
else
{
lean_object* v_toPure_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
lean_dec(v___x_2798_);
lean_dec(v_receivers_2797_);
lean_dec(v_inst_2795_);
lean_dec_ref(v_inst_2794_);
lean_dec(v_toBind_2793_);
lean_dec(v_inst_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v___f_2789_);
lean_dec_ref(v___f_2788_);
lean_dec(v_receiverId_2787_);
v_toPure_2804_ = lean_ctor_get(v_toApplicative_2790_, 1);
lean_inc(v_toPure_2804_);
lean_dec_ref(v_toApplicative_2790_);
v___x_2805_ = lean_box(0);
v___x_2806_ = lean_apply_2(v_toPure_2804_, lean_box(0), v___x_2805_);
return v___x_2806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_receiverId_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_toApplicative_2814_; lean_object* v_toBind_2815_; lean_object* v___f_2816_; lean_object* v___f_2817_; lean_object* v___f_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_toApplicative_2814_ = lean_ctor_get(v_inst_2809_, 0);
lean_inc_ref(v_toApplicative_2814_);
v_toBind_2815_ = lean_ctor_get(v_inst_2809_, 1);
lean_inc(v_toBind_2815_);
v___f_2816_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_2817_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_toBind_2815_);
lean_inc(v_inst_2810_);
lean_inc(v_a_2813_);
v___f_2818_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5), 11, 10);
lean_closure_set(v___f_2818_, 0, v___f_2816_);
lean_closure_set(v___f_2818_, 1, v_receiverId_2812_);
lean_closure_set(v___f_2818_, 2, v___f_2816_);
lean_closure_set(v___f_2818_, 3, v___f_2817_);
lean_closure_set(v___f_2818_, 4, v_toApplicative_2814_);
lean_closure_set(v___f_2818_, 5, v_a_2813_);
lean_closure_set(v___f_2818_, 6, v_inst_2810_);
lean_closure_set(v___f_2818_, 7, v_toBind_2815_);
lean_closure_set(v___f_2818_, 8, v_inst_2809_);
lean_closure_set(v___f_2818_, 9, v_inst_2811_);
v___x_2819_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2819_, 0, lean_box(0));
lean_closure_set(v___x_2819_, 1, lean_box(0));
lean_closure_set(v___x_2819_, 2, v_a_2813_);
v___x_2820_ = lean_apply_2(v_inst_2810_, lean_box(0), v___x_2819_);
v___x_2821_ = lean_apply_4(v_toBind_2815_, lean_box(0), lean_box(0), v___x_2820_, v___f_2818_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_2822_, lean_object* v_00_u03b1_2823_, lean_object* v_inst_2824_, lean_object* v_inst_2825_, lean_object* v_inst_2826_, lean_object* v_receiverId_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2824_, v_inst_2825_, v_inst_2826_, v_receiverId_2827_, v_a_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_2830_, lean_object* v_t_2831_){
_start:
{
if (lean_obj_tag(v_t_2831_) == 0)
{
lean_object* v_size_2832_; lean_object* v_k_2833_; lean_object* v_v_2834_; lean_object* v_l_2835_; lean_object* v_r_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2855_; 
v_size_2832_ = lean_ctor_get(v_t_2831_, 0);
v_k_2833_ = lean_ctor_get(v_t_2831_, 1);
v_v_2834_ = lean_ctor_get(v_t_2831_, 2);
v_l_2835_ = lean_ctor_get(v_t_2831_, 3);
v_r_2836_ = lean_ctor_get(v_t_2831_, 4);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_t_2831_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2838_ = v_t_2831_;
v_isShared_2839_ = v_isSharedCheck_2855_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_r_2836_);
lean_inc(v_l_2835_);
lean_inc(v_v_2834_);
lean_inc(v_k_2833_);
lean_inc(v_size_2832_);
lean_dec(v_t_2831_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2855_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
uint8_t v___x_2840_; 
v___x_2840_ = lean_nat_dec_lt(v_k_2830_, v_k_2833_);
if (v___x_2840_ == 0)
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_nat_dec_eq(v_k_2830_, v_k_2833_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2830_, v_r_2836_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v___x_2842_);
v___x_2844_ = v___x_2838_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_size_2832_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
lean_dec(v_k_2833_);
v___x_2846_ = lean_unsigned_to_nat(1u);
v___x_2847_ = lean_nat_add(v_v_2834_, v___x_2846_);
lean_dec(v_v_2834_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 2, v___x_2847_);
lean_ctor_set(v___x_2838_, 1, v_k_2830_);
v___x_2849_ = v___x_2838_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_size_2832_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_k_2830_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_r_2836_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2851_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2830_, v_l_2835_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 3, v___x_2851_);
v___x_2853_ = v___x_2838_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_size_2832_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_r_2836_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_dec(v_k_2830_);
return v_t_2831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_2856_, lean_object* v_next_2857_){
_start:
{
lean_object* v___x_2859_; lean_object* v_fst_2861_; lean_object* v_snd_2862_; lean_object* v_value_2864_; lean_object* v_pos_2865_; lean_object* v_remaining_2866_; uint8_t v___x_2867_; 
v___x_2859_ = lean_st_ref_take(v_slot_2856_);
v_value_2864_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_value_2864_);
v_pos_2865_ = lean_ctor_get(v___x_2859_, 1);
lean_inc(v_pos_2865_);
v_remaining_2866_ = lean_ctor_get(v___x_2859_, 2);
lean_inc(v_remaining_2866_);
v___x_2867_ = lean_nat_dec_eq(v_next_2857_, v_pos_2865_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_dec(v_remaining_2866_);
lean_dec(v_pos_2865_);
lean_dec(v_value_2864_);
v___x_2868_ = lean_box(0);
v___x_2869_ = lean_box(v___x_2867_);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v_fst_2861_ = v___x_2870_;
v_snd_2862_ = v___x_2859_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2889_; 
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2889_ == 0)
{
lean_object* v_unused_2890_; lean_object* v_unused_2891_; lean_object* v_unused_2892_; 
v_unused_2890_ = lean_ctor_get(v___x_2859_, 2);
lean_dec(v_unused_2890_);
v_unused_2891_ = lean_ctor_get(v___x_2859_, 1);
lean_dec(v_unused_2891_);
v_unused_2892_ = lean_ctor_get(v___x_2859_, 0);
lean_dec(v_unused_2892_);
v___x_2872_ = v___x_2859_;
v_isShared_2873_ = v_isSharedCheck_2889_;
goto v_resetjp_2871_;
}
else
{
lean_dec(v___x_2859_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2889_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2874_ = lean_unsigned_to_nat(1u);
v___x_2875_ = lean_nat_dec_eq(v_remaining_2866_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2876_ = lean_box(v___x_2875_);
lean_inc(v_value_2864_);
v___x_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2877_, 0, v_value_2864_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_nat_sub(v_remaining_2866_, v___x_2874_);
lean_dec(v_remaining_2866_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 2, v___x_2878_);
v___x_2880_ = v___x_2872_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_value_2864_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_pos_2865_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
v_fst_2861_ = v___x_2877_;
v_snd_2862_ = v___x_2880_;
goto v___jp_2860_;
}
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
lean_dec(v_remaining_2866_);
v___x_2882_ = lean_box(v___x_2867_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_value_2864_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_box(0);
v___x_2885_ = lean_unsigned_to_nat(0u);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 2, v___x_2885_);
lean_ctor_set(v___x_2872_, 0, v___x_2884_);
v___x_2887_ = v___x_2872_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_pos_2865_);
lean_ctor_set(v_reuseFailAlloc_2888_, 2, v___x_2885_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
v_fst_2861_ = v___x_2883_;
v_snd_2862_ = v___x_2887_;
goto v___jp_2860_;
}
}
}
}
v___jp_2860_:
{
lean_object* v___x_2863_; 
v___x_2863_ = lean_st_ref_set(v_slot_2856_, v_snd_2862_);
return v_fst_2861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_2893_, lean_object* v_next_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_2893_, v_next_2894_);
lean_dec(v_next_2894_);
lean_dec(v_slot_2893_);
return v_res_2896_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2899_; lean_object* v_size_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2899_ = lean_st_ref_get(v_a_2897_);
v_size_2900_ = lean_ctor_get(v___x_2899_, 3);
lean_inc(v_size_2900_);
lean_dec(v___x_2899_);
v___x_2901_ = lean_unsigned_to_nat(0u);
v___x_2902_ = lean_nat_dec_eq(v_size_2900_, v___x_2901_);
lean_dec(v_size_2900_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_2903_, lean_object* v___y_2904_){
_start:
{
uint8_t v_res_2905_; lean_object* v_r_2906_; 
v_res_2905_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_2903_);
lean_dec(v_a_2903_);
v_r_2906_ = lean_box(v_res_2905_);
return v_r_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v___x_2910_; lean_object* v_capacity_2911_; lean_object* v_buffer_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2910_ = lean_st_ref_get(v_a_2908_);
v_capacity_2911_ = lean_ctor_get(v___x_2910_, 2);
lean_inc(v_capacity_2911_);
v_buffer_2912_ = lean_ctor_get(v___x_2910_, 4);
lean_inc_ref(v_buffer_2912_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_nat_mod(v_place_2907_, v_capacity_2911_);
lean_dec(v_capacity_2911_);
v___x_2914_ = lean_array_fget(v_buffer_2912_, v___x_2913_);
lean_dec(v___x_2913_);
lean_dec_ref(v_buffer_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_2915_, lean_object* v_a_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec(v_place_2915_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = lean_st_ref_get(v_a_2920_);
v___x_2923_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_2920_);
if (v___x_2923_ == 0)
{
lean_object* v_capacity_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v_fst_2928_; lean_object* v_snd_2929_; lean_object* v_st_2931_; lean_object* v___y_2932_; 
v_capacity_2924_ = lean_ctor_get(v___x_2922_, 2);
lean_inc(v_capacity_2924_);
v___x_2925_ = lean_nat_mod(v_next_2919_, v_capacity_2924_);
lean_dec(v_capacity_2924_);
v___x_2926_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_2925_, v_a_2920_);
lean_dec(v___x_2925_);
v___x_2927_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_2926_, v_next_2919_);
lean_dec(v___x_2926_);
v_fst_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_fst_2928_);
v_snd_2929_ = lean_ctor_get(v___x_2927_, 1);
lean_inc(v_snd_2929_);
lean_dec_ref(v___x_2927_);
if (lean_obj_tag(v_fst_2928_) == 1)
{
uint8_t v___x_2934_; 
v___x_2934_ = lean_unbox(v_snd_2929_);
if (v___x_2934_ == 0)
{
lean_dec(v_snd_2929_);
v_st_2931_ = v___x_2922_;
v___y_2932_ = v_a_2920_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2935_; lean_object* v_producers_2936_; lean_object* v_waiters_2937_; lean_object* v_capacity_2938_; lean_object* v_size_2939_; lean_object* v_buffer_2940_; lean_object* v_write_2941_; lean_object* v_read_2942_; lean_object* v_receivers_2943_; lean_object* v_nextId_2944_; uint8_t v_closed_2945_; lean_object* v_pos_2946_; lean_object* v___x_2947_; 
v___x_2935_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_2922_);
v_producers_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_ref(v_producers_2936_);
v_waiters_2937_ = lean_ctor_get(v___x_2935_, 1);
lean_inc_ref(v_waiters_2937_);
v_capacity_2938_ = lean_ctor_get(v___x_2935_, 2);
lean_inc(v_capacity_2938_);
v_size_2939_ = lean_ctor_get(v___x_2935_, 3);
lean_inc(v_size_2939_);
v_buffer_2940_ = lean_ctor_get(v___x_2935_, 4);
lean_inc_ref(v_buffer_2940_);
v_write_2941_ = lean_ctor_get(v___x_2935_, 5);
lean_inc(v_write_2941_);
v_read_2942_ = lean_ctor_get(v___x_2935_, 6);
lean_inc(v_read_2942_);
v_receivers_2943_ = lean_ctor_get(v___x_2935_, 7);
lean_inc(v_receivers_2943_);
v_nextId_2944_ = lean_ctor_get(v___x_2935_, 8);
lean_inc(v_nextId_2944_);
v_closed_2945_ = lean_ctor_get_uint8(v___x_2935_, sizeof(void*)*10);
v_pos_2946_ = lean_ctor_get(v___x_2935_, 9);
lean_inc(v_pos_2946_);
v___x_2947_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_2936_);
if (lean_obj_tag(v___x_2947_) == 1)
{
lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2958_; 
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; lean_object* v_unused_2960_; lean_object* v_unused_2961_; lean_object* v_unused_2962_; lean_object* v_unused_2963_; lean_object* v_unused_2964_; lean_object* v_unused_2965_; lean_object* v_unused_2966_; lean_object* v_unused_2967_; lean_object* v_unused_2968_; 
v_unused_2959_ = lean_ctor_get(v___x_2935_, 9);
lean_dec(v_unused_2959_);
v_unused_2960_ = lean_ctor_get(v___x_2935_, 8);
lean_dec(v_unused_2960_);
v_unused_2961_ = lean_ctor_get(v___x_2935_, 7);
lean_dec(v_unused_2961_);
v_unused_2962_ = lean_ctor_get(v___x_2935_, 6);
lean_dec(v_unused_2962_);
v_unused_2963_ = lean_ctor_get(v___x_2935_, 5);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v___x_2935_, 4);
lean_dec(v_unused_2964_);
v_unused_2965_ = lean_ctor_get(v___x_2935_, 3);
lean_dec(v_unused_2965_);
v_unused_2966_ = lean_ctor_get(v___x_2935_, 2);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v___x_2935_, 1);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v___x_2935_, 0);
lean_dec(v_unused_2968_);
v___x_2949_ = v___x_2935_;
v_isShared_2950_ = v_isSharedCheck_2958_;
goto v_resetjp_2948_;
}
else
{
lean_dec(v___x_2935_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2958_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_val_2951_; lean_object* v_fst_2952_; lean_object* v_snd_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v_val_2951_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_val_2951_);
lean_dec_ref(v___x_2947_);
v_fst_2952_ = lean_ctor_get(v_val_2951_, 0);
lean_inc(v_fst_2952_);
v_snd_2953_ = lean_ctor_get(v_val_2951_, 1);
lean_inc(v_snd_2953_);
lean_dec(v_val_2951_);
v___x_2954_ = lean_io_promise_resolve(v_snd_2929_, v_fst_2952_);
lean_dec(v_fst_2952_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v_snd_2953_);
v___x_2956_ = v___x_2949_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_snd_2953_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_waiters_2937_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_capacity_2938_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_size_2939_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_buffer_2940_);
lean_ctor_set(v_reuseFailAlloc_2957_, 5, v_write_2941_);
lean_ctor_set(v_reuseFailAlloc_2957_, 6, v_read_2942_);
lean_ctor_set(v_reuseFailAlloc_2957_, 7, v_receivers_2943_);
lean_ctor_set(v_reuseFailAlloc_2957_, 8, v_nextId_2944_);
lean_ctor_set(v_reuseFailAlloc_2957_, 9, v_pos_2946_);
lean_ctor_set_uint8(v_reuseFailAlloc_2957_, sizeof(void*)*10, v_closed_2945_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
v_st_2931_ = v___x_2956_;
v___y_2932_ = v_a_2920_;
goto v___jp_2930_;
}
}
}
else
{
lean_dec(v___x_2947_);
lean_dec(v_pos_2946_);
lean_dec(v_nextId_2944_);
lean_dec(v_receivers_2943_);
lean_dec(v_read_2942_);
lean_dec(v_write_2941_);
lean_dec_ref(v_buffer_2940_);
lean_dec(v_size_2939_);
lean_dec(v_capacity_2938_);
lean_dec_ref(v_waiters_2937_);
lean_dec(v_snd_2929_);
v_st_2931_ = v___x_2935_;
v___y_2932_ = v_a_2920_;
goto v___jp_2930_;
}
}
}
else
{
lean_object* v___x_2969_; 
lean_dec(v_snd_2929_);
lean_dec(v_fst_2928_);
lean_dec(v___x_2922_);
v___x_2969_ = lean_box(0);
return v___x_2969_;
}
v___jp_2930_:
{
lean_object* v___x_2933_; 
v___x_2933_ = lean_st_ref_set(v___y_2932_, v_st_2931_);
return v_fst_2928_;
}
}
else
{
lean_object* v___x_2970_; 
lean_dec(v___x_2922_);
v___x_2970_ = lean_box(0);
return v___x_2970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_2971_, lean_object* v_a_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_2971_, v_a_2972_);
lean_dec(v_a_2972_);
lean_dec(v_next_2971_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v___x_2978_; lean_object* v_receivers_2979_; lean_object* v___x_2980_; 
v___x_2978_ = lean_st_ref_get(v_a_2976_);
v_receivers_2979_ = lean_ctor_get(v___x_2978_, 7);
lean_inc(v_receivers_2979_);
lean_dec(v___x_2978_);
v___x_2980_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2979_, v_receiverId_2975_);
if (lean_obj_tag(v___x_2980_) == 1)
{
lean_object* v_val_2981_; lean_object* v___x_2982_; 
v_val_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_val_2981_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_2981_, v_a_2976_);
lean_dec(v_val_2981_);
if (lean_obj_tag(v___x_2982_) == 1)
{
lean_object* v___x_2983_; lean_object* v_producers_2984_; lean_object* v_waiters_2985_; lean_object* v_capacity_2986_; lean_object* v_size_2987_; lean_object* v_buffer_2988_; lean_object* v_write_2989_; lean_object* v_read_2990_; lean_object* v_nextId_2991_; uint8_t v_closed_2992_; lean_object* v_pos_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3002_; 
v___x_2983_ = lean_st_ref_take(v_a_2976_);
v_producers_2984_ = lean_ctor_get(v___x_2983_, 0);
v_waiters_2985_ = lean_ctor_get(v___x_2983_, 1);
v_capacity_2986_ = lean_ctor_get(v___x_2983_, 2);
v_size_2987_ = lean_ctor_get(v___x_2983_, 3);
v_buffer_2988_ = lean_ctor_get(v___x_2983_, 4);
v_write_2989_ = lean_ctor_get(v___x_2983_, 5);
v_read_2990_ = lean_ctor_get(v___x_2983_, 6);
v_nextId_2991_ = lean_ctor_get(v___x_2983_, 8);
v_closed_2992_ = lean_ctor_get_uint8(v___x_2983_, sizeof(void*)*10);
v_pos_2993_ = lean_ctor_get(v___x_2983_, 9);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; 
v_unused_3003_ = lean_ctor_get(v___x_2983_, 7);
lean_dec(v_unused_3003_);
v___x_2995_ = v___x_2983_;
v_isShared_2996_ = v_isSharedCheck_3002_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_pos_2993_);
lean_inc(v_nextId_2991_);
lean_inc(v_read_2990_);
lean_inc(v_write_2989_);
lean_inc(v_buffer_2988_);
lean_inc(v_size_2987_);
lean_inc(v_capacity_2986_);
lean_inc(v_waiters_2985_);
lean_inc(v_producers_2984_);
lean_dec(v___x_2983_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3002_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; lean_object* v___x_2999_; 
v___x_2997_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_2975_, v_receivers_2979_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 7, v___x_2997_);
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_producers_2984_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_waiters_2985_);
lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_capacity_2986_);
lean_ctor_set(v_reuseFailAlloc_3001_, 3, v_size_2987_);
lean_ctor_set(v_reuseFailAlloc_3001_, 4, v_buffer_2988_);
lean_ctor_set(v_reuseFailAlloc_3001_, 5, v_write_2989_);
lean_ctor_set(v_reuseFailAlloc_3001_, 6, v_read_2990_);
lean_ctor_set(v_reuseFailAlloc_3001_, 7, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3001_, 8, v_nextId_2991_);
lean_ctor_set(v_reuseFailAlloc_3001_, 9, v_pos_2993_);
lean_ctor_set_uint8(v_reuseFailAlloc_3001_, sizeof(void*)*10, v_closed_2992_);
v___x_2999_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_st_ref_set(v_a_2976_, v___x_2999_);
return v___x_2982_;
}
}
}
else
{
lean_object* v___x_3004_; 
lean_dec(v___x_2982_);
lean_dec(v_receivers_2979_);
lean_dec(v_receiverId_2975_);
v___x_3004_ = lean_box(0);
return v___x_3004_;
}
}
else
{
lean_object* v___x_3005_; 
lean_dec(v___x_2980_);
lean_dec(v_receivers_2979_);
lean_dec(v_receiverId_2975_);
v___x_3005_ = lean_box(0);
return v___x_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3006_, lean_object* v_a_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3006_, v_a_3007_);
lean_dec(v_a_3007_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3010_, v___y_3011_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3014_, v___y_3015_);
lean_dec(v___y_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3018_){
_start:
{
lean_object* v_state_3020_; lean_object* v_id_3021_; lean_object* v___f_3022_; lean_object* v___x_3023_; 
v_state_3020_ = lean_ctor_get(v_ch_3018_, 0);
lean_inc_ref(v_state_3020_);
v_id_3021_ = lean_ctor_get(v_ch_3018_, 1);
lean_inc(v_id_3021_);
lean_dec_ref(v_ch_3018_);
v___f_3022_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3022_, 0, v_id_3021_);
v___x_3023_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3020_, v___f_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3024_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3027_, lean_object* v_ch_3028_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3028_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3031_, lean_object* v_ch_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3031_, v_ch_3032_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3035_, lean_object* v_receiverId_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3036_, v_a_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_receiverId_3041_, lean_object* v_a_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3040_, v_receiverId_3041_, v_a_3042_);
lean_dec(v_a_3042_);
return v_res_3044_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3045_, lean_object* v_a_3046_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3046_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3049_, lean_object* v_a_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v_res_3052_; lean_object* v_r_3053_; 
v_res_3052_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3049_, v_a_3050_);
lean_dec(v_a_3050_);
v_r_3053_ = lean_box(v_res_3052_);
return v_r_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3054_, lean_object* v_place_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3055_, v_a_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3059_, lean_object* v_place_3060_, lean_object* v_a_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3059_, v_place_3060_, v_a_3061_);
lean_dec(v_a_3061_);
lean_dec(v_place_3060_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3064_, lean_object* v_slot_3065_, lean_object* v_next_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3065_, v_next_3066_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3070_, lean_object* v_slot_3071_, lean_object* v_next_3072_, lean_object* v_a_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3070_, v_slot_3071_, v_next_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec(v_next_3072_);
lean_dec(v_slot_3071_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3076_, lean_object* v_next_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3077_, v_a_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3081_, lean_object* v_next_3082_, lean_object* v_a_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3081_, v_next_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec(v_next_3082_);
return v_res_3085_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3086_, lean_object* v_t_3087_){
_start:
{
if (lean_obj_tag(v_t_3087_) == 0)
{
lean_object* v_k_3088_; lean_object* v_l_3089_; lean_object* v_r_3090_; uint8_t v___x_3091_; 
v_k_3088_ = lean_ctor_get(v_t_3087_, 1);
v_l_3089_ = lean_ctor_get(v_t_3087_, 3);
v_r_3090_ = lean_ctor_get(v_t_3087_, 4);
v___x_3091_ = lean_nat_dec_lt(v_k_3086_, v_k_3088_);
if (v___x_3091_ == 0)
{
uint8_t v___x_3092_; 
v___x_3092_ = lean_nat_dec_eq(v_k_3086_, v_k_3088_);
if (v___x_3092_ == 0)
{
v_t_3087_ = v_r_3090_;
goto _start;
}
else
{
return v___x_3092_;
}
}
else
{
v_t_3087_ = v_l_3089_;
goto _start;
}
}
else
{
uint8_t v___x_3095_; 
v___x_3095_ = 0;
return v___x_3095_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3096_, lean_object* v_t_3097_){
_start:
{
uint8_t v_res_3098_; lean_object* v_r_3099_; 
v_res_3098_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3096_, v_t_3097_);
lean_dec(v_t_3097_);
lean_dec(v_k_3096_);
v_r_3099_ = lean_box(v_res_3098_);
return v_r_3099_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = lean_box(0);
v___x_3101_ = lean_task_pure(v___x_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3102_, lean_object* v___f_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v___x_3106_; lean_object* v_receivers_3107_; uint8_t v___x_3108_; 
v___x_3106_ = lean_st_ref_get(v___y_3104_);
v_receivers_3107_ = lean_ctor_get(v___x_3106_, 7);
lean_inc(v_receivers_3107_);
lean_dec(v___x_3106_);
v___x_3108_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3102_, v_receivers_3107_);
lean_dec(v_receivers_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
lean_dec_ref(v___f_3103_);
lean_dec(v_id_3102_);
v___x_3109_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3102_, v___y_3104_);
if (lean_obj_tag(v___x_3110_) == 1)
{
lean_object* v___x_3111_; 
lean_dec_ref(v___f_3103_);
v___x_3111_ = lean_task_pure(v___x_3110_);
return v___x_3111_;
}
else
{
lean_object* v___x_3112_; uint8_t v_closed_3113_; 
lean_dec(v___x_3110_);
v___x_3112_ = lean_st_ref_get(v___y_3104_);
v_closed_3113_ = lean_ctor_get_uint8(v___x_3112_, sizeof(void*)*10);
lean_dec(v___x_3112_);
if (v_closed_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_producers_3116_; lean_object* v_waiters_3117_; lean_object* v_capacity_3118_; lean_object* v_size_3119_; lean_object* v_buffer_3120_; lean_object* v_write_3121_; lean_object* v_read_3122_; lean_object* v_receivers_3123_; lean_object* v_nextId_3124_; uint8_t v_closed_3125_; lean_object* v_pos_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3140_; 
v___x_3114_ = lean_io_promise_new();
v___x_3115_ = lean_st_ref_take(v___y_3104_);
v_producers_3116_ = lean_ctor_get(v___x_3115_, 0);
v_waiters_3117_ = lean_ctor_get(v___x_3115_, 1);
v_capacity_3118_ = lean_ctor_get(v___x_3115_, 2);
v_size_3119_ = lean_ctor_get(v___x_3115_, 3);
v_buffer_3120_ = lean_ctor_get(v___x_3115_, 4);
v_write_3121_ = lean_ctor_get(v___x_3115_, 5);
v_read_3122_ = lean_ctor_get(v___x_3115_, 6);
v_receivers_3123_ = lean_ctor_get(v___x_3115_, 7);
v_nextId_3124_ = lean_ctor_get(v___x_3115_, 8);
v_closed_3125_ = lean_ctor_get_uint8(v___x_3115_, sizeof(void*)*10);
v_pos_3126_ = lean_ctor_get(v___x_3115_, 9);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3128_ = v___x_3115_;
v_isShared_3129_ = v_isSharedCheck_3140_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_pos_3126_);
lean_inc(v_nextId_3124_);
lean_inc(v_receivers_3123_);
lean_inc(v_read_3122_);
lean_inc(v_write_3121_);
lean_inc(v_buffer_3120_);
lean_inc(v_size_3119_);
lean_inc(v_capacity_3118_);
lean_inc(v_waiters_3117_);
lean_inc(v_producers_3116_);
lean_dec(v___x_3115_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3140_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3130_ = lean_box(0);
lean_inc(v___x_3114_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3114_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
v___x_3132_ = l_Std_Queue_enqueue___redArg(v___x_3131_, v_waiters_3117_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 1, v___x_3132_);
v___x_3134_ = v___x_3128_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_producers_3116_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_capacity_3118_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_size_3119_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_buffer_3120_);
lean_ctor_set(v_reuseFailAlloc_3139_, 5, v_write_3121_);
lean_ctor_set(v_reuseFailAlloc_3139_, 6, v_read_3122_);
lean_ctor_set(v_reuseFailAlloc_3139_, 7, v_receivers_3123_);
lean_ctor_set(v_reuseFailAlloc_3139_, 8, v_nextId_3124_);
lean_ctor_set(v_reuseFailAlloc_3139_, 9, v_pos_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3139_, sizeof(void*)*10, v_closed_3125_);
v___x_3134_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3135_ = lean_st_ref_set(v___y_3104_, v___x_3134_);
v___x_3136_ = lean_io_promise_result_opt(v___x_3114_);
lean_dec(v___x_3114_);
v___x_3137_ = lean_unsigned_to_nat(0u);
v___x_3138_ = lean_io_bind_task(v___x_3136_, v___f_3103_, v___x_3137_, v_closed_3113_);
return v___x_3138_;
}
}
}
else
{
lean_object* v___x_3141_; 
lean_dec_ref(v___f_3103_);
v___x_3141_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3142_, lean_object* v___f_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3142_, v___f_3143_, v___y_3144_);
lean_dec(v___y_3144_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3147_, lean_object* v_res_3148_){
_start:
{
if (lean_obj_tag(v_res_3148_) == 0)
{
lean_dec_ref(v_ch_3147_);
goto v___jp_3150_;
}
else
{
lean_object* v_val_3152_; uint8_t v___x_3153_; 
v_val_3152_ = lean_ctor_get(v_res_3148_, 0);
v___x_3153_ = lean_unbox(v_val_3152_);
if (v___x_3153_ == 0)
{
lean_dec_ref(v_ch_3147_);
goto v___jp_3150_;
}
else
{
lean_object* v___x_3154_; 
v___x_3154_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3147_);
return v___x_3154_;
}
}
v___jp_3150_:
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3155_, lean_object* v_res_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3155_, v_res_3156_);
lean_dec(v_res_3156_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3159_){
_start:
{
lean_object* v_state_3161_; lean_object* v_id_3162_; lean_object* v___f_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; 
v_state_3161_ = lean_ctor_get(v_ch_3159_, 0);
lean_inc_ref(v_state_3161_);
v_id_3162_ = lean_ctor_get(v_ch_3159_, 1);
lean_inc(v_id_3162_);
v___f_3163_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3163_, 0, v_ch_3159_);
v___f_3164_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3164_, 0, v_id_3162_);
lean_closure_set(v___f_3164_, 1, v___f_3163_);
v___x_3165_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3161_, v___f_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3166_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3169_, lean_object* v_ch_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3173_, lean_object* v_ch_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3173_, v_ch_3174_);
return v_res_3176_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3177_, lean_object* v_k_3178_, lean_object* v_t_3179_){
_start:
{
uint8_t v___x_3180_; 
v___x_3180_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3178_, v_t_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3181_, lean_object* v_k_3182_, lean_object* v_t_3183_){
_start:
{
uint8_t v_res_3184_; lean_object* v_r_3185_; 
v_res_3184_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3181_, v_k_3182_, v_t_3183_);
lean_dec(v_t_3183_);
lean_dec(v_k_3182_);
v_r_3185_ = lean_box(v_res_3184_);
return v_r_3185_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_box(0);
v___x_3187_ = lean_task_pure(v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3188_, lean_object* v_ch_3189_, lean_object* v_prio_3190_, lean_object* v_x_3191_){
_start:
{
if (lean_obj_tag(v_x_3191_) == 0)
{
lean_object* v___x_3193_; 
lean_dec(v_prio_3190_);
lean_dec_ref(v_ch_3189_);
lean_dec_ref(v_f_3188_);
v___x_3193_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3193_;
}
else
{
lean_object* v_val_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_val_3194_ = lean_ctor_get(v_x_3191_, 0);
lean_inc(v_val_3194_);
lean_dec_ref(v_x_3191_);
lean_inc_ref(v_f_3188_);
v___x_3195_ = lean_apply_2(v_f_3188_, v_val_3194_, lean_box(0));
v___x_3196_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3188_, v_ch_3189_, v_prio_3190_);
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3197_, lean_object* v_ch_3198_, lean_object* v_prio_3199_, lean_object* v_x_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3197_, v_ch_3198_, v_prio_3199_, v_x_3200_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3203_, lean_object* v_ch_3204_, lean_object* v_prio_3205_){
_start:
{
lean_object* v___x_3207_; lean_object* v___f_3208_; uint8_t v___x_3209_; lean_object* v___x_3210_; 
lean_inc_ref(v_ch_3204_);
v___x_3207_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3204_);
lean_inc(v_prio_3205_);
v___f_3208_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3208_, 0, v_f_3203_);
lean_closure_set(v___f_3208_, 1, v_ch_3204_);
lean_closure_set(v___f_3208_, 2, v_prio_3205_);
v___x_3209_ = 0;
v___x_3210_ = lean_io_bind_task(v___x_3207_, v___f_3208_, v_prio_3205_, v___x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3211_, lean_object* v_ch_3212_, lean_object* v_prio_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3211_, v_ch_3212_, v_prio_3213_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3216_, lean_object* v_f_3217_, lean_object* v_ch_3218_, lean_object* v_prio_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3217_, v_ch_3218_, v_prio_3219_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3222_, lean_object* v_f_3223_, lean_object* v_ch_3224_, lean_object* v_prio_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3222_, v_f_3223_, v_ch_3224_, v_prio_3225_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3228_, lean_object* v_val_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v_pos_3231_; lean_object* v_toPure_3232_; uint8_t v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_pos_3231_ = lean_ctor_get(v_a_3230_, 1);
v_toPure_3232_ = lean_ctor_get(v_toApplicative_3228_, 1);
lean_inc(v_toPure_3232_);
lean_dec_ref(v_toApplicative_3228_);
v___x_3233_ = lean_nat_dec_eq(v_pos_3231_, v_val_3229_);
v___x_3234_ = lean_box(v___x_3233_);
v___x_3235_ = lean_apply_2(v_toPure_3232_, lean_box(0), v___x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3236_, lean_object* v_val_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3236_, v_val_3237_, v_a_3238_);
lean_dec_ref(v_a_3238_);
lean_dec(v_val_3237_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3240_, lean_object* v_toBind_3241_, lean_object* v___f_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3244_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3244_, 0, lean_box(0));
lean_closure_set(v___x_3244_, 1, lean_box(0));
lean_closure_set(v___x_3244_, 2, v_a_3243_);
v___x_3245_ = lean_apply_2(v_inst_3240_, lean_box(0), v___x_3244_);
v___x_3246_ = lean_apply_4(v_toBind_3241_, lean_box(0), lean_box(0), v___x_3245_, v___f_3242_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3247_, lean_object* v_receiverId_3248_, lean_object* v_toApplicative_3249_, lean_object* v_inst_3250_, lean_object* v_toBind_3251_, lean_object* v_inst_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
uint8_t v_closed_3255_; 
v_closed_3255_ = lean_ctor_get_uint8(v_a_3254_, sizeof(void*)*10);
if (v_closed_3255_ == 0)
{
lean_object* v_capacity_3256_; lean_object* v_size_3257_; lean_object* v_receivers_3258_; lean_object* v___x_3259_; 
v_capacity_3256_ = lean_ctor_get(v_a_3254_, 2);
lean_inc(v_capacity_3256_);
v_size_3257_ = lean_ctor_get(v_a_3254_, 3);
lean_inc(v_size_3257_);
v_receivers_3258_ = lean_ctor_get(v_a_3254_, 7);
lean_inc(v_receivers_3258_);
lean_dec_ref(v_a_3254_);
v___x_3259_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3247_, v_receivers_3258_, v_receiverId_3248_);
if (lean_obj_tag(v___x_3259_) == 1)
{
lean_object* v_val_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v_val_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_val_3260_);
lean_dec_ref(v___x_3259_);
v___x_3261_ = lean_unsigned_to_nat(0u);
v___x_3262_ = lean_nat_dec_eq(v_size_3257_, v___x_3261_);
lean_dec(v_size_3257_);
if (v___x_3262_ == 0)
{
lean_object* v___f_3263_; lean_object* v___f_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_inc(v_val_3260_);
v___f_3263_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3263_, 0, v_toApplicative_3249_);
lean_closure_set(v___f_3263_, 1, v_val_3260_);
lean_inc(v_toBind_3251_);
lean_inc(v_inst_3250_);
v___f_3264_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3264_, 0, v_inst_3250_);
lean_closure_set(v___f_3264_, 1, v_toBind_3251_);
lean_closure_set(v___f_3264_, 2, v___f_3263_);
v___x_3265_ = lean_nat_mod(v_val_3260_, v_capacity_3256_);
lean_dec(v_capacity_3256_);
lean_dec(v_val_3260_);
v___x_3266_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3252_, v_inst_3250_, v___x_3265_, v_a_3253_);
v___x_3267_ = lean_apply_4(v_toBind_3251_, lean_box(0), lean_box(0), v___x_3266_, v___f_3264_);
return v___x_3267_;
}
else
{
lean_object* v_toPure_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec(v_val_3260_);
lean_dec(v_capacity_3256_);
lean_dec(v_a_3253_);
lean_dec_ref(v_inst_3252_);
lean_dec(v_toBind_3251_);
lean_dec(v_inst_3250_);
v_toPure_3268_ = lean_ctor_get(v_toApplicative_3249_, 1);
lean_inc(v_toPure_3268_);
lean_dec_ref(v_toApplicative_3249_);
v___x_3269_ = lean_box(v_closed_3255_);
v___x_3270_ = lean_apply_2(v_toPure_3268_, lean_box(0), v___x_3269_);
return v___x_3270_;
}
}
else
{
lean_object* v_toPure_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v___x_3259_);
lean_dec(v_size_3257_);
lean_dec(v_capacity_3256_);
lean_dec(v_a_3253_);
lean_dec_ref(v_inst_3252_);
lean_dec(v_toBind_3251_);
lean_dec(v_inst_3250_);
v_toPure_3271_ = lean_ctor_get(v_toApplicative_3249_, 1);
lean_inc(v_toPure_3271_);
lean_dec_ref(v_toApplicative_3249_);
v___x_3272_ = lean_box(v_closed_3255_);
v___x_3273_ = lean_apply_2(v_toPure_3271_, lean_box(0), v___x_3272_);
return v___x_3273_;
}
}
else
{
lean_object* v_toPure_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_dec_ref(v_a_3254_);
lean_dec(v_a_3253_);
lean_dec_ref(v_inst_3252_);
lean_dec(v_toBind_3251_);
lean_dec(v_inst_3250_);
lean_dec(v_receiverId_3248_);
lean_dec_ref(v___f_3247_);
v_toPure_3274_ = lean_ctor_get(v_toApplicative_3249_, 1);
lean_inc(v_toPure_3274_);
lean_dec_ref(v_toApplicative_3249_);
v___x_3275_ = lean_box(v_closed_3255_);
v___x_3276_ = lean_apply_2(v_toPure_3274_, lean_box(0), v___x_3275_);
return v___x_3276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3277_, lean_object* v_inst_3278_, lean_object* v_receiverId_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v_toApplicative_3281_; lean_object* v_toBind_3282_; lean_object* v___f_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_toApplicative_3281_ = lean_ctor_get(v_inst_3277_, 0);
lean_inc_ref(v_toApplicative_3281_);
v_toBind_3282_ = lean_ctor_get(v_inst_3277_, 1);
lean_inc(v_toBind_3282_);
v___f_3283_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc(v_a_3280_);
lean_inc(v_toBind_3282_);
lean_inc(v_inst_3278_);
v___f_3284_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2), 8, 7);
lean_closure_set(v___f_3284_, 0, v___f_3283_);
lean_closure_set(v___f_3284_, 1, v_receiverId_3279_);
lean_closure_set(v___f_3284_, 2, v_toApplicative_3281_);
lean_closure_set(v___f_3284_, 3, v_inst_3278_);
lean_closure_set(v___f_3284_, 4, v_toBind_3282_);
lean_closure_set(v___f_3284_, 5, v_inst_3277_);
lean_closure_set(v___f_3284_, 6, v_a_3280_);
v___x_3285_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3285_, 0, lean_box(0));
lean_closure_set(v___x_3285_, 1, lean_box(0));
lean_closure_set(v___x_3285_, 2, v_a_3280_);
v___x_3286_ = lean_apply_2(v_inst_3278_, lean_box(0), v___x_3285_);
v___x_3287_ = lean_apply_4(v_toBind_3282_, lean_box(0), lean_box(0), v___x_3286_, v___f_3284_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3288_, lean_object* v_00_u03b1_3289_, lean_object* v_inst_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_inst_3293_, lean_object* v_receiverId_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_toApplicative_3296_; lean_object* v_toBind_3297_; lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_toApplicative_3296_ = lean_ctor_get(v_inst_3290_, 0);
lean_inc_ref(v_toApplicative_3296_);
v_toBind_3297_ = lean_ctor_get(v_inst_3290_, 1);
lean_inc(v_toBind_3297_);
v___f_3298_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc(v_a_3295_);
lean_inc(v_toBind_3297_);
lean_inc(v_inst_3291_);
v___f_3299_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2), 8, 7);
lean_closure_set(v___f_3299_, 0, v___f_3298_);
lean_closure_set(v___f_3299_, 1, v_receiverId_3294_);
lean_closure_set(v___f_3299_, 2, v_toApplicative_3296_);
lean_closure_set(v___f_3299_, 3, v_inst_3291_);
lean_closure_set(v___f_3299_, 4, v_toBind_3297_);
lean_closure_set(v___f_3299_, 5, v_inst_3290_);
lean_closure_set(v___f_3299_, 6, v_a_3295_);
v___x_3300_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3300_, 0, lean_box(0));
lean_closure_set(v___x_3300_, 1, lean_box(0));
lean_closure_set(v___x_3300_, 2, v_a_3295_);
v___x_3301_ = lean_apply_2(v_inst_3291_, lean_box(0), v___x_3300_);
v___x_3302_ = lean_apply_4(v_toBind_3297_, lean_box(0), lean_box(0), v___x_3301_, v___f_3299_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3303_, lean_object* v_00_u03b1_3304_, lean_object* v_inst_3305_, lean_object* v_inst_3306_, lean_object* v_inst_3307_, lean_object* v_inst_3308_, lean_object* v_receiverId_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3303_, v_00_u03b1_3304_, v_inst_3305_, v_inst_3306_, v_inst_3307_, v_inst_3308_, v_receiverId_3309_, v_a_3310_);
lean_dec(v_inst_3308_);
lean_dec(v_inst_3307_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3314_, lean_object* v_lose_3315_){
_start:
{
lean_object* v_finished_3317_; lean_object* v_promise_3318_; lean_object* v___x_3319_; uint8_t v___y_3321_; uint8_t v___x_3329_; 
v_finished_3317_ = lean_ctor_get(v_w_3314_, 0);
v_promise_3318_ = lean_ctor_get(v_w_3314_, 1);
v___x_3319_ = lean_st_ref_take(v_finished_3317_);
v___x_3329_ = lean_unbox(v___x_3319_);
lean_dec(v___x_3319_);
if (v___x_3329_ == 0)
{
uint8_t v___x_3330_; 
v___x_3330_ = 1;
v___y_3321_ = v___x_3330_;
goto v___jp_3320_;
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = 0;
v___y_3321_ = v___x_3331_;
goto v___jp_3320_;
}
v___jp_3320_:
{
uint8_t v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = 1;
v___x_3323_ = lean_box(v___x_3322_);
v___x_3324_ = lean_st_ref_set(v_finished_3317_, v___x_3323_);
if (v___y_3321_ == 0)
{
lean_object* v___x_3325_; 
v___x_3325_ = lean_apply_1(v_lose_3315_, lean_box(0));
return v___x_3325_;
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec_ref(v_lose_3315_);
v___x_3326_ = ((lean_object*)(l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3327_ = lean_io_promise_resolve(v___x_3326_, v_promise_3318_);
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
return v___x_3328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3332_, lean_object* v_lose_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3332_, v_lose_3333_);
lean_dec_ref(v_w_3332_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3336_, lean_object* v_w_3337_, lean_object* v_lose_3338_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3337_, v_lose_3338_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3341_, lean_object* v_w_3342_, lean_object* v_lose_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3341_, v_w_3342_, v_lose_3343_);
lean_dec_ref(v_w_3342_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v___x_3349_; lean_object* v_receivers_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_st_ref_get(v_a_3347_);
v_receivers_3350_ = lean_ctor_get(v___x_3349_, 7);
lean_inc(v_receivers_3350_);
lean_dec(v___x_3349_);
v___x_3351_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3350_, v_receiverId_3346_);
if (lean_obj_tag(v___x_3351_) == 1)
{
lean_object* v_val_3352_; lean_object* v___x_3353_; 
v_val_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_val_3352_);
lean_dec_ref(v___x_3351_);
v___x_3353_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3352_, v_a_3347_);
lean_dec(v_val_3352_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3386_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3386_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3386_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
if (lean_obj_tag(v_a_3354_) == 1)
{
lean_object* v___x_3358_; lean_object* v_producers_3359_; lean_object* v_waiters_3360_; lean_object* v_capacity_3361_; lean_object* v_size_3362_; lean_object* v_buffer_3363_; lean_object* v_write_3364_; lean_object* v_read_3365_; lean_object* v_nextId_3366_; uint8_t v_closed_3367_; lean_object* v_pos_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3380_; 
v___x_3358_ = lean_st_ref_take(v_a_3347_);
v_producers_3359_ = lean_ctor_get(v___x_3358_, 0);
v_waiters_3360_ = lean_ctor_get(v___x_3358_, 1);
v_capacity_3361_ = lean_ctor_get(v___x_3358_, 2);
v_size_3362_ = lean_ctor_get(v___x_3358_, 3);
v_buffer_3363_ = lean_ctor_get(v___x_3358_, 4);
v_write_3364_ = lean_ctor_get(v___x_3358_, 5);
v_read_3365_ = lean_ctor_get(v___x_3358_, 6);
v_nextId_3366_ = lean_ctor_get(v___x_3358_, 8);
v_closed_3367_ = lean_ctor_get_uint8(v___x_3358_, sizeof(void*)*10);
v_pos_3368_ = lean_ctor_get(v___x_3358_, 9);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v___x_3358_, 7);
lean_dec(v_unused_3381_);
v___x_3370_ = v___x_3358_;
v_isShared_3371_ = v_isSharedCheck_3380_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_pos_3368_);
lean_inc(v_nextId_3366_);
lean_inc(v_read_3365_);
lean_inc(v_write_3364_);
lean_inc(v_buffer_3363_);
lean_inc(v_size_3362_);
lean_inc(v_capacity_3361_);
lean_inc(v_waiters_3360_);
lean_inc(v_producers_3359_);
lean_dec(v___x_3358_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3380_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3346_, v_receivers_3350_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 7, v___x_3372_);
v___x_3374_ = v___x_3370_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_producers_3359_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_waiters_3360_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_capacity_3361_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_size_3362_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_buffer_3363_);
lean_ctor_set(v_reuseFailAlloc_3379_, 5, v_write_3364_);
lean_ctor_set(v_reuseFailAlloc_3379_, 6, v_read_3365_);
lean_ctor_set(v_reuseFailAlloc_3379_, 7, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3379_, 8, v_nextId_3366_);
lean_ctor_set(v_reuseFailAlloc_3379_, 9, v_pos_3368_);
lean_ctor_set_uint8(v_reuseFailAlloc_3379_, sizeof(void*)*10, v_closed_3367_);
v___x_3374_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_st_ref_set(v_a_3347_, v___x_3374_);
if (v_isShared_3357_ == 0)
{
v___x_3377_ = v___x_3356_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3354_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v___x_3382_; lean_object* v___x_3384_; 
lean_dec(v_a_3354_);
lean_dec(v_receivers_3350_);
lean_dec(v_receiverId_3346_);
v___x_3382_ = lean_box(0);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3382_);
v___x_3384_ = v___x_3356_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_dec(v_receivers_3350_);
lean_dec(v_receiverId_3346_);
return v___x_3353_;
}
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec(v___x_3351_);
lean_dec(v_receivers_3350_);
lean_dec(v_receiverId_3346_);
v___x_3387_ = lean_box(0);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3389_, lean_object* v_a_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3389_, v_a_3390_);
lean_dec(v_a_3390_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3393_, lean_object* v_w_3394_, lean_object* v_lose_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_finished_3398_; lean_object* v_promise_3399_; lean_object* v___x_3400_; uint8_t v___y_3402_; uint8_t v___x_3426_; 
v_finished_3398_ = lean_ctor_get(v_w_3394_, 0);
v_promise_3399_ = lean_ctor_get(v_w_3394_, 1);
v___x_3400_ = lean_st_ref_take(v_finished_3398_);
v___x_3426_ = lean_unbox(v___x_3400_);
lean_dec(v___x_3400_);
if (v___x_3426_ == 0)
{
uint8_t v___x_3427_; 
v___x_3427_ = 1;
v___y_3402_ = v___x_3427_;
goto v___jp_3401_;
}
else
{
uint8_t v___x_3428_; 
v___x_3428_ = 0;
v___y_3402_ = v___x_3428_;
goto v___jp_3401_;
}
v___jp_3401_:
{
uint8_t v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = 1;
v___x_3404_ = lean_box(v___x_3403_);
v___x_3405_ = lean_st_ref_set(v_finished_3398_, v___x_3404_);
if (v___y_3402_ == 0)
{
lean_object* v___x_3406_; 
lean_dec(v___x_3393_);
v___x_3406_ = lean_apply_2(v_lose_3395_, v___y_3396_, lean_box(0));
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; 
lean_dec_ref(v_lose_3395_);
v___x_3407_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3393_, v___y_3396_);
lean_dec(v___y_3396_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3417_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3417_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3417_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3412_, 0, v_a_3408_);
v___x_3413_ = lean_io_promise_resolve(v___x_3412_, v_promise_3399_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3413_);
v___x_3415_ = v___x_3410_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
v_a_3418_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3407_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3407_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3429_, lean_object* v_w_3430_, lean_object* v_lose_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3429_, v_w_3430_, v_lose_3431_, v___y_3432_);
lean_dec_ref(v_w_3430_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3435_, lean_object* v___x_3436_, lean_object* v_w_3437_, lean_object* v_lose_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3436_, v_w_3437_, v_lose_3438_, v___y_3439_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3442_, lean_object* v___x_3443_, lean_object* v_w_3444_, lean_object* v_lose_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3442_, v___x_3443_, v_w_3444_, v_lose_3445_, v___y_3446_);
lean_dec_ref(v_w_3444_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3449_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3452_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3455_, lean_object* v___f_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; uint8_t v_closed_3460_; 
v___x_3459_ = lean_st_ref_get(v___y_3457_);
v_closed_3460_ = lean_ctor_get_uint8(v___x_3459_, sizeof(void*)*10);
if (v_closed_3460_ == 0)
{
lean_object* v_capacity_3461_; lean_object* v_size_3462_; lean_object* v_receivers_3463_; lean_object* v___x_3464_; 
v_capacity_3461_ = lean_ctor_get(v___x_3459_, 2);
lean_inc(v_capacity_3461_);
v_size_3462_ = lean_ctor_get(v___x_3459_, 3);
lean_inc(v_size_3462_);
v_receivers_3463_ = lean_ctor_get(v___x_3459_, 7);
lean_inc(v_receivers_3463_);
lean_dec(v___x_3459_);
v___x_3464_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3463_, v_id_3455_);
lean_dec(v_receivers_3463_);
if (lean_obj_tag(v___x_3464_) == 1)
{
lean_object* v_val_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v_val_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_val_3465_);
lean_dec_ref(v___x_3464_);
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_nat_dec_eq(v_size_3462_, v___x_3466_);
lean_dec(v_size_3462_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_nat_mod(v_val_3465_, v_capacity_3461_);
lean_dec(v_capacity_3461_);
v___x_3469_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3468_, v___y_3457_);
lean_dec(v___x_3468_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; lean_object* v_pos_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref(v___x_3469_);
v___x_3471_ = lean_st_ref_get(v_a_3470_);
lean_dec(v_a_3470_);
v_pos_3472_ = lean_ctor_get(v___x_3471_, 1);
lean_inc(v_pos_3472_);
lean_dec(v___x_3471_);
v___x_3473_ = lean_nat_dec_eq(v_pos_3472_, v_val_3465_);
lean_dec(v_val_3465_);
lean_dec(v_pos_3472_);
v___x_3474_ = lean_box(v___x_3473_);
v___x_3475_ = lean_apply_3(v___f_3456_, v___x_3474_, v___y_3457_, lean_box(0));
return v___x_3475_;
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec(v_val_3465_);
lean_dec(v___y_3457_);
lean_dec_ref(v___f_3456_);
v_a_3476_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3469_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3469_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
lean_dec(v_val_3465_);
lean_dec(v_capacity_3461_);
v___x_3484_ = lean_box(v_closed_3460_);
v___x_3485_ = lean_apply_3(v___f_3456_, v___x_3484_, v___y_3457_, lean_box(0));
return v___x_3485_;
}
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec(v___x_3464_);
lean_dec(v_size_3462_);
lean_dec(v_capacity_3461_);
v___x_3486_ = lean_box(v_closed_3460_);
v___x_3487_ = lean_apply_3(v___f_3456_, v___x_3486_, v___y_3457_, lean_box(0));
return v___x_3487_;
}
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec(v___x_3459_);
v___x_3488_ = lean_box(v_closed_3460_);
v___x_3489_ = lean_apply_3(v___f_3456_, v___x_3488_, v___y_3457_, lean_box(0));
return v___x_3489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3490_, lean_object* v___f_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3490_, v___f_3491_, v___y_3492_);
lean_dec(v_id_3490_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; lean_object* v_producers_3499_; lean_object* v_waiters_3500_; lean_object* v_capacity_3501_; lean_object* v_size_3502_; lean_object* v_buffer_3503_; lean_object* v_write_3504_; lean_object* v_read_3505_; lean_object* v_receivers_3506_; lean_object* v_nextId_3507_; uint8_t v_closed_3508_; lean_object* v_pos_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3531_; 
v___x_3498_ = lean_st_ref_get(v___y_3496_);
v_producers_3499_ = lean_ctor_get(v___x_3498_, 0);
v_waiters_3500_ = lean_ctor_get(v___x_3498_, 1);
v_capacity_3501_ = lean_ctor_get(v___x_3498_, 2);
v_size_3502_ = lean_ctor_get(v___x_3498_, 3);
v_buffer_3503_ = lean_ctor_get(v___x_3498_, 4);
v_write_3504_ = lean_ctor_get(v___x_3498_, 5);
v_read_3505_ = lean_ctor_get(v___x_3498_, 6);
v_receivers_3506_ = lean_ctor_get(v___x_3498_, 7);
v_nextId_3507_ = lean_ctor_get(v___x_3498_, 8);
v_closed_3508_ = lean_ctor_get_uint8(v___x_3498_, sizeof(void*)*10);
v_pos_3509_ = lean_ctor_get(v___x_3498_, 9);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3511_ = v___x_3498_;
v_isShared_3512_ = v_isSharedCheck_3531_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_pos_3509_);
lean_inc(v_nextId_3507_);
lean_inc(v_receivers_3506_);
lean_inc(v_read_3505_);
lean_inc(v_write_3504_);
lean_inc(v_buffer_3503_);
lean_inc(v_size_3502_);
lean_inc(v_capacity_3501_);
lean_inc(v_waiters_3500_);
lean_inc(v_producers_3499_);
lean_dec(v___x_3498_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3531_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3500_);
if (lean_obj_tag(v___x_3513_) == 1)
{
lean_object* v_val_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3528_; 
v_val_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3528_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_val_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3528_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v_fst_3518_; lean_object* v_snd_3519_; lean_object* v___x_3520_; lean_object* v___x_3522_; 
v_fst_3518_ = lean_ctor_get(v_val_3514_, 0);
lean_inc(v_fst_3518_);
v_snd_3519_ = lean_ctor_get(v_val_3514_, 1);
lean_inc(v_snd_3519_);
lean_dec(v_val_3514_);
v___x_3520_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3518_, v_____do__lift_3495_);
lean_dec(v_fst_3518_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v_snd_3519_);
v___x_3522_ = v___x_3511_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_producers_3499_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_snd_3519_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_capacity_3501_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_size_3502_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_buffer_3503_);
lean_ctor_set(v_reuseFailAlloc_3527_, 5, v_write_3504_);
lean_ctor_set(v_reuseFailAlloc_3527_, 6, v_read_3505_);
lean_ctor_set(v_reuseFailAlloc_3527_, 7, v_receivers_3506_);
lean_ctor_set(v_reuseFailAlloc_3527_, 8, v_nextId_3507_);
lean_ctor_set(v_reuseFailAlloc_3527_, 9, v_pos_3509_);
lean_ctor_set_uint8(v_reuseFailAlloc_3527_, sizeof(void*)*10, v_closed_3508_);
v___x_3522_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = lean_st_ref_set(v___y_3496_, v___x_3522_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set_tag(v___x_3516_, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3523_);
v___x_3525_ = v___x_3516_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec(v___x_3513_);
lean_del_object(v___x_3511_);
lean_dec(v_pos_3509_);
lean_dec(v_nextId_3507_);
lean_dec(v_receivers_3506_);
lean_dec(v_read_3505_);
lean_dec(v_write_3504_);
lean_dec_ref(v_buffer_3503_);
lean_dec(v_size_3502_);
lean_dec(v_capacity_3501_);
lean_dec_ref(v_producers_3499_);
v___x_3529_ = lean_box(0);
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
return v___x_3530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
uint8_t v_____do__lift_5973__boxed_3535_; lean_object* v_res_3536_; 
v_____do__lift_5973__boxed_3535_ = lean_unbox(v_____do__lift_3532_);
v_res_3536_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_5973__boxed_3535_, v___y_3533_);
lean_dec(v___y_3533_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3537_, lean_object* v___f_3538_, lean_object* v_id_3539_, uint8_t v_____do__lift_3540_, lean_object* v___y_3541_){
_start:
{
if (v_____do__lift_3540_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v_producers_3545_; lean_object* v_waiters_3546_; lean_object* v_capacity_3547_; lean_object* v_size_3548_; lean_object* v_buffer_3549_; lean_object* v_write_3550_; lean_object* v_read_3551_; lean_object* v_receivers_3552_; lean_object* v_nextId_3553_; uint8_t v_closed_3554_; lean_object* v_pos_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_id_3539_);
v___x_3543_ = lean_io_promise_new();
v___x_3544_ = lean_st_ref_take(v___y_3541_);
v_producers_3545_ = lean_ctor_get(v___x_3544_, 0);
v_waiters_3546_ = lean_ctor_get(v___x_3544_, 1);
v_capacity_3547_ = lean_ctor_get(v___x_3544_, 2);
v_size_3548_ = lean_ctor_get(v___x_3544_, 3);
v_buffer_3549_ = lean_ctor_get(v___x_3544_, 4);
v_write_3550_ = lean_ctor_get(v___x_3544_, 5);
v_read_3551_ = lean_ctor_get(v___x_3544_, 6);
v_receivers_3552_ = lean_ctor_get(v___x_3544_, 7);
v_nextId_3553_ = lean_ctor_get(v___x_3544_, 8);
v_closed_3554_ = lean_ctor_get_uint8(v___x_3544_, sizeof(void*)*10);
v_pos_3555_ = lean_ctor_get(v___x_3544_, 9);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3557_ = v___x_3544_;
v_isShared_3558_ = v_isSharedCheck_3569_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_pos_3555_);
lean_inc(v_nextId_3553_);
lean_inc(v_receivers_3552_);
lean_inc(v_read_3551_);
lean_inc(v_write_3550_);
lean_inc(v_buffer_3549_);
lean_inc(v_size_3548_);
lean_inc(v_capacity_3547_);
lean_inc(v_waiters_3546_);
lean_inc(v_producers_3545_);
lean_dec(v___x_3544_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3569_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_waiter_3537_);
lean_inc(v___x_3543_);
v___x_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3543_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Std_Queue_enqueue___redArg(v___x_3560_, v_waiters_3546_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v___x_3561_);
v___x_3563_ = v___x_3557_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_producers_3545_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_capacity_3547_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_size_3548_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v_buffer_3549_);
lean_ctor_set(v_reuseFailAlloc_3568_, 5, v_write_3550_);
lean_ctor_set(v_reuseFailAlloc_3568_, 6, v_read_3551_);
lean_ctor_set(v_reuseFailAlloc_3568_, 7, v_receivers_3552_);
lean_ctor_set(v_reuseFailAlloc_3568_, 8, v_nextId_3553_);
lean_ctor_set(v_reuseFailAlloc_3568_, 9, v_pos_3555_);
lean_ctor_set_uint8(v_reuseFailAlloc_3568_, sizeof(void*)*10, v_closed_3554_);
v___x_3563_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3564_ = lean_st_ref_set(v___y_3541_, v___x_3563_);
lean_dec(v___y_3541_);
v___x_3565_ = lean_io_promise_result_opt(v___x_3543_);
lean_dec(v___x_3543_);
v___x_3566_ = lean_unsigned_to_nat(0u);
v___x_3567_ = l_EIO_chainTask___redArg(v___x_3565_, v___f_3538_, v___x_3566_, v_____do__lift_3540_);
return v___x_3567_;
}
}
}
else
{
lean_object* v___x_3570_; lean_object* v_lose_3571_; lean_object* v___x_3572_; 
lean_dec_ref(v___f_3538_);
v___x_3570_ = lean_box(v_____do__lift_3540_);
v_lose_3571_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3571_, 0, v___x_3570_);
v___x_3572_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3539_, v_waiter_3537_, v_lose_3571_, v___y_3541_);
lean_dec_ref(v_waiter_3537_);
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3573_, lean_object* v___f_3574_, lean_object* v_id_3575_, lean_object* v_____do__lift_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
uint8_t v_____do__lift_6029__boxed_3579_; lean_object* v_res_3580_; 
v_____do__lift_6029__boxed_3579_ = lean_unbox(v_____do__lift_3576_);
v_res_3580_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3573_, v___f_3574_, v_id_3575_, v_____do__lift_6029__boxed_3579_, v___y_3577_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3583_, lean_object* v_ch_3584_, lean_object* v_res_x3f_3585_){
_start:
{
if (lean_obj_tag(v_res_x3f_3585_) == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec_ref(v_ch_3584_);
lean_dec_ref(v_waiter_3583_);
v___x_3587_ = lean_box(0);
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
return v___x_3588_;
}
else
{
lean_object* v_val_3589_; uint8_t v___x_3590_; 
v_val_3589_ = lean_ctor_get(v_res_x3f_3585_, 0);
v___x_3590_ = lean_unbox(v_val_3589_);
if (v___x_3590_ == 0)
{
lean_object* v___f_3591_; lean_object* v___x_3592_; 
lean_dec_ref(v_ch_3584_);
v___f_3591_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3592_ = l_Std_Internal_IO_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3583_, v___f_3591_);
lean_dec_ref(v_waiter_3583_);
return v___x_3592_;
}
else
{
lean_object* v___x_3593_; 
v___x_3593_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3584_, v_waiter_3583_);
return v___x_3593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3594_, lean_object* v_ch_3595_, lean_object* v_res_x3f_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3594_, v_ch_3595_, v_res_x3f_3596_);
lean_dec(v_res_x3f_3596_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3599_, lean_object* v_waiter_3600_){
_start:
{
lean_object* v_state_3602_; lean_object* v_id_3603_; lean_object* v___f_3604_; lean_object* v___f_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; 
v_state_3602_ = lean_ctor_get(v_ch_3599_, 0);
lean_inc_ref(v_state_3602_);
v_id_3603_ = lean_ctor_get(v_ch_3599_, 1);
lean_inc(v_id_3603_);
lean_inc_ref(v_waiter_3600_);
v___f_3604_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3604_, 0, v_waiter_3600_);
lean_closure_set(v___f_3604_, 1, v_ch_3599_);
lean_inc(v_id_3603_);
v___f_3605_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3605_, 0, v_waiter_3600_);
lean_closure_set(v___f_3605_, 1, v___f_3604_);
lean_closure_set(v___f_3605_, 2, v_id_3603_);
v___f_3606_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3606_, 0, v_id_3603_);
lean_closure_set(v___f_3606_, 1, v___f_3605_);
v___x_3607_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3602_, v___f_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3608_, lean_object* v_waiter_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3608_, v_waiter_3609_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3612_, lean_object* v_ch_3613_, lean_object* v_waiter_3614_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3613_, v_waiter_3614_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3617_, lean_object* v_ch_3618_, lean_object* v_waiter_3619_, lean_object* v_a_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3617_, v_ch_3618_, v_waiter_3619_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3622_, lean_object* v_receiverId_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3623_, v_a_3624_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3627_, lean_object* v_receiverId_3628_, lean_object* v_a_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3627_, v_receiverId_3628_, v_a_3629_);
lean_dec(v_a_3629_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3632_, lean_object* v_x_3633_){
_start:
{
if (lean_obj_tag(v_x_3633_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3643_; 
v_a_3635_ = lean_ctor_get(v_x_3633_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v_x_3633_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3637_ = v_x_3633_;
v_isShared_3638_ = v_isSharedCheck_3643_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v_x_3633_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3643_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; 
v___x_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
return v___x_3641_;
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3656_; 
v_a_3644_ = lean_ctor_get(v_x_3633_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_x_3633_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3646_ = v_x_3633_;
v_isShared_3647_ = v_isSharedCheck_3656_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v_x_3633_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3656_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v_capacity_3648_; lean_object* v_buffer_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3653_; 
v_capacity_3648_ = lean_ctor_get(v_a_3644_, 2);
lean_inc(v_capacity_3648_);
v_buffer_3649_ = lean_ctor_get(v_a_3644_, 4);
lean_inc_ref(v_buffer_3649_);
lean_dec(v_a_3644_);
v___x_3650_ = lean_nat_mod(v_place_3632_, v_capacity_3648_);
lean_dec(v_capacity_3648_);
v___x_3651_ = lean_array_fget(v_buffer_3649_, v___x_3650_);
lean_dec(v___x_3650_);
lean_dec_ref(v_buffer_3649_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3651_);
v___x_3653_ = v___x_3646_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3651_);
v___x_3653_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3654_; 
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3657_, lean_object* v_x_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3657_, v_x_3658_);
lean_dec(v_place_3657_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v___x_3664_; lean_object* v___f_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; lean_object* v___x_3670_; 
v___x_3664_ = lean_st_ref_get(v_a_3662_);
v___f_3665_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3665_, 0, v_place_3661_);
v___x_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
v___x_3668_ = lean_unsigned_to_nat(0u);
v___x_3669_ = 0;
v___x_3670_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3668_, v___x_3669_, v___x_3667_, v___f_3665_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3671_, lean_object* v_a_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3671_, v_a_3672_);
lean_dec(v_a_3672_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3675_, lean_object* v_place_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3676_, v_a_3677_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3680_, lean_object* v_place_3681_, lean_object* v_a_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3680_, v_place_3681_, v_a_3682_);
lean_dec(v_a_3682_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_3685_, lean_object* v_x_3686_){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3688_ = lean_io_basemutex_unlock(v_mutex_3685_);
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_3691_, lean_object* v_x_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(v_mutex_3691_, v_x_3692_);
lean_dec(v_x_3692_);
lean_dec(v_mutex_3691_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_3695_, lean_object* v_ref_3696_, lean_object* v_x_3697_){
_start:
{
if (lean_obj_tag(v_x_3697_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v_ref_3696_);
lean_dec_ref(v_k_3695_);
v_a_3699_ = lean_ctor_get(v_x_3697_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_x_3697_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3701_ = v_x_3697_;
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v_x_3697_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3707_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
}
}
else
{
lean_object* v___x_3708_; 
lean_dec_ref(v_x_3697_);
v___x_3708_ = lean_apply_2(v_k_3695_, v_ref_3696_, lean_box(0));
return v___x_3708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_3709_, lean_object* v_ref_3710_, lean_object* v_x_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_k_3709_, v_ref_3710_, v_x_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_3714_, lean_object* v___f_3715_){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; 
v___x_3717_ = lean_io_basemutex_lock(v_mutex_3714_);
v___x_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
v___x_3720_ = lean_unsigned_to_nat(0u);
v___x_3721_ = 0;
v___x_3722_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3720_, v___x_3721_, v___x_3719_, v___f_3715_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_3723_, lean_object* v___f_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_mutex_3723_, v___f_3724_);
lean_dec(v_mutex_3723_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_3727_){
_start:
{
if (lean_obj_tag(v___y_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
v_a_3728_ = lean_ctor_get(v___y_3727_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___y_3727_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___y_3727_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___y_3727_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
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
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3744_; 
v_a_3736_ = lean_ctor_get(v___y_3727_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___y_3727_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3738_ = v___y_3727_;
v_isShared_3739_ = v_isSharedCheck_3744_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___y_3727_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3744_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v_fst_3740_; lean_object* v___x_3742_; 
v_fst_3740_ = lean_ctor_get(v_a_3736_, 0);
lean_inc(v_fst_3740_);
lean_dec(v_a_3736_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set(v___x_3738_, 0, v_fst_3740_);
v___x_3742_ = v___x_3738_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_fst_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_3746_, lean_object* v_k_3747_){
_start:
{
lean_object* v_ref_3749_; lean_object* v_mutex_3750_; lean_object* v___f_3751_; lean_object* v___f_3752_; lean_object* v___f_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___y_3758_; 
v_ref_3749_ = lean_ctor_get(v_mutex_3746_, 0);
lean_inc(v_ref_3749_);
v_mutex_3750_ = lean_ctor_get(v_mutex_3746_, 1);
lean_inc(v_mutex_3750_);
lean_dec_ref(v_mutex_3746_);
lean_inc(v_mutex_3750_);
v___f_3751_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3751_, 0, v_mutex_3750_);
v___f_3752_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3752_, 0, v_k_3747_);
lean_closure_set(v___f_3752_, 1, v_ref_3749_);
v___f_3753_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3753_, 0, v_mutex_3750_);
lean_closure_set(v___f_3753_, 1, v___f_3752_);
v___x_3754_ = lean_unsigned_to_nat(0u);
v___x_3755_ = 0;
v___x_3756_ = l_Std_Internal_IO_Async_EAsync_tryFinally_x27___redArg(v___f_3753_, v___f_3751_, v___x_3754_, v___x_3755_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3760_; 
v_a_3760_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3760_);
lean_dec_ref(v___x_3756_);
if (lean_obj_tag(v_a_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v_a_3761_ = lean_ctor_get(v_a_3760_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_a_3760_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v_a_3760_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v_a_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
v___y_3758_ = v___x_3766_;
goto v___jp_3757_;
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3777_; 
v_a_3769_ = lean_ctor_get(v_a_3760_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_a_3760_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3771_ = v_a_3760_;
v_isShared_3772_ = v_isSharedCheck_3777_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v_a_3760_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3777_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v_fst_3773_; lean_object* v___x_3775_; 
v_fst_3773_ = lean_ctor_get(v_a_3769_, 0);
lean_inc(v_fst_3773_);
lean_dec(v_a_3769_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v_fst_3773_);
v___x_3775_ = v___x_3771_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_fst_3773_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
v___y_3758_ = v___x_3775_;
goto v___jp_3757_;
}
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3787_; 
v_a_3778_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3780_ = v___x_3756_;
v_isShared_3781_ = v_isSharedCheck_3787_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3756_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3787_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___f_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___f_3782_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___x_3783_ = lean_task_map(v___f_3782_, v_a_3778_, v___x_3754_, v___x_3755_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3783_);
v___x_3785_ = v___x_3780_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
v___jp_3757_:
{
lean_object* v___x_3759_; 
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v___y_3758_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_3788_, lean_object* v_k_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3788_, v_k_3789_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_3792_, lean_object* v_00_u03b2_3793_, lean_object* v_mutex_3794_, lean_object* v_k_3795_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3794_, v_k_3795_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_3798_, lean_object* v_00_u03b2_3799_, lean_object* v_mutex_3800_, lean_object* v_k_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_3798_, v_00_u03b2_3799_, v_mutex_3800_, v_k_3801_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_3804_, lean_object* v_capacity_3805_, lean_object* v_size_3806_, lean_object* v_buffer_3807_, lean_object* v_write_3808_, lean_object* v_read_3809_, lean_object* v_receivers_3810_, lean_object* v_nextId_3811_, uint8_t v_closed_3812_, lean_object* v_pos_3813_, lean_object* v___y_3814_, lean_object* v_x_3815_){
_start:
{
if (lean_obj_tag(v_x_3815_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v_pos_3813_);
lean_dec(v_nextId_3811_);
lean_dec(v_receivers_3810_);
lean_dec(v_read_3809_);
lean_dec(v_write_3808_);
lean_dec_ref(v_buffer_3807_);
lean_dec(v_size_3806_);
lean_dec(v_capacity_3805_);
lean_dec_ref(v_producers_3804_);
v_a_3817_ = lean_ctor_get(v_x_3815_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_x_3815_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3819_ = v_x_3815_;
v_isShared_3820_ = v_isSharedCheck_3825_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v_x_3815_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3825_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
return v___x_3823_;
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3836_; 
v_a_3826_ = lean_ctor_get(v_x_3815_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_x_3815_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3828_ = v_x_3815_;
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v_x_3815_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3836_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3830_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3830_, 0, v_producers_3804_);
lean_ctor_set(v___x_3830_, 1, v_a_3826_);
lean_ctor_set(v___x_3830_, 2, v_capacity_3805_);
lean_ctor_set(v___x_3830_, 3, v_size_3806_);
lean_ctor_set(v___x_3830_, 4, v_buffer_3807_);
lean_ctor_set(v___x_3830_, 5, v_write_3808_);
lean_ctor_set(v___x_3830_, 6, v_read_3809_);
lean_ctor_set(v___x_3830_, 7, v_receivers_3810_);
lean_ctor_set(v___x_3830_, 8, v_nextId_3811_);
lean_ctor_set(v___x_3830_, 9, v_pos_3813_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*10, v_closed_3812_);
v___x_3831_ = lean_st_ref_set(v___y_3814_, v___x_3830_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3831_);
v___x_3833_ = v___x_3828_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3831_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_3837_, lean_object* v_capacity_3838_, lean_object* v_size_3839_, lean_object* v_buffer_3840_, lean_object* v_write_3841_, lean_object* v_read_3842_, lean_object* v_receivers_3843_, lean_object* v_nextId_3844_, lean_object* v_closed_3845_, lean_object* v_pos_3846_, lean_object* v___y_3847_, lean_object* v_x_3848_, lean_object* v___y_3849_){
_start:
{
uint8_t v_closed_boxed_3850_; lean_object* v_res_3851_; 
v_closed_boxed_3850_ = lean_unbox(v_closed_3845_);
v_res_3851_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_3837_, v_capacity_3838_, v_size_3839_, v_buffer_3840_, v_write_3841_, v_read_3842_, v_receivers_3843_, v_nextId_3844_, v_closed_boxed_3850_, v_pos_3846_, v___y_3847_, v_x_3848_);
lean_dec(v___y_3847_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_3852_){
_start:
{
if (lean_obj_tag(v_x_3852_) == 0)
{
lean_object* v___x_3854_; 
v___x_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3854_, 0, v_x_3852_);
return v___x_3854_;
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3864_; 
v_a_3855_ = lean_ctor_get(v_x_3852_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_x_3852_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3857_ = v_x_3852_;
v_isShared_3858_ = v_isSharedCheck_3864_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v_x_3852_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3864_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = l_List_reverse___redArg(v_a_3855_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3859_);
v___x_3861_ = v___x_3857_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
lean_object* v___x_3862_; 
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_3865_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_3868_, lean_object* v___x_3869_, lean_object* v_x_3870_){
_start:
{
if (lean_obj_tag(v_x_3870_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3880_; 
lean_dec(v___x_3869_);
lean_dec(v_a_3868_);
v_a_3872_ = lean_ctor_get(v_x_3870_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_x_3870_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3874_ = v_x_3870_;
v_isShared_3875_ = v_isSharedCheck_3880_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v_x_3870_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3880_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3878_; 
v___x_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
return v___x_3878_;
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3897_; 
v_a_3881_ = lean_ctor_get(v_x_3870_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_x_3870_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3883_ = v_x_3870_;
v_isShared_3884_ = v_isSharedCheck_3897_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v_x_3870_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3897_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
uint8_t v___x_3885_; 
v___x_3885_ = l_List_isEmpty___redArg(v_a_3868_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
lean_dec(v___x_3869_);
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v_a_3881_);
lean_ctor_set(v___x_3886_, 1, v_a_3868_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v___x_3886_);
v___x_3888_ = v___x_3883_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
return v___x_3889_;
}
}
else
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3894_; 
lean_dec(v_a_3868_);
v___x_3891_ = l_List_reverse___redArg(v_a_3881_);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3869_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v___x_3892_);
v___x_3894_ = v___x_3883_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3892_);
v___x_3894_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
lean_object* v___x_3895_; 
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
return v___x_3895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_3898_, lean_object* v___x_3899_, lean_object* v_x_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_3898_, v___x_3899_, v_x_3900_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_3903_){
_start:
{
uint8_t v___y_3906_; 
if (lean_obj_tag(v_x_3903_) == 0)
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v_x_3903_);
return v___x_3910_;
}
else
{
lean_object* v_a_3911_; uint8_t v___x_3912_; 
v_a_3911_ = lean_ctor_get(v_x_3903_, 0);
lean_inc(v_a_3911_);
lean_dec_ref(v_x_3903_);
v___x_3912_ = lean_unbox(v_a_3911_);
lean_dec(v_a_3911_);
if (v___x_3912_ == 0)
{
uint8_t v___x_3913_; 
v___x_3913_ = 1;
v___y_3906_ = v___x_3913_;
goto v___jp_3905_;
}
else
{
uint8_t v___x_3914_; 
v___x_3914_ = 0;
v___y_3906_ = v___x_3914_;
goto v___jp_3905_;
}
}
v___jp_3905_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3907_ = lean_box(v___y_3906_);
v___x_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_3918_, lean_object* v_x_3919_, lean_object* v_head_3920_, lean_object* v_x_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_3918_, v_x_3919_, v_head_3920_, v_x_3921_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_3930_, lean_object* v_x_3931_){
_start:
{
if (lean_obj_tag(v_x_3930_) == 0)
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3933_, 0, v_x_3931_);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
return v___x_3934_;
}
else
{
lean_object* v_head_3935_; lean_object* v_tail_3936_; lean_object* v_waiter_3937_; lean_object* v___f_3938_; lean_object* v_val_3940_; 
v_head_3935_ = lean_ctor_get(v_x_3930_, 0);
lean_inc(v_head_3935_);
v_tail_3936_ = lean_ctor_get(v_x_3930_, 1);
lean_inc(v_tail_3936_);
lean_dec_ref(v_x_3930_);
v_waiter_3937_ = lean_ctor_get(v_head_3935_, 1);
lean_inc(v_waiter_3937_);
v___f_3938_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3938_, 0, v_tail_3936_);
lean_closure_set(v___f_3938_, 1, v_x_3931_);
lean_closure_set(v___f_3938_, 2, v_head_3935_);
if (lean_obj_tag(v_waiter_3937_) == 0)
{
lean_object* v___x_3944_; 
v___x_3944_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v_val_3940_ = v___x_3944_;
goto v___jp_3939_;
}
else
{
lean_object* v_val_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3959_; 
v_val_3945_ = lean_ctor_get(v_waiter_3937_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_waiter_3937_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3947_ = v_waiter_3937_;
v_isShared_3948_ = v_isSharedCheck_3959_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_val_3945_);
lean_dec(v_waiter_3937_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3959_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v_finished_3949_; lean_object* v___x_3950_; lean_object* v___f_3951_; lean_object* v___x_3953_; 
v_finished_3949_ = lean_ctor_get(v_val_3945_, 0);
lean_inc(v_finished_3949_);
lean_dec(v_val_3945_);
v___x_3950_ = lean_st_ref_get(v_finished_3949_);
lean_dec(v_finished_3949_);
v___f_3951_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3950_);
v___x_3953_ = v___x_3947_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3950_);
v___x_3953_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; uint8_t v___x_3956_; lean_object* v___x_3957_; 
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
v___x_3955_ = lean_unsigned_to_nat(0u);
v___x_3956_ = 0;
v___x_3957_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3955_, v___x_3956_, v___x_3954_, v___f_3951_);
v_val_3940_ = v___x_3957_;
goto v___jp_3939_;
}
}
}
v___jp_3939_:
{
lean_object* v___x_3941_; uint8_t v___x_3942_; lean_object* v___x_3943_; 
v___x_3941_ = lean_unsigned_to_nat(0u);
v___x_3942_ = 0;
v___x_3943_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3941_, v___x_3942_, v_val_3940_, v___f_3938_);
return v___x_3943_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_3960_, lean_object* v_x_3961_, lean_object* v_head_3962_, lean_object* v_x_3963_){
_start:
{
if (lean_obj_tag(v_x_3963_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3973_; 
lean_dec_ref(v_head_3962_);
lean_dec(v_x_3961_);
lean_dec(v_tail_3960_);
v_a_3965_ = lean_ctor_get(v_x_3963_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_x_3963_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3967_ = v_x_3963_;
v_isShared_3968_ = v_isSharedCheck_3973_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v_x_3963_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3973_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
lean_object* v___x_3971_; 
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
}
}
else
{
lean_object* v_a_3974_; uint8_t v___x_3975_; 
v_a_3974_ = lean_ctor_get(v_x_3963_, 0);
lean_inc(v_a_3974_);
lean_dec_ref(v_x_3963_);
v___x_3975_ = lean_unbox(v_a_3974_);
lean_dec(v_a_3974_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; 
lean_dec_ref(v_head_3962_);
v___x_3976_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_3960_, v_x_3961_);
return v___x_3976_;
}
else
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3977_, 0, v_head_3962_);
lean_ctor_set(v___x_3977_, 1, v_x_3961_);
v___x_3978_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_3960_, v___x_3977_);
return v___x_3978_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_3979_, lean_object* v_x_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_3979_, v_x_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_3983_, lean_object* v___x_3984_, lean_object* v___f_3985_, lean_object* v_x_3986_){
_start:
{
if (lean_obj_tag(v_x_3986_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3996_; 
lean_dec_ref(v___f_3985_);
lean_dec(v___x_3984_);
lean_dec(v_eList_3983_);
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
lean_object* v_a_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; lean_object* v___x_4001_; lean_object* v___f_4002_; lean_object* v___x_4003_; 
v_a_3997_ = lean_ctor_get(v_x_3986_, 0);
lean_inc(v_a_3997_);
lean_dec_ref(v_x_3986_);
lean_inc(v___x_3984_);
v___x_3998_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_3983_, v___x_3984_);
v___x_3999_ = lean_unsigned_to_nat(0u);
v___x_4000_ = 0;
v___x_4001_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3999_, v___x_4000_, v___x_3998_, v___f_3985_);
v___f_4002_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4002_, 0, v_a_3997_);
lean_closure_set(v___f_4002_, 1, v___x_3984_);
v___x_4003_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3999_, v___x_4000_, v___x_4001_, v___f_4002_);
return v___x_4003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_4004_, lean_object* v___x_4005_, lean_object* v___f_4006_, lean_object* v_x_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v_eList_4004_, v___x_4005_, v___f_4006_, v_x_4007_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_eList_4014_; lean_object* v_dList_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___f_4018_; lean_object* v___x_4019_; uint8_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___f_4022_; lean_object* v___x_4023_; 
v_eList_4014_ = lean_ctor_get(v_q_4011_, 0);
lean_inc(v_eList_4014_);
v_dList_4015_ = lean_ctor_get(v_q_4011_, 1);
lean_inc(v_dList_4015_);
lean_dec_ref(v_q_4011_);
v___x_4016_ = lean_box(0);
v___x_4017_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4015_, v___x_4016_);
v___f_4018_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4019_ = lean_unsigned_to_nat(0u);
v___x_4020_ = 0;
v___x_4021_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4019_, v___x_4020_, v___x_4017_, v___f_4018_);
v___f_4022_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4022_, 0, v_eList_4014_);
lean_closure_set(v___f_4022_, 1, v___x_4016_);
lean_closure_set(v___f_4022_, 2, v___f_4018_);
v___x_4023_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4019_, v___x_4020_, v___x_4021_, v___f_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4024_, v___y_4025_);
lean_dec(v___y_4025_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4028_, lean_object* v_x_4029_){
_start:
{
if (lean_obj_tag(v_x_4029_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4039_; 
lean_dec(v___y_4028_);
v_a_4031_ = lean_ctor_get(v_x_4029_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_x_4029_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4033_ = v_x_4029_;
v_isShared_4034_ = v_isSharedCheck_4039_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v_x_4029_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4039_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4031_);
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
else
{
lean_object* v_a_4040_; lean_object* v_producers_4041_; lean_object* v_waiters_4042_; lean_object* v_capacity_4043_; lean_object* v_size_4044_; lean_object* v_buffer_4045_; lean_object* v_write_4046_; lean_object* v_read_4047_; lean_object* v_receivers_4048_; lean_object* v_nextId_4049_; uint8_t v_closed_4050_; lean_object* v_pos_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___f_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; lean_object* v___x_4057_; 
v_a_4040_ = lean_ctor_get(v_x_4029_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v_x_4029_);
v_producers_4041_ = lean_ctor_get(v_a_4040_, 0);
lean_inc_ref(v_producers_4041_);
v_waiters_4042_ = lean_ctor_get(v_a_4040_, 1);
lean_inc_ref(v_waiters_4042_);
v_capacity_4043_ = lean_ctor_get(v_a_4040_, 2);
lean_inc(v_capacity_4043_);
v_size_4044_ = lean_ctor_get(v_a_4040_, 3);
lean_inc(v_size_4044_);
v_buffer_4045_ = lean_ctor_get(v_a_4040_, 4);
lean_inc_ref(v_buffer_4045_);
v_write_4046_ = lean_ctor_get(v_a_4040_, 5);
lean_inc(v_write_4046_);
v_read_4047_ = lean_ctor_get(v_a_4040_, 6);
lean_inc(v_read_4047_);
v_receivers_4048_ = lean_ctor_get(v_a_4040_, 7);
lean_inc(v_receivers_4048_);
v_nextId_4049_ = lean_ctor_get(v_a_4040_, 8);
lean_inc(v_nextId_4049_);
v_closed_4050_ = lean_ctor_get_uint8(v_a_4040_, sizeof(void*)*10);
v_pos_4051_ = lean_ctor_get(v_a_4040_, 9);
lean_inc(v_pos_4051_);
lean_dec(v_a_4040_);
v___x_4052_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4042_, v___y_4028_);
v___x_4053_ = lean_box(v_closed_4050_);
v___f_4054_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4054_, 0, v_producers_4041_);
lean_closure_set(v___f_4054_, 1, v_capacity_4043_);
lean_closure_set(v___f_4054_, 2, v_size_4044_);
lean_closure_set(v___f_4054_, 3, v_buffer_4045_);
lean_closure_set(v___f_4054_, 4, v_write_4046_);
lean_closure_set(v___f_4054_, 5, v_read_4047_);
lean_closure_set(v___f_4054_, 6, v_receivers_4048_);
lean_closure_set(v___f_4054_, 7, v_nextId_4049_);
lean_closure_set(v___f_4054_, 8, v___x_4053_);
lean_closure_set(v___f_4054_, 9, v_pos_4051_);
lean_closure_set(v___f_4054_, 10, v___y_4028_);
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = 0;
v___x_4057_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4055_, v___x_4056_, v___x_4052_, v___f_4054_);
return v___x_4057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4058_, lean_object* v_x_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4058_, v_x_4059_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4062_){
_start:
{
lean_object* v___x_4064_; lean_object* v___f_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; lean_object* v___x_4070_; 
v___x_4064_ = lean_st_ref_get(v___y_4062_);
v___f_4065_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4065_, 0, v___y_4062_);
v___x_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4064_);
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
v___x_4068_ = lean_unsigned_to_nat(0u);
v___x_4069_ = 0;
v___x_4070_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4068_, v___x_4069_, v___x_4067_, v___f_4065_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4071_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4074_, lean_object* v_waiter_4075_){
_start:
{
lean_object* v_val_4078_; lean_object* v___x_4080_; 
v___x_4080_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4074_, v_waiter_4075_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4080_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4080_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
lean_ctor_set_tag(v___x_4083_, 1);
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
v_val_4078_ = v___x_4086_;
goto v___jp_4077_;
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
v_a_4089_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4080_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4080_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
lean_ctor_set_tag(v___x_4091_, 0);
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
v_val_4078_ = v___x_4094_;
goto v___jp_4077_;
}
}
}
v___jp_4077_:
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v_val_4078_);
return v___x_4079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4097_, lean_object* v_waiter_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4097_, v_waiter_4098_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4101_){
_start:
{
if (lean_obj_tag(v_x_4101_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4111_; 
v_a_4103_ = lean_ctor_get(v_x_4101_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v_x_4101_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4105_ = v_x_4101_;
v_isShared_4106_ = v_isSharedCheck_4111_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v_x_4101_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4111_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
return v___x_4109_;
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4121_; 
v_a_4112_ = lean_ctor_get(v_x_4101_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_x_4101_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4114_ = v_x_4101_;
v_isShared_4115_ = v_isSharedCheck_4121_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v_x_4101_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4121_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; lean_object* v___x_4118_; 
v___x_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4116_, 0, v_a_4112_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set(v___x_4114_, 0, v___x_4116_);
v___x_4118_ = v___x_4114_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4116_);
v___x_4118_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4119_; 
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
return v___x_4119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4122_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_val_4125_, lean_object* v_x_4126_){
_start:
{
if (lean_obj_tag(v_x_4126_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4136_; 
v_a_4128_ = lean_ctor_get(v_x_4126_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_x_4126_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4130_ = v_x_4126_;
v_isShared_4131_ = v_isSharedCheck_4136_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v_x_4126_);
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
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4148_; 
v_a_4137_ = lean_ctor_get(v_x_4126_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_x_4126_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4139_ = v_x_4126_;
v_isShared_4140_ = v_isSharedCheck_4148_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v_x_4126_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4148_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v_pos_4141_; uint8_t v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
v_pos_4141_ = lean_ctor_get(v_a_4137_, 1);
lean_inc(v_pos_4141_);
lean_dec(v_a_4137_);
v___x_4142_ = lean_nat_dec_eq(v_pos_4141_, v_val_4125_);
lean_dec(v_pos_4141_);
v___x_4143_ = lean_box(v___x_4142_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v___x_4143_);
v___x_4145_ = v___x_4139_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_val_4149_, lean_object* v_x_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_val_4149_, v_x_4150_);
lean_dec(v_val_4149_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v___x_4153_, uint8_t v_closed_4154_, lean_object* v___f_4155_, lean_object* v_x_4156_){
_start:
{
if (lean_obj_tag(v_x_4156_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4166_; 
lean_dec_ref(v___f_4155_);
lean_dec(v___x_4153_);
v_a_4158_ = lean_ctor_get(v_x_4156_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_x_4156_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4160_ = v_x_4156_;
v_isShared_4161_ = v_isSharedCheck_4166_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v_x_4156_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4166_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4177_; 
v_a_4167_ = lean_ctor_get(v_x_4156_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v_x_4156_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4169_ = v_x_4156_;
v_isShared_4170_ = v_isSharedCheck_4177_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v_x_4156_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4177_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4171_ = lean_st_ref_get(v_a_4167_);
lean_dec(v_a_4167_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4171_);
v___x_4173_ = v___x_4169_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
v___x_4175_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4153_, v_closed_4154_, v___x_4174_, v___f_4155_);
return v___x_4175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v___x_4178_, lean_object* v_closed_4179_, lean_object* v___f_4180_, lean_object* v_x_4181_, lean_object* v___y_4182_){
_start:
{
uint8_t v_closed_boxed_4183_; lean_object* v_res_4184_; 
v_closed_boxed_4183_ = lean_unbox(v_closed_4179_);
v_res_4184_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v___x_4178_, v_closed_boxed_4183_, v___f_4180_, v_x_4181_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v_id_4185_, lean_object* v___y_4186_, lean_object* v_x_4187_){
_start:
{
if (lean_obj_tag(v_x_4187_) == 0)
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4197_; 
v_a_4189_ = lean_ctor_get(v_x_4187_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v_x_4187_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4191_ = v_x_4187_;
v_isShared_4192_ = v_isSharedCheck_4197_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v_x_4187_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4197_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
lean_object* v___x_4195_; 
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4237_; 
v_a_4198_ = lean_ctor_get(v_x_4187_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_x_4187_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4200_ = v_x_4187_;
v_isShared_4201_ = v_isSharedCheck_4237_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v_x_4187_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4237_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
uint8_t v_closed_4202_; 
v_closed_4202_ = lean_ctor_get_uint8(v_a_4198_, sizeof(void*)*10);
if (v_closed_4202_ == 0)
{
lean_object* v_capacity_4203_; lean_object* v_size_4204_; lean_object* v_receivers_4205_; lean_object* v___x_4206_; 
v_capacity_4203_ = lean_ctor_get(v_a_4198_, 2);
lean_inc(v_capacity_4203_);
v_size_4204_ = lean_ctor_get(v_a_4198_, 3);
lean_inc(v_size_4204_);
v_receivers_4205_ = lean_ctor_get(v_a_4198_, 7);
lean_inc(v_receivers_4205_);
lean_dec(v_a_4198_);
v___x_4206_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4205_, v_id_4185_);
lean_dec(v_receivers_4205_);
if (lean_obj_tag(v___x_4206_) == 1)
{
lean_object* v_val_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4226_; 
v_val_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4226_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_val_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4226_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4211_; uint8_t v___x_4212_; 
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = lean_nat_dec_eq(v_size_4204_, v___x_4211_);
lean_dec(v_size_4204_);
if (v___x_4212_ == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; lean_object* v___f_4217_; lean_object* v___x_4218_; 
lean_del_object(v___x_4209_);
lean_del_object(v___x_4200_);
v___x_4213_ = lean_nat_mod(v_val_4207_, v_capacity_4203_);
lean_dec(v_capacity_4203_);
v___x_4214_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4213_, v___y_4186_);
v___f_4215_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4215_, 0, v_val_4207_);
v___x_4216_ = lean_box(v_closed_4202_);
v___f_4217_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_4217_, 0, v___x_4211_);
lean_closure_set(v___f_4217_, 1, v___x_4216_);
lean_closure_set(v___f_4217_, 2, v___f_4215_);
v___x_4218_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4211_, v_closed_4202_, v___x_4214_, v___f_4217_);
return v___x_4218_;
}
else
{
lean_object* v___x_4219_; lean_object* v___x_4221_; 
lean_dec(v_val_4207_);
lean_dec(v_capacity_4203_);
v___x_4219_ = lean_box(v_closed_4202_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4219_);
v___x_4221_ = v___x_4200_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
lean_object* v___x_4223_; 
if (v_isShared_4210_ == 0)
{
lean_ctor_set_tag(v___x_4209_, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4221_);
v___x_4223_ = v___x_4209_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
}
else
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
lean_dec(v___x_4206_);
lean_dec(v_size_4204_);
lean_dec(v_capacity_4203_);
v___x_4227_ = lean_box(v_closed_4202_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4227_);
v___x_4229_ = v___x_4200_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
lean_object* v___x_4230_; 
v___x_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4229_);
return v___x_4230_;
}
}
}
else
{
lean_object* v___x_4232_; lean_object* v___x_4234_; 
lean_dec(v_a_4198_);
v___x_4232_ = lean_box(v_closed_4202_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4232_);
v___x_4234_ = v___x_4200_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4232_);
v___x_4234_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; 
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
return v___x_4235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v_id_4238_, lean_object* v___y_4239_, lean_object* v_x_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v_id_4238_, v___y_4239_, v_x_4240_);
lean_dec(v___y_4239_);
lean_dec(v_id_4238_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4243_, lean_object* v_x_4244_){
_start:
{
if (lean_obj_tag(v_x_4244_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4254_; 
lean_dec_ref(v_x_4243_);
v_a_4246_ = lean_ctor_get(v_x_4244_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_x_4244_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4248_ = v_x_4244_;
v_isShared_4249_ = v_isSharedCheck_4254_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v_x_4244_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4254_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4252_; 
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4251_);
return v___x_4252_;
}
}
}
else
{
lean_object* v___x_4255_; 
lean_dec_ref(v_x_4244_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v_x_4243_);
return v___x_4255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4256_, lean_object* v_x_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4256_, v_x_4257_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4266_, lean_object* v_receiverId_4267_, lean_object* v_receivers_4268_, lean_object* v_x_4269_){
_start:
{
if (lean_obj_tag(v_x_4269_) == 0)
{
lean_object* v___x_4271_; 
lean_dec(v_receivers_4268_);
lean_dec(v_receiverId_4267_);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v_x_4269_);
return v___x_4271_;
}
else
{
lean_object* v_a_4272_; 
v_a_4272_ = lean_ctor_get(v_x_4269_, 0);
if (lean_obj_tag(v_a_4272_) == 1)
{
lean_object* v___x_4273_; lean_object* v_producers_4274_; lean_object* v_waiters_4275_; lean_object* v_capacity_4276_; lean_object* v_size_4277_; lean_object* v_buffer_4278_; lean_object* v_write_4279_; lean_object* v_read_4280_; lean_object* v_nextId_4281_; uint8_t v_closed_4282_; lean_object* v_pos_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4297_; 
v___x_4273_ = lean_st_ref_take(v_a_4266_);
v_producers_4274_ = lean_ctor_get(v___x_4273_, 0);
v_waiters_4275_ = lean_ctor_get(v___x_4273_, 1);
v_capacity_4276_ = lean_ctor_get(v___x_4273_, 2);
v_size_4277_ = lean_ctor_get(v___x_4273_, 3);
v_buffer_4278_ = lean_ctor_get(v___x_4273_, 4);
v_write_4279_ = lean_ctor_get(v___x_4273_, 5);
v_read_4280_ = lean_ctor_get(v___x_4273_, 6);
v_nextId_4281_ = lean_ctor_get(v___x_4273_, 8);
v_closed_4282_ = lean_ctor_get_uint8(v___x_4273_, sizeof(void*)*10);
v_pos_4283_ = lean_ctor_get(v___x_4273_, 9);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4297_ == 0)
{
lean_object* v_unused_4298_; 
v_unused_4298_ = lean_ctor_get(v___x_4273_, 7);
lean_dec(v_unused_4298_);
v___x_4285_ = v___x_4273_;
v_isShared_4286_ = v_isSharedCheck_4297_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_pos_4283_);
lean_inc(v_nextId_4281_);
lean_inc(v_read_4280_);
lean_inc(v_write_4279_);
lean_inc(v_buffer_4278_);
lean_inc(v_size_4277_);
lean_inc(v_capacity_4276_);
lean_inc(v_waiters_4275_);
lean_inc(v_producers_4274_);
lean_dec(v___x_4273_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4297_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4287_; lean_object* v___x_4289_; 
v___x_4287_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4267_, v_receivers_4268_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 7, v___x_4287_);
v___x_4289_ = v___x_4285_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_producers_4274_);
lean_ctor_set(v_reuseFailAlloc_4296_, 1, v_waiters_4275_);
lean_ctor_set(v_reuseFailAlloc_4296_, 2, v_capacity_4276_);
lean_ctor_set(v_reuseFailAlloc_4296_, 3, v_size_4277_);
lean_ctor_set(v_reuseFailAlloc_4296_, 4, v_buffer_4278_);
lean_ctor_set(v_reuseFailAlloc_4296_, 5, v_write_4279_);
lean_ctor_set(v_reuseFailAlloc_4296_, 6, v_read_4280_);
lean_ctor_set(v_reuseFailAlloc_4296_, 7, v___x_4287_);
lean_ctor_set(v_reuseFailAlloc_4296_, 8, v_nextId_4281_);
lean_ctor_set(v_reuseFailAlloc_4296_, 9, v_pos_4283_);
lean_ctor_set_uint8(v_reuseFailAlloc_4296_, sizeof(void*)*10, v_closed_4282_);
v___x_4289_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
lean_object* v___x_4290_; lean_object* v___f_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; uint8_t v___x_4294_; lean_object* v___x_4295_; 
v___x_4290_ = lean_st_ref_set(v_a_4266_, v___x_4289_);
v___f_4291_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4291_, 0, v_x_4269_);
v___x_4292_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_4293_ = lean_unsigned_to_nat(0u);
v___x_4294_ = 0;
v___x_4295_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4293_, v___x_4294_, v___x_4292_, v___f_4291_);
return v___x_4295_;
}
}
}
else
{
lean_object* v___x_4299_; 
lean_dec_ref(v_x_4269_);
lean_dec(v_receivers_4268_);
lean_dec(v_receiverId_4267_);
v___x_4299_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4300_, lean_object* v_receiverId_4301_, lean_object* v_receivers_4302_, lean_object* v_x_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4300_, v_receiverId_4301_, v_receivers_4302_, v_x_4303_);
lean_dec(v_a_4300_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4306_){
_start:
{
if (lean_obj_tag(v_x_4306_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4316_; 
v_a_4308_ = lean_ctor_get(v_x_4306_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v_x_4306_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4310_ = v_x_4306_;
v_isShared_4311_ = v_isSharedCheck_4316_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v_x_4306_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4316_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4314_; 
v___x_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
return v___x_4314_;
}
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4329_; 
v_a_4317_ = lean_ctor_get(v_x_4306_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v_x_4306_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4319_ = v_x_4306_;
v_isShared_4320_ = v_isSharedCheck_4329_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v_x_4306_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4329_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v_size_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4326_; 
v_size_4321_ = lean_ctor_get(v_a_4317_, 3);
lean_inc(v_size_4321_);
lean_dec(v_a_4317_);
v___x_4322_ = lean_unsigned_to_nat(0u);
v___x_4323_ = lean_nat_dec_eq(v_size_4321_, v___x_4322_);
lean_dec(v_size_4321_);
v___x_4324_ = lean_box(v___x_4323_);
if (v_isShared_4320_ == 0)
{
lean_ctor_set(v___x_4319_, 0, v___x_4324_);
v___x_4326_ = v___x_4319_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4324_);
v___x_4326_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
lean_object* v___x_4327_; 
v___x_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
return v___x_4327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4330_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4334_){
_start:
{
lean_object* v___x_4336_; lean_object* v___f_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; lean_object* v___x_4342_; 
v___x_4336_ = lean_st_ref_get(v_a_4334_);
v___f_4337_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
v___x_4340_ = lean_unsigned_to_nat(0u);
v___x_4341_ = 0;
v___x_4342_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4340_, v___x_4341_, v___x_4339_, v___f_4337_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4343_);
lean_dec(v_a_4343_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4346_, lean_object* v_next_4347_){
_start:
{
lean_object* v___x_4349_; lean_object* v_fst_4351_; lean_object* v_snd_4352_; lean_object* v_value_4356_; lean_object* v_pos_4357_; lean_object* v_remaining_4358_; uint8_t v___x_4359_; 
v___x_4349_ = lean_st_ref_take(v_slot_4346_);
v_value_4356_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_value_4356_);
v_pos_4357_ = lean_ctor_get(v___x_4349_, 1);
lean_inc(v_pos_4357_);
v_remaining_4358_ = lean_ctor_get(v___x_4349_, 2);
lean_inc(v_remaining_4358_);
v___x_4359_ = lean_nat_dec_eq(v_next_4347_, v_pos_4357_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
lean_dec(v_remaining_4358_);
lean_dec(v_pos_4357_);
lean_dec(v_value_4356_);
v___x_4360_ = lean_box(0);
v___x_4361_ = lean_box(v___x_4359_);
v___x_4362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set(v___x_4362_, 1, v___x_4361_);
v_fst_4351_ = v___x_4362_;
v_snd_4352_ = v___x_4349_;
goto v___jp_4350_;
}
else
{
lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4381_; 
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4381_ == 0)
{
lean_object* v_unused_4382_; lean_object* v_unused_4383_; lean_object* v_unused_4384_; 
v_unused_4382_ = lean_ctor_get(v___x_4349_, 2);
lean_dec(v_unused_4382_);
v_unused_4383_ = lean_ctor_get(v___x_4349_, 1);
lean_dec(v_unused_4383_);
v_unused_4384_ = lean_ctor_get(v___x_4349_, 0);
lean_dec(v_unused_4384_);
v___x_4364_ = v___x_4349_;
v_isShared_4365_ = v_isSharedCheck_4381_;
goto v_resetjp_4363_;
}
else
{
lean_dec(v___x_4349_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4381_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4366_; uint8_t v___x_4367_; 
v___x_4366_ = lean_unsigned_to_nat(1u);
v___x_4367_ = lean_nat_dec_eq(v_remaining_4358_, v___x_4366_);
if (v___x_4367_ == 0)
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; 
v___x_4368_ = lean_box(v___x_4367_);
lean_inc(v_value_4356_);
v___x_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4369_, 0, v_value_4356_);
lean_ctor_set(v___x_4369_, 1, v___x_4368_);
v___x_4370_ = lean_nat_sub(v_remaining_4358_, v___x_4366_);
lean_dec(v_remaining_4358_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 2, v___x_4370_);
v___x_4372_ = v___x_4364_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_value_4356_);
lean_ctor_set(v_reuseFailAlloc_4373_, 1, v_pos_4357_);
lean_ctor_set(v_reuseFailAlloc_4373_, 2, v___x_4370_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
v_fst_4351_ = v___x_4369_;
v_snd_4352_ = v___x_4372_;
goto v___jp_4350_;
}
}
else
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4379_; 
lean_dec(v_remaining_4358_);
v___x_4374_ = lean_box(v___x_4359_);
v___x_4375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4375_, 0, v_value_4356_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
v___x_4376_ = lean_box(0);
v___x_4377_ = lean_unsigned_to_nat(0u);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 2, v___x_4377_);
lean_ctor_set(v___x_4364_, 0, v___x_4376_);
v___x_4379_ = v___x_4364_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4376_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v_pos_4357_);
lean_ctor_set(v_reuseFailAlloc_4380_, 2, v___x_4377_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
v_fst_4351_ = v___x_4375_;
v_snd_4352_ = v___x_4379_;
goto v___jp_4350_;
}
}
}
}
v___jp_4350_:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4353_ = lean_st_ref_set(v_slot_4346_, v_snd_4352_);
v___x_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4354_, 0, v_fst_4351_);
v___x_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
return v___x_4355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4385_, lean_object* v_next_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4385_, v_next_4386_);
lean_dec(v_next_4386_);
lean_dec(v_slot_4385_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4389_, uint8_t v_a_4390_, lean_object* v___f_4391_, lean_object* v_x_4392_){
_start:
{
if (lean_obj_tag(v_x_4392_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4402_; 
lean_dec_ref(v___f_4391_);
v_a_4394_ = lean_ctor_get(v_x_4392_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_x_4392_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4396_ = v_x_4392_;
v_isShared_4397_ = v_isSharedCheck_4402_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v_x_4392_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4402_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
return v___x_4400_;
}
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v_a_4403_ = lean_ctor_get(v_x_4392_, 0);
lean_inc(v_a_4403_);
lean_dec_ref(v_x_4392_);
v___x_4404_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4403_, v_next_4389_);
lean_dec(v_a_4403_);
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4405_, v_a_4390_, v___x_4404_, v___f_4391_);
return v___x_4406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4407_, lean_object* v_a_4408_, lean_object* v___f_4409_, lean_object* v_x_4410_, lean_object* v___y_4411_){
_start:
{
uint8_t v_a_11851__boxed_4412_; lean_object* v_res_4413_; 
v_a_11851__boxed_4412_ = lean_unbox(v_a_4408_);
v_res_4413_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4407_, v_a_11851__boxed_4412_, v___f_4409_, v_x_4410_);
lean_dec(v_next_4407_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4414_, lean_object* v___f_4415_, lean_object* v_____r_4416_, lean_object* v_st_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4420_ = lean_st_ref_set(v___y_4418_, v_st_4417_);
v___x_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
v___x_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4423_, v_a_4414_, v___x_4422_, v___f_4415_);
return v___x_4424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4425_, lean_object* v___f_4426_, lean_object* v_____r_4427_, lean_object* v_st_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
uint8_t v_a_11889__boxed_4431_; lean_object* v_res_4432_; 
v_a_11889__boxed_4431_ = lean_unbox(v_a_4425_);
v_res_4432_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_11889__boxed_4431_, v___f_4426_, v_____r_4427_, v_st_4428_, v___y_4429_);
lean_dec(v___y_4429_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4433_, lean_object* v_waiters_4434_, lean_object* v_capacity_4435_, lean_object* v_size_4436_, lean_object* v_buffer_4437_, lean_object* v_write_4438_, lean_object* v_read_4439_, lean_object* v_receivers_4440_, lean_object* v_nextId_4441_, uint8_t v_closed_4442_, lean_object* v_pos_4443_, lean_object* v___f_4444_, lean_object* v_a_4445_, lean_object* v_x_4446_){
_start:
{
if (lean_obj_tag(v_x_4446_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4456_; 
lean_dec(v_a_4445_);
lean_dec_ref(v___f_4444_);
lean_dec(v_pos_4443_);
lean_dec(v_nextId_4441_);
lean_dec(v_receivers_4440_);
lean_dec(v_read_4439_);
lean_dec(v_write_4438_);
lean_dec_ref(v_buffer_4437_);
lean_dec(v_size_4436_);
lean_dec(v_capacity_4435_);
lean_dec_ref(v_waiters_4434_);
lean_dec_ref(v_snd_4433_);
v_a_4448_ = lean_ctor_get(v_x_4446_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_x_4446_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4450_ = v_x_4446_;
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v_x_4446_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4456_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4454_; 
v___x_4454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4453_);
return v___x_4454_;
}
}
}
else
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_dec_ref(v_x_4446_);
v___x_4457_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4457_, 0, v_snd_4433_);
lean_ctor_set(v___x_4457_, 1, v_waiters_4434_);
lean_ctor_set(v___x_4457_, 2, v_capacity_4435_);
lean_ctor_set(v___x_4457_, 3, v_size_4436_);
lean_ctor_set(v___x_4457_, 4, v_buffer_4437_);
lean_ctor_set(v___x_4457_, 5, v_write_4438_);
lean_ctor_set(v___x_4457_, 6, v_read_4439_);
lean_ctor_set(v___x_4457_, 7, v_receivers_4440_);
lean_ctor_set(v___x_4457_, 8, v_nextId_4441_);
lean_ctor_set(v___x_4457_, 9, v_pos_4443_);
lean_ctor_set_uint8(v___x_4457_, sizeof(void*)*10, v_closed_4442_);
v___x_4458_ = lean_box(0);
v___x_4459_ = lean_apply_4(v___f_4444_, v___x_4458_, v___x_4457_, v_a_4445_, lean_box(0));
return v___x_4459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4460_, lean_object* v_waiters_4461_, lean_object* v_capacity_4462_, lean_object* v_size_4463_, lean_object* v_buffer_4464_, lean_object* v_write_4465_, lean_object* v_read_4466_, lean_object* v_receivers_4467_, lean_object* v_nextId_4468_, lean_object* v_closed_4469_, lean_object* v_pos_4470_, lean_object* v___f_4471_, lean_object* v_a_4472_, lean_object* v_x_4473_, lean_object* v___y_4474_){
_start:
{
uint8_t v_closed_boxed_4475_; lean_object* v_res_4476_; 
v_closed_boxed_4475_ = lean_unbox(v_closed_4469_);
v_res_4476_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4460_, v_waiters_4461_, v_capacity_4462_, v_size_4463_, v_buffer_4464_, v_write_4465_, v_read_4466_, v_receivers_4467_, v_nextId_4468_, v_closed_boxed_4475_, v_pos_4470_, v___f_4471_, v_a_4472_, v_x_4473_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4477_, lean_object* v_x_4478_){
_start:
{
if (lean_obj_tag(v_x_4478_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4488_; 
lean_dec(v_fst_4477_);
v_a_4480_ = lean_ctor_get(v_x_4478_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_x_4478_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4482_ = v_x_4478_;
v_isShared_4483_ = v_isSharedCheck_4488_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v_x_4478_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4488_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4480_);
v___x_4485_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4486_; 
v___x_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
return v___x_4486_;
}
}
}
else
{
lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4496_; 
v_isSharedCheck_4496_ = !lean_is_exclusive(v_x_4478_);
if (v_isSharedCheck_4496_ == 0)
{
lean_object* v_unused_4497_; 
v_unused_4497_ = lean_ctor_get(v_x_4478_, 0);
lean_dec(v_unused_4497_);
v___x_4490_ = v_x_4478_;
v_isShared_4491_ = v_isSharedCheck_4496_;
goto v_resetjp_4489_;
}
else
{
lean_dec(v_x_4478_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4496_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
lean_ctor_set(v___x_4490_, 0, v_fst_4477_);
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_fst_4477_);
v___x_4493_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4494_; 
v___x_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
return v___x_4494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4498_, lean_object* v_x_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4498_, v_x_4499_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, uint8_t v___x_4505_, lean_object* v_x_4506_){
_start:
{
if (lean_obj_tag(v_x_4506_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
v_a_4508_ = lean_ctor_get(v_x_4506_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_x_4506_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4510_ = v_x_4506_;
v_isShared_4511_ = v_isSharedCheck_4516_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v_x_4506_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4516_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
lean_object* v___x_4514_; 
v___x_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
return v___x_4514_;
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4564_; 
v_a_4517_ = lean_ctor_get(v_x_4506_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v_x_4506_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4519_ = v_x_4506_;
v_isShared_4520_ = v_isSharedCheck_4564_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v_x_4506_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4564_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v_fst_4521_; 
v_fst_4521_ = lean_ctor_get(v_a_4517_, 0);
lean_inc(v_fst_4521_);
if (lean_obj_tag(v_fst_4521_) == 1)
{
lean_object* v_snd_4522_; lean_object* v___f_4523_; lean_object* v___x_4524_; lean_object* v___f_4525_; uint8_t v___x_4526_; 
v_snd_4522_ = lean_ctor_get(v_a_4517_, 1);
lean_inc(v_snd_4522_);
lean_dec(v_a_4517_);
v___f_4523_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4523_, 0, v_fst_4521_);
v___x_4524_ = lean_box(v_a_4502_);
lean_inc_ref(v___f_4523_);
v___f_4525_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4525_, 0, v___x_4524_);
lean_closure_set(v___f_4525_, 1, v___f_4523_);
v___x_4526_ = lean_unbox(v_snd_4522_);
lean_dec(v_snd_4522_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; lean_object* v___x_4528_; 
lean_dec_ref(v___f_4525_);
lean_del_object(v___x_4519_);
v___x_4527_ = lean_box(0);
v___x_4528_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4502_, v___f_4523_, v___x_4527_, v_a_4503_, v_a_4504_);
lean_dec(v_a_4504_);
return v___x_4528_;
}
else
{
lean_object* v___x_4529_; lean_object* v_producers_4530_; lean_object* v_waiters_4531_; lean_object* v_capacity_4532_; lean_object* v_size_4533_; lean_object* v_buffer_4534_; lean_object* v_write_4535_; lean_object* v_read_4536_; lean_object* v_receivers_4537_; lean_object* v_nextId_4538_; uint8_t v_closed_4539_; lean_object* v_pos_4540_; lean_object* v___x_4541_; 
v___x_4529_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4503_);
v_producers_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc_ref(v_producers_4530_);
v_waiters_4531_ = lean_ctor_get(v___x_4529_, 1);
lean_inc_ref(v_waiters_4531_);
v_capacity_4532_ = lean_ctor_get(v___x_4529_, 2);
lean_inc(v_capacity_4532_);
v_size_4533_ = lean_ctor_get(v___x_4529_, 3);
lean_inc(v_size_4533_);
v_buffer_4534_ = lean_ctor_get(v___x_4529_, 4);
lean_inc_ref(v_buffer_4534_);
v_write_4535_ = lean_ctor_get(v___x_4529_, 5);
lean_inc(v_write_4535_);
v_read_4536_ = lean_ctor_get(v___x_4529_, 6);
lean_inc(v_read_4536_);
v_receivers_4537_ = lean_ctor_get(v___x_4529_, 7);
lean_inc(v_receivers_4537_);
v_nextId_4538_ = lean_ctor_get(v___x_4529_, 8);
lean_inc(v_nextId_4538_);
v_closed_4539_ = lean_ctor_get_uint8(v___x_4529_, sizeof(void*)*10);
v_pos_4540_ = lean_ctor_get(v___x_4529_, 9);
lean_inc(v_pos_4540_);
v___x_4541_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4530_);
if (lean_obj_tag(v___x_4541_) == 1)
{
lean_object* v_val_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4560_; 
lean_dec_ref(v___x_4529_);
lean_dec_ref(v___f_4523_);
v_val_4542_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4544_ = v___x_4541_;
v_isShared_4545_ = v_isSharedCheck_4560_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_val_4542_);
lean_dec(v___x_4541_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4560_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v_fst_4546_; lean_object* v_snd_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___f_4551_; lean_object* v___x_4553_; 
v_fst_4546_ = lean_ctor_get(v_val_4542_, 0);
lean_inc(v_fst_4546_);
v_snd_4547_ = lean_ctor_get(v_val_4542_, 1);
lean_inc(v_snd_4547_);
lean_dec(v_val_4542_);
v___x_4548_ = lean_box(v___x_4505_);
v___x_4549_ = lean_io_promise_resolve(v___x_4548_, v_fst_4546_);
lean_dec(v_fst_4546_);
v___x_4550_ = lean_box(v_closed_4539_);
v___f_4551_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4551_, 0, v_snd_4547_);
lean_closure_set(v___f_4551_, 1, v_waiters_4531_);
lean_closure_set(v___f_4551_, 2, v_capacity_4532_);
lean_closure_set(v___f_4551_, 3, v_size_4533_);
lean_closure_set(v___f_4551_, 4, v_buffer_4534_);
lean_closure_set(v___f_4551_, 5, v_write_4535_);
lean_closure_set(v___f_4551_, 6, v_read_4536_);
lean_closure_set(v___f_4551_, 7, v_receivers_4537_);
lean_closure_set(v___f_4551_, 8, v_nextId_4538_);
lean_closure_set(v___f_4551_, 9, v___x_4550_);
lean_closure_set(v___f_4551_, 10, v_pos_4540_);
lean_closure_set(v___f_4551_, 11, v___f_4525_);
lean_closure_set(v___f_4551_, 12, v_a_4504_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 0, v___x_4549_);
v___x_4553_ = v___x_4519_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4549_);
v___x_4553_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4555_; 
if (v_isShared_4545_ == 0)
{
lean_ctor_set_tag(v___x_4544_, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4553_);
v___x_4555_ = v___x_4544_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v___x_4553_);
v___x_4555_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4556_ = lean_unsigned_to_nat(0u);
v___x_4557_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4556_, v_a_4502_, v___x_4555_, v___f_4551_);
return v___x_4557_;
}
}
}
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
lean_dec(v___x_4541_);
lean_dec(v_pos_4540_);
lean_dec(v_nextId_4538_);
lean_dec(v_receivers_4537_);
lean_dec(v_read_4536_);
lean_dec(v_write_4535_);
lean_dec_ref(v_buffer_4534_);
lean_dec(v_size_4533_);
lean_dec(v_capacity_4532_);
lean_dec_ref(v_waiters_4531_);
lean_dec_ref(v___f_4525_);
lean_del_object(v___x_4519_);
v___x_4561_ = lean_box(0);
v___x_4562_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4502_, v___f_4523_, v___x_4561_, v___x_4529_, v_a_4504_);
lean_dec(v_a_4504_);
return v___x_4562_;
}
}
}
else
{
lean_object* v___x_4563_; 
lean_dec(v_fst_4521_);
lean_del_object(v___x_4519_);
lean_dec(v_a_4517_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
v___x_4563_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v___x_4568_, lean_object* v_x_4569_, lean_object* v___y_4570_){
_start:
{
uint8_t v_a_12004__boxed_4571_; uint8_t v___x_12007__boxed_4572_; lean_object* v_res_4573_; 
v_a_12004__boxed_4571_ = lean_unbox(v_a_4565_);
v___x_12007__boxed_4572_ = lean_unbox(v___x_4568_);
v_res_4573_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12004__boxed_4571_, v_a_4566_, v_a_4567_, v___x_12007__boxed_4572_, v_x_4569_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4574_, lean_object* v_next_4575_, lean_object* v_a_4576_, lean_object* v_x_4577_){
_start:
{
if (lean_obj_tag(v_x_4577_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_a_4576_);
lean_dec(v_next_4575_);
lean_dec_ref(v_a_4574_);
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
lean_object* v_a_4588_; uint8_t v___x_4589_; 
v_a_4588_ = lean_ctor_get(v_x_4577_, 0);
lean_inc(v_a_4588_);
lean_dec_ref(v_x_4577_);
v___x_4589_ = lean_unbox(v_a_4588_);
if (v___x_4589_ == 0)
{
lean_object* v_capacity_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; uint8_t v___x_4593_; lean_object* v___x_4594_; lean_object* v___f_4595_; lean_object* v___f_4596_; lean_object* v___x_4597_; uint8_t v___x_4598_; lean_object* v___x_4599_; 
v_capacity_4590_ = lean_ctor_get(v_a_4574_, 2);
v___x_4591_ = lean_nat_mod(v_next_4575_, v_capacity_4590_);
v___x_4592_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4591_, v_a_4576_);
v___x_4593_ = 1;
v___x_4594_ = lean_box(v___x_4593_);
lean_inc(v_a_4588_);
v___f_4595_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4595_, 0, v_a_4588_);
lean_closure_set(v___f_4595_, 1, v_a_4574_);
lean_closure_set(v___f_4595_, 2, v_a_4576_);
lean_closure_set(v___f_4595_, 3, v___x_4594_);
lean_inc(v_a_4588_);
v___f_4596_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4596_, 0, v_next_4575_);
lean_closure_set(v___f_4596_, 1, v_a_4588_);
lean_closure_set(v___f_4596_, 2, v___f_4595_);
v___x_4597_ = lean_unsigned_to_nat(0u);
v___x_4598_ = lean_unbox(v_a_4588_);
lean_dec(v_a_4588_);
v___x_4599_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4597_, v___x_4598_, v___x_4592_, v___f_4596_);
return v___x_4599_;
}
else
{
lean_object* v___x_4600_; 
lean_dec(v_a_4588_);
lean_dec(v_a_4576_);
lean_dec(v_next_4575_);
lean_dec_ref(v_a_4574_);
v___x_4600_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4600_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4601_, lean_object* v_next_4602_, lean_object* v_a_4603_, lean_object* v_x_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4601_, v_next_4602_, v_a_4603_, v_x_4604_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4607_, lean_object* v_next_4608_, lean_object* v_x_4609_){
_start:
{
if (lean_obj_tag(v_x_4609_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4619_; 
lean_dec(v_next_4608_);
lean_dec(v_a_4607_);
v_a_4611_ = lean_ctor_get(v_x_4609_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v_x_4609_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4613_ = v_x_4609_;
v_isShared_4614_ = v_isSharedCheck_4619_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v_x_4609_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4619_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4611_);
v___x_4616_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v___x_4616_);
return v___x_4617_;
}
}
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4621_; lean_object* v___f_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; lean_object* v___x_4625_; 
v_a_4620_ = lean_ctor_get(v_x_4609_, 0);
lean_inc(v_a_4620_);
lean_dec_ref(v_x_4609_);
v___x_4621_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4607_);
v___f_4622_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4622_, 0, v_a_4620_);
lean_closure_set(v___f_4622_, 1, v_next_4608_);
lean_closure_set(v___f_4622_, 2, v_a_4607_);
v___x_4623_ = lean_unsigned_to_nat(0u);
v___x_4624_ = 0;
v___x_4625_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4623_, v___x_4624_, v___x_4621_, v___f_4622_);
return v___x_4625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4626_, lean_object* v_next_4627_, lean_object* v_x_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4626_, v_next_4627_, v_x_4628_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v___x_4634_; lean_object* v___f_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; uint8_t v___x_4639_; lean_object* v___x_4640_; 
v___x_4634_ = lean_st_ref_get(v_a_4632_);
v___f_4635_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4635_, 0, v_a_4632_);
lean_closure_set(v___f_4635_, 1, v_next_4631_);
v___x_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4634_);
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
v___x_4638_ = lean_unsigned_to_nat(0u);
v___x_4639_ = 0;
v___x_4640_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4638_, v___x_4639_, v___x_4637_, v___f_4635_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4641_, lean_object* v_a_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4641_, v_a_4642_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4645_, lean_object* v_a_4646_, lean_object* v_x_4647_){
_start:
{
if (lean_obj_tag(v_x_4647_) == 0)
{
lean_object* v_a_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4657_; 
lean_dec(v_a_4646_);
lean_dec(v_receiverId_4645_);
v_a_4649_ = lean_ctor_get(v_x_4647_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_x_4647_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4651_ = v_x_4647_;
v_isShared_4652_ = v_isSharedCheck_4657_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_a_4649_);
lean_dec(v_x_4647_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4657_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4654_; 
if (v_isShared_4652_ == 0)
{
v___x_4654_ = v___x_4651_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4649_);
v___x_4654_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
lean_object* v___x_4655_; 
v___x_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4654_);
return v___x_4655_;
}
}
}
else
{
lean_object* v_a_4658_; lean_object* v_receivers_4659_; lean_object* v___x_4660_; 
v_a_4658_ = lean_ctor_get(v_x_4647_, 0);
lean_inc(v_a_4658_);
lean_dec_ref(v_x_4647_);
v_receivers_4659_ = lean_ctor_get(v_a_4658_, 7);
lean_inc(v_receivers_4659_);
lean_dec(v_a_4658_);
v___x_4660_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4659_, v_receiverId_4645_);
if (lean_obj_tag(v___x_4660_) == 1)
{
lean_object* v_val_4661_; lean_object* v___x_4662_; lean_object* v___f_4663_; lean_object* v___x_4664_; uint8_t v___x_4665_; lean_object* v___x_4666_; 
v_val_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_val_4661_);
lean_dec_ref(v___x_4660_);
lean_inc(v_a_4646_);
v___x_4662_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4661_, v_a_4646_);
v___f_4663_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4663_, 0, v_a_4646_);
lean_closure_set(v___f_4663_, 1, v_receiverId_4645_);
lean_closure_set(v___f_4663_, 2, v_receivers_4659_);
v___x_4664_ = lean_unsigned_to_nat(0u);
v___x_4665_ = 0;
v___x_4666_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4664_, v___x_4665_, v___x_4662_, v___f_4663_);
return v___x_4666_;
}
else
{
lean_object* v___x_4667_; 
lean_dec(v___x_4660_);
lean_dec(v_receivers_4659_);
lean_dec(v_a_4646_);
lean_dec(v_receiverId_4645_);
v___x_4667_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4668_, lean_object* v_a_4669_, lean_object* v_x_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4668_, v_a_4669_, v_x_4670_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v___x_4676_; lean_object* v___f_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; uint8_t v___x_4681_; lean_object* v___x_4682_; 
v___x_4676_ = lean_st_ref_get(v_a_4674_);
v___f_4677_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4677_, 0, v_receiverId_4673_);
lean_closure_set(v___f_4677_, 1, v_a_4674_);
v___x_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4676_);
v___x_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
v___x_4680_ = lean_unsigned_to_nat(0u);
v___x_4681_ = 0;
v___x_4682_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4680_, v___x_4681_, v___x_4679_, v___f_4677_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4683_, lean_object* v_a_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4683_, v_a_4684_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4691_, lean_object* v___y_4692_, lean_object* v___f_4693_, lean_object* v_x_4694_){
_start:
{
if (lean_obj_tag(v_x_4694_) == 0)
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4704_; 
lean_dec_ref(v___f_4693_);
lean_dec(v___y_4692_);
lean_dec(v_id_4691_);
v_a_4696_ = lean_ctor_get(v_x_4694_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v_x_4694_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4698_ = v_x_4694_;
v_isShared_4699_ = v_isSharedCheck_4704_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v_x_4694_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4704_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4701_; 
if (v_isShared_4699_ == 0)
{
v___x_4701_ = v___x_4698_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4696_);
v___x_4701_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
lean_object* v___x_4702_; 
v___x_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4702_, 0, v___x_4701_);
return v___x_4702_;
}
}
}
else
{
lean_object* v_a_4705_; uint8_t v___x_4706_; 
v_a_4705_ = lean_ctor_get(v_x_4694_, 0);
lean_inc(v_a_4705_);
lean_dec_ref(v_x_4694_);
v___x_4706_ = lean_unbox(v_a_4705_);
lean_dec(v_a_4705_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4707_; 
lean_dec_ref(v___f_4693_);
lean_dec(v___y_4692_);
lean_dec(v_id_4691_);
v___x_4707_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1));
return v___x_4707_;
}
else
{
lean_object* v___x_4708_; lean_object* v___x_4709_; uint8_t v___x_4710_; lean_object* v___x_4711_; 
v___x_4708_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4691_, v___y_4692_);
v___x_4709_ = lean_unsigned_to_nat(0u);
v___x_4710_ = 0;
v___x_4711_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4709_, v___x_4710_, v___x_4708_, v___f_4693_);
return v___x_4711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4712_, lean_object* v___y_4713_, lean_object* v___f_4714_, lean_object* v_x_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4712_, v___y_4713_, v___f_4714_, v_x_4715_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4718_, lean_object* v___f_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v___x_4722_; lean_object* v___f_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; lean_object* v___x_4728_; lean_object* v___f_4729_; lean_object* v___x_4730_; 
v___x_4722_ = lean_st_ref_get(v___y_4720_);
lean_inc(v___y_4720_);
lean_inc(v_id_4718_);
v___f_4723_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_4723_, 0, v_id_4718_);
lean_closure_set(v___f_4723_, 1, v___y_4720_);
v___x_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4722_);
v___x_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4724_);
v___x_4726_ = lean_unsigned_to_nat(0u);
v___x_4727_ = 0;
v___x_4728_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4726_, v___x_4727_, v___x_4725_, v___f_4723_);
v___f_4729_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4729_, 0, v_id_4718_);
lean_closure_set(v___f_4729_, 1, v___y_4720_);
lean_closure_set(v___f_4729_, 2, v___f_4719_);
v___x_4730_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4726_, v___x_4727_, v___x_4728_, v___f_4729_);
return v___x_4730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4731_, lean_object* v___f_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4731_, v___f_4732_, v___y_4733_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4738_){
_start:
{
lean_object* v_state_4739_; lean_object* v_id_4740_; lean_object* v___f_4741_; lean_object* v___f_4742_; lean_object* v___f_4743_; lean_object* v___f_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; 
v_state_4739_ = lean_ctor_get(v_ch_4738_, 0);
lean_inc_ref(v_state_4739_);
v_id_4740_ = lean_ctor_get(v_ch_4738_, 1);
lean_inc(v_id_4740_);
v___f_4741_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4742_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4742_, 0, v_ch_4738_);
v___f_4743_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4744_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4744_, 0, v_id_4740_);
lean_closure_set(v___f_4744_, 1, v___f_4743_);
lean_inc_ref(v_state_4739_);
v___x_4745_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4745_, 0, lean_box(0));
lean_closure_set(v___x_4745_, 1, lean_box(0));
lean_closure_set(v___x_4745_, 2, v_state_4739_);
lean_closure_set(v___x_4745_, 3, v___f_4744_);
v___x_4746_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4746_, 0, lean_box(0));
lean_closure_set(v___x_4746_, 1, lean_box(0));
lean_closure_set(v___x_4746_, 2, v_state_4739_);
lean_closure_set(v___x_4746_, 3, v___f_4741_);
v___x_4747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4745_);
lean_ctor_set(v___x_4747_, 1, v___f_4742_);
lean_ctor_set(v___x_4747_, 2, v___x_4746_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4748_, lean_object* v_ch_4749_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4751_, lean_object* v_receiverId_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v___x_4755_; 
v___x_4755_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4752_, v_a_4753_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4756_, lean_object* v_receiverId_4757_, lean_object* v_a_4758_, lean_object* v___y_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4756_, v_receiverId_4757_, v_a_4758_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4761_, lean_object* v_q_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v___x_4765_; 
v___x_4765_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4762_, v___y_4763_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4766_, lean_object* v_q_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4766_, v_q_4767_, v___y_4768_);
lean_dec(v___y_4768_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4771_, lean_object* v_slot_4772_, lean_object* v_next_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v___x_4776_; 
v___x_4776_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4772_, v_next_4773_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4777_, lean_object* v_slot_4778_, lean_object* v_next_4779_, lean_object* v_a_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4777_, v_slot_4778_, v_next_4779_, v_a_4780_);
lean_dec(v_a_4780_);
lean_dec(v_next_4779_);
lean_dec(v_slot_4778_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4783_, lean_object* v_a_4784_){
_start:
{
lean_object* v___x_4786_; 
v___x_4786_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4784_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4787_, lean_object* v_a_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4787_, v_a_4788_);
lean_dec(v_a_4788_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4791_, lean_object* v_next_4792_, lean_object* v_a_4793_){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4792_, v_a_4793_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4796_, lean_object* v_next_4797_, lean_object* v_a_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_res_4800_; 
v_res_4800_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4796_, v_next_4797_, v_a_4798_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4801_, lean_object* v_x_4802_, lean_object* v_x_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4802_, v_x_4803_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4807_, lean_object* v_x_4808_, lean_object* v_x_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4807_, v_x_4808_, v_x_4809_, v___y_4810_);
lean_dec(v___y_4810_);
return v_res_4812_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4814_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4814_);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4817_, lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_Std_Broadcast_new___redArg(v_capacity_4817_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4820_, lean_object* v_capacity_4821_, lean_object* v_h_4822_){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4821_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4825_, lean_object* v_capacity_4826_, lean_object* v_h_4827_, lean_object* v_a_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Std_Broadcast_new(v_00_u03b1_4825_, v_capacity_4826_, v_h_4827_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4830_, lean_object* v_v_4831_){
_start:
{
lean_object* v___x_4833_; 
v___x_4833_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4830_, v_v_4831_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4834_, lean_object* v_v_4835_, lean_object* v_a_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l_Std_Broadcast_trySend___redArg(v_ch_4834_, v_v_4835_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4838_, lean_object* v_ch_4839_, lean_object* v_v_4840_){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4839_, v_v_4840_);
return v___x_4842_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4843_, lean_object* v_ch_4844_, lean_object* v_v_4845_, lean_object* v_a_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_Std_Broadcast_trySend(v_00_u03b1_4843_, v_ch_4844_, v_v_4845_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4848_){
_start:
{
lean_object* v___x_4850_; 
v___x_4850_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4848_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4858_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4853_ = v___x_4850_;
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4850_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4854_ == 0)
{
v___x_4856_ = v___x_4853_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4851_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
else
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4866_; 
v_a_4859_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4861_ = v___x_4850_;
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4850_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4864_; 
if (v_isShared_4862_ == 0)
{
v___x_4864_ = v___x_4861_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_a_4859_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v_res_4869_; 
v_res_4869_ = l_Std_Broadcast_subscribe___redArg(v_ch_4867_);
return v_res_4869_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_4870_, lean_object* v_ch_4871_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4871_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
v_a_4882_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___x_4873_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4873_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_4890_, lean_object* v_ch_4891_, lean_object* v_a_4892_){
_start:
{
lean_object* v_res_4893_; 
v_res_4893_ = l_Std_Broadcast_subscribe(v_00_u03b1_4890_, v_ch_4891_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_4894_){
_start:
{
lean_object* v___x_4896_; 
v___x_4896_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_4894_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4922_; 
v_a_4905_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4907_ = v___x_4896_;
v_isShared_4908_ = v_isSharedCheck_4922_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4896_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4922_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
uint8_t v___x_4909_; 
v___x_4909_ = lean_unbox(v_a_4905_);
lean_dec(v_a_4905_);
switch(v___x_4909_)
{
case 0:
{
lean_object* v___x_4910_; lean_object* v___x_4912_; 
v___x_4910_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4910_);
v___x_4912_ = v___x_4907_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
case 1:
{
lean_object* v___x_4914_; lean_object* v___x_4916_; 
v___x_4914_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4914_);
v___x_4916_ = v___x_4907_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4914_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
default: 
{
lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4918_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4918_);
v___x_4920_ = v___x_4907_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_4923_, lean_object* v_a_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l_Std_Broadcast_close___redArg(v_ch_4923_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_4926_, lean_object* v_ch_4927_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_4927_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4929_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4929_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4955_; 
v_a_4938_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4940_ = v___x_4929_;
v_isShared_4941_ = v_isSharedCheck_4955_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4929_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4955_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
uint8_t v___x_4942_; 
v___x_4942_ = lean_unbox(v_a_4938_);
lean_dec(v_a_4938_);
switch(v___x_4942_)
{
case 0:
{
lean_object* v___x_4943_; lean_object* v___x_4945_; 
v___x_4943_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 0, v___x_4943_);
v___x_4945_ = v___x_4940_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4943_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
case 1:
{
lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4947_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 0, v___x_4947_);
v___x_4949_ = v___x_4940_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
default: 
{
lean_object* v___x_4951_; lean_object* v___x_4953_; 
v___x_4951_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_4941_ == 0)
{
lean_ctor_set(v___x_4940_, 0, v___x_4951_);
v___x_4953_ = v___x_4940_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4951_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_4956_, lean_object* v_ch_4957_, lean_object* v_a_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_Std_Broadcast_close(v_00_u03b1_4956_, v_ch_4957_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_4960_){
_start:
{
lean_object* v___y_4963_; 
if (lean_obj_tag(v_x_4960_) == 0)
{
lean_object* v_a_4967_; uint8_t v___x_4968_; 
v_a_4967_ = lean_ctor_get(v_x_4960_, 0);
lean_inc(v_a_4967_);
lean_dec_ref(v_x_4960_);
v___x_4968_ = lean_unbox(v_a_4967_);
lean_dec(v_a_4967_);
switch(v___x_4968_)
{
case 0:
{
lean_object* v___x_4969_; 
v___x_4969_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_4963_ = v___x_4969_;
goto v___jp_4962_;
}
case 1:
{
lean_object* v___x_4970_; 
v___x_4970_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_4963_ = v___x_4970_;
goto v___jp_4962_;
}
default: 
{
lean_object* v___x_4971_; 
v___x_4971_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_4963_ = v___x_4971_;
goto v___jp_4962_;
}
}
}
else
{
lean_object* v_a_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4980_; 
v_a_4972_ = lean_ctor_get(v_x_4960_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v_x_4960_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4974_ = v_x_4960_;
v_isShared_4975_ = v_isSharedCheck_4980_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_a_4972_);
lean_dec(v_x_4960_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4980_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___x_4977_; 
if (v_isShared_4975_ == 0)
{
v___x_4977_ = v___x_4974_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4972_);
v___x_4977_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
lean_object* v___x_4978_; 
v___x_4978_ = lean_task_pure(v___x_4977_);
return v___x_4978_;
}
}
}
v___jp_4962_:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4964_ = lean_mk_io_user_error(v___y_4963_);
v___x_4965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4964_);
v___x_4966_ = lean_task_pure(v___x_4965_);
return v___x_4966_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Std_Broadcast_send___redArg___lam__0(v_x_4981_);
return v_res_4983_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_4985_, lean_object* v_v_4986_){
_start:
{
lean_object* v___x_4988_; lean_object* v___f_4989_; lean_object* v___x_4990_; uint8_t v___x_4991_; lean_object* v___x_4992_; 
v___x_4988_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_4985_, v_v_4986_);
v___f_4989_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_4990_ = lean_unsigned_to_nat(0u);
v___x_4991_ = 1;
v___x_4992_ = lean_io_bind_task(v___x_4988_, v___f_4989_, v___x_4990_, v___x_4991_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_4993_, lean_object* v_v_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Std_Broadcast_send___redArg(v_ch_4993_, v_v_4994_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_4997_, lean_object* v_ch_4998_, lean_object* v_v_4999_){
_start:
{
lean_object* v___x_5001_; lean_object* v___f_5002_; lean_object* v___x_5003_; uint8_t v___x_5004_; lean_object* v___x_5005_; 
v___x_5001_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_4998_, v_v_4999_);
v___f_5002_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5003_ = lean_unsigned_to_nat(0u);
v___x_5004_ = 1;
v___x_5005_ = lean_io_bind_task(v___x_5001_, v___f_5002_, v___x_5003_, v___x_5004_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5006_, lean_object* v_ch_5007_, lean_object* v_v_5008_, lean_object* v_a_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l_Std_Broadcast_send(v_00_u03b1_5006_, v_ch_5007_, v_v_5008_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5011_){
_start:
{
lean_object* v___x_5013_; 
v___x_5013_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5011_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5014_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5017_, lean_object* v_ch_5018_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5018_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5021_, lean_object* v_ch_5022_, lean_object* v_a_5023_){
_start:
{
lean_object* v_res_5024_; 
v_res_5024_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5021_, v_ch_5022_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5025_){
_start:
{
lean_object* v___x_5027_; 
v___x_5027_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5025_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5028_, lean_object* v_a_5029_){
_start:
{
lean_object* v_res_5030_; 
v_res_5030_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5028_);
return v_res_5030_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5031_, lean_object* v_inst_5032_, lean_object* v_ch_5033_){
_start:
{
lean_object* v___x_5035_; 
v___x_5035_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5033_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5036_, lean_object* v_inst_5037_, lean_object* v_ch_5038_, lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5036_, v_inst_5037_, v_ch_5038_);
lean_dec(v_inst_5037_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5041_){
_start:
{
lean_object* v___x_5042_; 
v___x_5042_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5043_, lean_object* v_inst_5044_, lean_object* v_ch_5045_){
_start:
{
lean_object* v___x_5046_; 
v___x_5046_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5045_);
return v___x_5046_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5047_, lean_object* v_inst_5048_, lean_object* v_ch_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5047_, v_inst_5048_, v_ch_5049_);
lean_dec(v_inst_5048_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5051_){
_start:
{
lean_object* v___x_5053_; 
v___x_5053_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5051_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5054_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5057_, lean_object* v_ch_5058_){
_start:
{
lean_object* v___x_5060_; 
v___x_5060_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5058_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5061_, lean_object* v_ch_5062_, lean_object* v_a_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5061_, v_ch_5062_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5065_, lean_object* v_ch_5066_, lean_object* v_prio_5067_){
_start:
{
lean_object* v___x_5069_; 
v___x_5069_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5065_, v_ch_5066_, v_prio_5067_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5070_, lean_object* v_ch_5071_, lean_object* v_prio_5072_, lean_object* v_a_5073_){
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5070_, v_ch_5071_, v_prio_5072_);
return v_res_5074_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5075_, lean_object* v_f_5076_, lean_object* v_ch_5077_, lean_object* v_prio_5078_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5076_, v_ch_5077_, v_prio_5078_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5081_, lean_object* v_f_5082_, lean_object* v_ch_5083_, lean_object* v_prio_5084_, lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5081_, v_f_5082_, v_ch_5083_, v_prio_5084_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5092_, lean_object* v_inst_5093_){
_start:
{
lean_object* v___x_5094_; 
v___x_5094_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5095_, lean_object* v_inst_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5095_, v_inst_5096_);
lean_dec(v_inst_5096_);
return v_res_5097_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_5098_){
_start:
{
lean_object* v___x_5099_; 
v___x_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5099_, 0, v_a_5098_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_5100_, lean_object* v_x_5101_){
_start:
{
if (lean_obj_tag(v_x_5101_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5111_; 
lean_dec_ref(v___f_5100_);
v_a_5103_ = lean_ctor_get(v_x_5101_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v_x_5101_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5105_ = v_x_5101_;
v_isShared_5106_ = v_isSharedCheck_5111_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v_x_5101_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5111_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
lean_object* v___x_5109_; 
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
return v___x_5109_;
}
}
}
else
{
lean_object* v_a_5112_; 
v_a_5112_ = lean_ctor_get(v_x_5101_, 0);
lean_inc(v_a_5112_);
lean_dec_ref(v_x_5101_);
if (lean_obj_tag(v_a_5112_) == 0)
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5121_; 
lean_dec_ref(v___f_5100_);
v_a_5113_ = lean_ctor_get(v_a_5112_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v_a_5112_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5115_ = v_a_5112_;
v_isShared_5116_ = v_isSharedCheck_5121_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v_a_5112_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5121_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
lean_object* v___x_5119_; 
v___x_5119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5119_, 0, v___x_5118_);
return v___x_5119_;
}
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5123_; uint8_t v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v_a_5122_ = lean_ctor_get(v_a_5112_, 0);
lean_inc(v_a_5122_);
lean_dec_ref(v_a_5112_);
v___x_5123_ = lean_unsigned_to_nat(0u);
v___x_5124_ = 0;
v___x_5125_ = lean_task_map(v___f_5100_, v_a_5122_, v___x_5123_, v___x_5124_);
v___x_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5126_, 0, v___x_5125_);
return v___x_5126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_5127_, lean_object* v_x_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(v___f_5127_, v_x_5128_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_5131_, lean_object* v_receiver_5132_){
_start:
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; uint8_t v___x_5139_; lean_object* v___x_5140_; 
v___x_5134_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5132_);
v___x_5135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5135_, 0, v___x_5134_);
v___x_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5136_, 0, v___x_5135_);
v___x_5137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
v___x_5138_ = lean_unsigned_to_nat(0u);
v___x_5139_ = 0;
v___x_5140_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5138_, v___x_5139_, v___x_5137_, v___f_5131_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_5141_, lean_object* v_receiver_5142_, lean_object* v___y_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(v___f_5141_, v_receiver_5142_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5150_, lean_object* v_inst_5151_){
_start:
{
lean_object* v___f_5152_; 
v___f_5152_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2));
return v___f_5152_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5153_, lean_object* v_inst_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5153_, v_inst_5154_);
lean_dec(v_inst_5154_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__1(lean_object* v_a_5156_){
_start:
{
lean_object* v___x_5157_; 
v___x_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5157_, 0, v_a_5156_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_5162_, lean_object* v_x_5163_){
_start:
{
if (lean_obj_tag(v_x_5163_) == 0)
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5173_; 
lean_dec_ref(v___f_5162_);
v_a_5165_ = lean_ctor_get(v_x_5163_, 0);
v_isSharedCheck_5173_ = !lean_is_exclusive(v_x_5163_);
if (v_isSharedCheck_5173_ == 0)
{
v___x_5167_ = v_x_5163_;
v_isShared_5168_ = v_isSharedCheck_5173_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v_x_5163_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5173_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5171_; 
v___x_5171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5171_, 0, v___x_5170_);
return v___x_5171_;
}
}
}
else
{
lean_object* v_a_5174_; lean_object* v___x_5175_; uint8_t v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v_a_5174_ = lean_ctor_get(v_x_5163_, 0);
lean_inc(v_a_5174_);
lean_dec_ref(v_x_5163_);
v___x_5175_ = lean_unsigned_to_nat(0u);
v___x_5176_ = 0;
v___x_5177_ = lean_task_map(v___f_5162_, v_a_5174_, v___x_5175_, v___x_5176_);
v___x_5178_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1));
v___x_5179_ = lean_task_map(v___x_5178_, v___x_5177_, v___x_5175_, v___x_5176_);
v___x_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5179_);
return v___x_5180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_5181_, lean_object* v_x_5182_, lean_object* v___y_5183_){
_start:
{
lean_object* v_res_5184_; 
v_res_5184_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(v___f_5181_, v_x_5182_);
return v_res_5184_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5185_, lean_object* v___f_5186_, lean_object* v_receiver_5187_, lean_object* v_x_5188_){
_start:
{
lean_object* v___x_5190_; lean_object* v___x_5191_; uint8_t v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; uint8_t v___x_5196_; lean_object* v___x_5197_; 
v___x_5190_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5187_, v_x_5188_);
v___x_5191_ = lean_unsigned_to_nat(0u);
v___x_5192_ = 1;
v___x_5193_ = lean_io_bind_task(v___x_5190_, v___f_5185_, v___x_5191_, v___x_5192_);
v___x_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5193_);
v___x_5195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5195_, 0, v___x_5194_);
v___x_5196_ = 0;
v___x_5197_ = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5191_, v___x_5196_, v___x_5195_, v___f_5186_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5198_, lean_object* v___f_5199_, lean_object* v_receiver_5200_, lean_object* v_x_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(v___f_5198_, v___f_5199_, v_receiver_5200_, v_x_5201_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(lean_object* v_x_5204_){
_start:
{
lean_object* v___x_5206_; 
v___x_5206_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v_x_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(v_x_5207_);
lean_dec_ref(v_x_5207_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_5210_, lean_object* v_socket_5211_, lean_object* v_x_5212_, lean_object* v___y_5213_){
_start:
{
lean_object* v___x_5215_; 
v___x_5215_ = lean_apply_3(v___f_5210_, v_socket_5211_, v___y_5213_, lean_box(0));
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_5216_, lean_object* v_socket_5217_, lean_object* v_x_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(v___f_5216_, v_socket_5217_, v_x_5218_, v___y_5219_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(lean_object* v___f_5222_, lean_object* v___x_5223_, lean_object* v_socket_5224_, lean_object* v_data_5225_){
_start:
{
lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; uint8_t v___x_5230_; 
v___x_5227_ = lean_unsigned_to_nat(0u);
v___x_5228_ = lean_array_get_size(v_data_5225_);
v___x_5229_ = lean_box(0);
v___x_5230_ = lean_nat_dec_lt(v___x_5227_, v___x_5228_);
if (v___x_5230_ == 0)
{
lean_object* v___x_5231_; 
lean_dec_ref(v_data_5225_);
lean_dec_ref(v_socket_5224_);
lean_dec_ref(v___x_5223_);
lean_dec_ref(v___f_5222_);
v___x_5231_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5231_;
}
else
{
lean_object* v___f_5232_; uint8_t v___x_5233_; 
v___f_5232_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5232_, 0, v___f_5222_);
lean_closure_set(v___f_5232_, 1, v_socket_5224_);
v___x_5233_ = lean_nat_dec_le(v___x_5228_, v___x_5228_);
if (v___x_5233_ == 0)
{
if (v___x_5230_ == 0)
{
lean_object* v___x_5234_; 
lean_dec_ref(v___f_5232_);
lean_dec_ref(v_data_5225_);
lean_dec_ref(v___x_5223_);
v___x_5234_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5234_;
}
else
{
size_t v___x_5235_; size_t v___x_5236_; lean_object* v___x_857__overap_5237_; lean_object* v___x_5238_; 
v___x_5235_ = ((size_t)0ULL);
v___x_5236_ = lean_usize_of_nat(v___x_5228_);
v___x_857__overap_5237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5223_, v___f_5232_, v_data_5225_, v___x_5235_, v___x_5236_, v___x_5229_);
v___x_5238_ = lean_apply_1(v___x_857__overap_5237_, lean_box(0));
return v___x_5238_;
}
}
else
{
size_t v___x_5239_; size_t v___x_5240_; lean_object* v___x_860__overap_5241_; lean_object* v___x_5242_; 
v___x_5239_ = ((size_t)0ULL);
v___x_5240_ = lean_usize_of_nat(v___x_5228_);
v___x_860__overap_5241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5223_, v___f_5232_, v_data_5225_, v___x_5239_, v___x_5240_, v___x_5229_);
v___x_5242_ = lean_apply_1(v___x_860__overap_5241_, lean_box(0));
return v___x_5242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed(lean_object* v___f_5243_, lean_object* v___x_5244_, lean_object* v_socket_5245_, lean_object* v_data_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v_res_5248_; 
v_res_5248_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(v___f_5243_, v___x_5244_, v_socket_5245_, v_data_5246_);
return v_res_5248_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_5256_; 
v___x_5256_ = l_Std_Internal_IO_Async_EAsync_instMonad(lean_box(0));
return v___x_5256_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___x_5257_; lean_object* v___f_5258_; lean_object* v___f_5259_; 
v___x_5257_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4);
v___f_5258_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___f_5259_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed), 5, 2);
lean_closure_set(v___f_5259_, 0, v___f_5258_);
lean_closure_set(v___f_5259_, 1, v___x_5257_);
return v___f_5259_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6(void){
_start:
{
lean_object* v___f_5260_; lean_object* v___f_5261_; lean_object* v___f_5262_; lean_object* v___x_5263_; 
v___f_5260_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3));
v___f_5261_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5);
v___f_5262_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___x_5263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5263_, 0, v___f_5262_);
lean_ctor_set(v___x_5263_, 1, v___f_5261_);
lean_ctor_set(v___x_5263_, 2, v___f_5260_);
return v___x_5263_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5264_, lean_object* v_inst_5265_){
_start:
{
lean_object* v___x_5266_; 
v___x_5266_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6);
return v___x_5266_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5267_, lean_object* v_inst_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5267_, v_inst_5268_);
lean_dec(v_inst_5268_);
return v_res_5269_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5271_){
_start:
{
lean_object* v___x_5273_; 
v___x_5273_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5271_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5274_, lean_object* v_a_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5274_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5277_, lean_object* v_capacity_5278_, lean_object* v_h_5279_){
_start:
{
lean_object* v___x_5281_; 
v___x_5281_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5278_);
return v___x_5281_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5282_, lean_object* v_capacity_5283_, lean_object* v_h_5284_, lean_object* v_a_5285_){
_start:
{
lean_object* v_res_5286_; 
v_res_5286_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5282_, v_capacity_5283_, v_h_5284_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5287_, lean_object* v_v_5288_){
_start:
{
lean_object* v___x_5290_; 
v___x_5290_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5287_, v_v_5288_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5291_, lean_object* v_v_5292_, lean_object* v_a_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5291_, v_v_5292_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5295_, lean_object* v_ch_5296_, lean_object* v_v_5297_){
_start:
{
lean_object* v___x_5299_; 
v___x_5299_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5296_, v_v_5297_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5300_, lean_object* v_ch_5301_, lean_object* v_v_5302_, lean_object* v_a_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5300_, v_ch_5301_, v_v_5302_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5306_, lean_object* v_v_5307_){
_start:
{
lean_object* v___x_5309_; lean_object* v___f_5310_; lean_object* v___x_5311_; uint8_t v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
v___x_5309_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5306_, v_v_5307_);
v___f_5310_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5311_ = lean_unsigned_to_nat(0u);
v___x_5312_ = 1;
v___x_5313_ = lean_io_bind_task(v___x_5309_, v___f_5310_, v___x_5311_, v___x_5312_);
v___x_5314_ = lean_io_wait(v___x_5313_);
v___x_5315_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5316_ = l_IO_ofExcept___redArg(v___x_5315_, v___x_5314_);
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5317_, lean_object* v_v_5318_, lean_object* v_a_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5317_, v_v_5318_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5321_, lean_object* v_ch_5322_, lean_object* v_v_5323_){
_start:
{
lean_object* v___x_5325_; lean_object* v___f_5326_; lean_object* v___x_5327_; uint8_t v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; 
v___x_5325_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5322_, v_v_5323_);
v___f_5326_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5327_ = lean_unsigned_to_nat(0u);
v___x_5328_ = 1;
v___x_5329_ = lean_io_bind_task(v___x_5325_, v___f_5326_, v___x_5327_, v___x_5328_);
v___x_5330_ = lean_io_wait(v___x_5329_);
v___x_5331_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5332_ = l_IO_ofExcept___redArg(v___x_5331_, v___x_5330_);
return v___x_5332_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5333_, lean_object* v_ch_5334_, lean_object* v_v_5335_, lean_object* v_a_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5333_, v_ch_5334_, v_v_5335_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5338_){
_start:
{
lean_object* v___x_5340_; 
v___x_5340_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5338_);
return v___x_5340_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5341_, lean_object* v_a_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5341_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5344_, lean_object* v_ch_5345_){
_start:
{
lean_object* v___x_5347_; 
v___x_5347_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5345_);
return v___x_5347_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5348_, lean_object* v_ch_5349_, lean_object* v_a_5350_){
_start:
{
lean_object* v_res_5351_; 
v_res_5351_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5348_, v_ch_5349_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5352_){
_start:
{
lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5354_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5352_);
v___x_5355_ = lean_io_wait(v___x_5354_);
return v___x_5355_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5356_, lean_object* v_a_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5356_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5359_, lean_object* v_inst_5360_, lean_object* v_ch_5361_){
_start:
{
lean_object* v___x_5363_; 
v___x_5363_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5361_);
return v___x_5363_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5364_, lean_object* v_inst_5365_, lean_object* v_ch_5366_, lean_object* v_a_5367_){
_start:
{
lean_object* v_res_5368_; 
v_res_5368_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5364_, v_inst_5365_, v_ch_5366_);
lean_dec(v_inst_5365_);
return v_res_5368_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5369_, lean_object* v_b_5370_, lean_object* v_f_5371_, lean_object* v_toBind_5372_, lean_object* v___f_5373_, lean_object* v_a_5374_){
_start:
{
if (lean_obj_tag(v_a_5374_) == 0)
{
lean_object* v___x_5375_; 
lean_dec(v___f_5373_);
lean_dec(v_toBind_5372_);
lean_dec(v_f_5371_);
v___x_5375_ = lean_apply_2(v_toPure_5369_, lean_box(0), v_b_5370_);
return v___x_5375_;
}
else
{
lean_object* v_val_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; 
lean_dec(v_toPure_5369_);
v_val_5376_ = lean_ctor_get(v_a_5374_, 0);
lean_inc(v_val_5376_);
lean_dec_ref(v_a_5374_);
v___x_5377_ = lean_apply_2(v_f_5371_, v_val_5376_, v_b_5370_);
v___x_5378_ = lean_apply_4(v_toBind_5372_, lean_box(0), lean_box(0), v___x_5377_, v___f_5373_);
return v___x_5378_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5379_, lean_object* v_inst_5380_, lean_object* v_inst_5381_, lean_object* v_ch_5382_, lean_object* v_f_5383_, lean_object* v_b_5384_){
_start:
{
lean_object* v_toApplicative_5385_; lean_object* v_toBind_5386_; lean_object* v_toPure_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___f_5390_; lean_object* v___f_5391_; lean_object* v___x_5392_; 
v_toApplicative_5385_ = lean_ctor_get(v_inst_5380_, 0);
v_toBind_5386_ = lean_ctor_get(v_inst_5380_, 1);
lean_inc(v_toBind_5386_);
v_toPure_5387_ = lean_ctor_get(v_toApplicative_5385_, 1);
lean_inc(v_toPure_5387_);
lean_inc_ref(v_ch_5382_);
lean_inc(v_inst_5379_);
v___x_5388_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5388_, 0, lean_box(0));
lean_closure_set(v___x_5388_, 1, v_inst_5379_);
lean_closure_set(v___x_5388_, 2, v_ch_5382_);
lean_inc(v_inst_5381_);
v___x_5389_ = lean_apply_2(v_inst_5381_, lean_box(0), v___x_5388_);
lean_inc(v_f_5383_);
lean_inc(v_toPure_5387_);
v___f_5390_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5390_, 0, v_toPure_5387_);
lean_closure_set(v___f_5390_, 1, v_inst_5379_);
lean_closure_set(v___f_5390_, 2, v_inst_5380_);
lean_closure_set(v___f_5390_, 3, v_inst_5381_);
lean_closure_set(v___f_5390_, 4, v_ch_5382_);
lean_closure_set(v___f_5390_, 5, v_f_5383_);
lean_inc(v_toBind_5386_);
v___f_5391_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5391_, 0, v_toPure_5387_);
lean_closure_set(v___f_5391_, 1, v_b_5384_);
lean_closure_set(v___f_5391_, 2, v_f_5383_);
lean_closure_set(v___f_5391_, 3, v_toBind_5386_);
lean_closure_set(v___f_5391_, 4, v___f_5390_);
v___x_5392_ = lean_apply_4(v_toBind_5386_, lean_box(0), lean_box(0), v___x_5389_, v___f_5391_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5393_, lean_object* v_inst_5394_, lean_object* v_inst_5395_, lean_object* v_inst_5396_, lean_object* v_ch_5397_, lean_object* v_f_5398_, lean_object* v_____do__lift_5399_){
_start:
{
if (lean_obj_tag(v_____do__lift_5399_) == 0)
{
lean_object* v_a_5400_; lean_object* v___x_5401_; 
lean_dec(v_f_5398_);
lean_dec_ref(v_ch_5397_);
lean_dec(v_inst_5396_);
lean_dec_ref(v_inst_5395_);
lean_dec(v_inst_5394_);
v_a_5400_ = lean_ctor_get(v_____do__lift_5399_, 0);
lean_inc(v_a_5400_);
lean_dec_ref(v_____do__lift_5399_);
v___x_5401_ = lean_apply_2(v_toPure_5393_, lean_box(0), v_a_5400_);
return v___x_5401_;
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5403_; 
lean_dec(v_toPure_5393_);
v_a_5402_ = lean_ctor_get(v_____do__lift_5399_, 0);
lean_inc(v_a_5402_);
lean_dec_ref(v_____do__lift_5399_);
v___x_5403_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5394_, v_inst_5395_, v_inst_5396_, v_ch_5397_, v_f_5398_, v_a_5402_);
return v___x_5403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5404_, lean_object* v_m_5405_, lean_object* v_00_u03b2_5406_, lean_object* v_inst_5407_, lean_object* v_inst_5408_, lean_object* v_inst_5409_, lean_object* v_ch_5410_, lean_object* v_f_5411_, lean_object* v_b_5412_){
_start:
{
lean_object* v___x_5413_; 
v___x_5413_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5407_, v_inst_5408_, v_inst_5409_, v_ch_5410_, v_f_5411_, v_b_5412_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5414_, lean_object* v_inst_5415_, lean_object* v_inst_5416_, lean_object* v_00_u03b2_5417_, lean_object* v_ch_5418_, lean_object* v_b_5419_, lean_object* v_f_5420_){
_start:
{
lean_object* v___x_5421_; 
v___x_5421_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5414_, v_inst_5415_, v_inst_5416_, v_ch_5418_, v_f_5420_, v_b_5419_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5422_, lean_object* v_inst_5423_, lean_object* v_inst_5424_){
_start:
{
lean_object* v___f_5425_; 
v___f_5425_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5425_, 0, v_inst_5422_);
lean_closure_set(v___f_5425_, 1, v_inst_5423_);
lean_closure_set(v___f_5425_, 2, v_inst_5424_);
return v___f_5425_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5426_, lean_object* v_m_5427_, lean_object* v_inst_5428_, lean_object* v_inst_5429_, lean_object* v_inst_5430_){
_start:
{
lean_object* v___f_5431_; 
v___f_5431_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5431_, 0, v_inst_5428_);
lean_closure_set(v___f_5431_, 1, v_inst_5429_);
lean_closure_set(v___f_5431_, 2, v_inst_5430_);
return v___f_5431_;
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

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
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0_value)}};
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
lean_dec_ref_known(v_receivers_1093_, 5);
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
lean_dec_ref_known(v_receivers_1181_, 5);
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
lean_dec_ref_known(v_receivers_1224_, 5);
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
uint8_t v___x_1417__boxed_1362_; size_t v_sz_boxed_1363_; size_t v_i_boxed_1364_; lean_object* v_res_1365_; 
v___x_1417__boxed_1362_ = lean_unbox(v___x_1356_);
v_sz_boxed_1363_ = lean_unbox_usize(v_sz_1358_);
lean_dec(v_sz_1358_);
v_i_boxed_1364_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1417__boxed_1362_, v_as_1357_, v_sz_boxed_1363_, v_i_boxed_1364_, v_b_1360_);
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
uint8_t v___x_1513__boxed_1442_; size_t v_sz_boxed_1443_; size_t v_i_boxed_1444_; lean_object* v_res_1445_; 
v___x_1513__boxed_1442_ = lean_unbox(v___x_1435_);
v_sz_boxed_1443_ = lean_unbox_usize(v_sz_1437_);
lean_dec(v_sz_1437_);
v_i_boxed_1444_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_res_1445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1434_, v___x_1513__boxed_1442_, v_as_1436_, v_sz_boxed_1443_, v_i_boxed_1444_, v_b_1439_, v___y_1440_);
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
lean_dec_ref_known(v___x_1613_, 1);
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
uint8_t v___x_1069__boxed_1636_; lean_object* v_res_1637_; 
v___x_1069__boxed_1636_ = lean_unbox(v___x_1633_);
v_res_1637_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1628_, v_inst_1629_, v_toBind_1630_, v_a_1631_, v_a_1632_, v___x_1069__boxed_1636_, v_inst_1634_, v_a_1635_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___x_1732_; lean_object* v_capacity_1733_; lean_object* v_buffer_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1732_ = lean_st_ref_get(v_a_1730_);
v_capacity_1733_ = lean_ctor_get(v___x_1732_, 2);
lean_inc(v_capacity_1733_);
v_buffer_1734_ = lean_ctor_get(v___x_1732_, 4);
lean_inc_ref(v_buffer_1734_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_nat_mod(v_place_1729_, v_capacity_1733_);
lean_dec(v_capacity_1733_);
v___x_1736_ = lean_array_fget(v_buffer_1734_, v___x_1735_);
lean_dec(v___x_1735_);
lean_dec_ref(v_buffer_1734_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_1738_, lean_object* v_a_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_1738_, v_a_1739_);
lean_dec(v_a_1739_);
lean_dec(v_place_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v_size_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1744_ = lean_st_ref_get(v_a_1742_);
v_size_1745_ = lean_ctor_get(v___x_1744_, 3);
lean_inc(v_size_1745_);
lean_dec(v___x_1744_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_nat_dec_eq(v_size_1745_, v___x_1746_);
lean_dec(v_size_1745_);
v___x_1748_ = lean_box(v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1750_);
lean_dec(v_a_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_1753_, lean_object* v_next_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v_fst_1758_; lean_object* v_snd_1759_; lean_object* v_value_1762_; lean_object* v_pos_1763_; lean_object* v_remaining_1764_; uint8_t v___x_1765_; 
v___x_1756_ = lean_st_ref_take(v_slot_1753_);
v_value_1762_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_value_1762_);
v_pos_1763_ = lean_ctor_get(v___x_1756_, 1);
lean_inc(v_pos_1763_);
v_remaining_1764_ = lean_ctor_get(v___x_1756_, 2);
lean_inc(v_remaining_1764_);
v___x_1765_ = lean_nat_dec_eq(v_next_1754_, v_pos_1763_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v_remaining_1764_);
lean_dec(v_pos_1763_);
lean_dec(v_value_1762_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_box(v___x_1765_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v_fst_1758_ = v___x_1768_;
v_snd_1759_ = v___x_1756_;
goto v___jp_1757_;
}
else
{
lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1787_; 
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; lean_object* v_unused_1789_; lean_object* v_unused_1790_; 
v_unused_1788_ = lean_ctor_get(v___x_1756_, 2);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v___x_1756_, 1);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v___x_1756_, 0);
lean_dec(v_unused_1790_);
v___x_1770_ = v___x_1756_;
v_isShared_1771_ = v_isSharedCheck_1787_;
goto v_resetjp_1769_;
}
else
{
lean_dec(v___x_1756_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1787_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_nat_dec_eq(v_remaining_1764_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1774_ = lean_box(v___x_1773_);
lean_inc(v_value_1762_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_value_1762_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_nat_sub(v_remaining_1764_, v___x_1772_);
lean_dec(v_remaining_1764_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 2, v___x_1776_);
v___x_1778_ = v___x_1770_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_value_1762_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_pos_1763_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
v_fst_1758_ = v___x_1775_;
v_snd_1759_ = v___x_1778_;
goto v___jp_1757_;
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
lean_dec(v_remaining_1764_);
v___x_1780_ = lean_box(v___x_1765_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_value_1762_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_unsigned_to_nat(0u);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 2, v___x_1783_);
lean_ctor_set(v___x_1770_, 0, v___x_1782_);
v___x_1785_ = v___x_1770_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_pos_1763_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v_fst_1758_ = v___x_1781_;
v_snd_1759_ = v___x_1785_;
goto v___jp_1757_;
}
}
}
}
v___jp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_st_ref_set(v_slot_1753_, v_snd_1759_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_fst_1758_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_1791_, lean_object* v_next_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_1791_, v_next_1792_);
lean_dec(v_next_1792_);
lean_dec(v_slot_1791_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1871_; 
v___x_1798_ = lean_st_ref_get(v_a_1796_);
v___x_1799_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1796_);
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1871_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1871_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_unbox(v_a_1800_);
lean_dec(v_a_1800_);
if (v___x_1804_ == 0)
{
lean_object* v_capacity_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1866_; 
lean_del_object(v___x_1802_);
v_capacity_1805_ = lean_ctor_get(v___x_1798_, 2);
lean_inc(v_capacity_1805_);
v___x_1806_ = lean_nat_mod(v_next_1795_, v_capacity_1805_);
lean_dec(v_capacity_1805_);
v___x_1807_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_1806_, v_a_1796_);
lean_dec(v___x_1806_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1866_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1866_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1865_; 
v___x_1812_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_1808_, v_next_1795_);
lean_dec(v_a_1808_);
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1865_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1865_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_fst_1817_; lean_object* v_snd_1818_; lean_object* v_st_1820_; lean_object* v___y_1821_; 
v_fst_1817_ = lean_ctor_get(v_a_1813_, 0);
lean_inc(v_fst_1817_);
v_snd_1818_ = lean_ctor_get(v_a_1813_, 1);
lean_inc(v_snd_1818_);
lean_dec(v_a_1813_);
if (lean_obj_tag(v_fst_1817_) == 1)
{
uint8_t v___x_1826_; 
lean_del_object(v___x_1810_);
v___x_1826_ = lean_unbox(v_snd_1818_);
if (v___x_1826_ == 0)
{
lean_dec(v_snd_1818_);
v_st_1820_ = v___x_1798_;
v___y_1821_ = v_a_1796_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1827_; lean_object* v_producers_1828_; lean_object* v_waiters_1829_; lean_object* v_capacity_1830_; lean_object* v_size_1831_; lean_object* v_buffer_1832_; lean_object* v_write_1833_; lean_object* v_read_1834_; lean_object* v_receivers_1835_; lean_object* v_nextId_1836_; uint8_t v_closed_1837_; lean_object* v_pos_1838_; lean_object* v___x_1839_; 
v___x_1827_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_1798_);
v_producers_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc_ref(v_producers_1828_);
v_waiters_1829_ = lean_ctor_get(v___x_1827_, 1);
lean_inc_ref(v_waiters_1829_);
v_capacity_1830_ = lean_ctor_get(v___x_1827_, 2);
lean_inc(v_capacity_1830_);
v_size_1831_ = lean_ctor_get(v___x_1827_, 3);
lean_inc(v_size_1831_);
v_buffer_1832_ = lean_ctor_get(v___x_1827_, 4);
lean_inc_ref(v_buffer_1832_);
v_write_1833_ = lean_ctor_get(v___x_1827_, 5);
lean_inc(v_write_1833_);
v_read_1834_ = lean_ctor_get(v___x_1827_, 6);
lean_inc(v_read_1834_);
v_receivers_1835_ = lean_ctor_get(v___x_1827_, 7);
lean_inc(v_receivers_1835_);
v_nextId_1836_ = lean_ctor_get(v___x_1827_, 8);
lean_inc(v_nextId_1836_);
v_closed_1837_ = lean_ctor_get_uint8(v___x_1827_, sizeof(void*)*10);
v_pos_1838_ = lean_ctor_get(v___x_1827_, 9);
lean_inc(v_pos_1838_);
v___x_1839_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1828_);
if (lean_obj_tag(v___x_1839_) == 1)
{
lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1850_; 
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1851_ = lean_ctor_get(v___x_1827_, 9);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v___x_1827_, 8);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v___x_1827_, 7);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v___x_1827_, 6);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v___x_1827_, 5);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v___x_1827_, 4);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v___x_1827_, 3);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v___x_1827_, 2);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v___x_1827_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v___x_1827_, 0);
lean_dec(v_unused_1860_);
v___x_1841_ = v___x_1827_;
v_isShared_1842_ = v_isSharedCheck_1850_;
goto v_resetjp_1840_;
}
else
{
lean_dec(v___x_1827_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1850_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_val_1843_; lean_object* v_fst_1844_; lean_object* v_snd_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v_val_1843_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_val_1843_);
lean_dec_ref_known(v___x_1839_, 1);
v_fst_1844_ = lean_ctor_get(v_val_1843_, 0);
lean_inc(v_fst_1844_);
v_snd_1845_ = lean_ctor_get(v_val_1843_, 1);
lean_inc(v_snd_1845_);
lean_dec(v_val_1843_);
v___x_1846_ = lean_io_promise_resolve(v_snd_1818_, v_fst_1844_);
lean_dec(v_fst_1844_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v_snd_1845_);
v___x_1848_ = v___x_1841_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_snd_1845_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_waiters_1829_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_capacity_1830_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v_size_1831_);
lean_ctor_set(v_reuseFailAlloc_1849_, 4, v_buffer_1832_);
lean_ctor_set(v_reuseFailAlloc_1849_, 5, v_write_1833_);
lean_ctor_set(v_reuseFailAlloc_1849_, 6, v_read_1834_);
lean_ctor_set(v_reuseFailAlloc_1849_, 7, v_receivers_1835_);
lean_ctor_set(v_reuseFailAlloc_1849_, 8, v_nextId_1836_);
lean_ctor_set(v_reuseFailAlloc_1849_, 9, v_pos_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1849_, sizeof(void*)*10, v_closed_1837_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
v_st_1820_ = v___x_1848_;
v___y_1821_ = v_a_1796_;
goto v___jp_1819_;
}
}
}
else
{
lean_dec(v___x_1839_);
lean_dec(v_pos_1838_);
lean_dec(v_nextId_1836_);
lean_dec(v_receivers_1835_);
lean_dec(v_read_1834_);
lean_dec(v_write_1833_);
lean_dec_ref(v_buffer_1832_);
lean_dec(v_size_1831_);
lean_dec(v_capacity_1830_);
lean_dec_ref(v_waiters_1829_);
lean_dec(v_snd_1818_);
v_st_1820_ = v___x_1827_;
v___y_1821_ = v_a_1796_;
goto v___jp_1819_;
}
}
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_dec(v_snd_1818_);
lean_dec(v_fst_1817_);
lean_del_object(v___x_1815_);
lean_dec(v___x_1798_);
v___x_1861_ = lean_box(0);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1861_);
v___x_1863_ = v___x_1810_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
v___jp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_st_ref_set(v___y_1821_, v_st_1820_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v_fst_1817_);
v___x_1824_ = v___x_1815_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_fst_1817_);
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
lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_dec(v___x_1798_);
v___x_1867_ = lean_box(0);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1867_);
v___x_1869_ = v___x_1802_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_1872_, lean_object* v_a_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_1872_, v_a_1873_);
lean_dec(v_a_1873_);
lean_dec(v_next_1872_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_a_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_fst_1879_; lean_object* v_snd_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1917_; 
v_fst_1879_ = lean_ctor_get(v_a_1876_, 0);
v_snd_1880_ = lean_ctor_get(v_a_1876_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_a_1876_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1882_ = v_a_1876_;
v_isShared_1883_ = v_isSharedCheck_1917_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_snd_1880_);
lean_inc(v_fst_1879_);
lean_dec(v_a_1876_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1917_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_size_1889_; lean_object* v_pos_1890_; uint8_t v___x_1891_; 
v_size_1889_ = lean_ctor_get(v_fst_1879_, 3);
v_pos_1890_ = lean_ctor_get(v_fst_1879_, 9);
v___x_1891_ = lean_nat_dec_lt(v_snd_1880_, v_pos_1890_);
if (v___x_1891_ == 0)
{
goto v___jp_1884_;
}
else
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = lean_nat_dec_lt(v___x_1892_, v_size_1889_);
if (v___x_1893_ == 0)
{
goto v___jp_1884_;
}
else
{
lean_object* v___x_1894_; 
lean_del_object(v___x_1882_);
v___x_1894_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_1880_, v___y_1877_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1908_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1908_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1908_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
if (lean_obj_tag(v_a_1895_) == 1)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec_ref_known(v_a_1895_, 1);
lean_del_object(v___x_1897_);
lean_dec(v_fst_1879_);
v___x_1899_ = lean_st_ref_get(v___y_1877_);
v___x_1900_ = lean_unsigned_to_nat(1u);
v___x_1901_ = lean_nat_add(v_snd_1880_, v___x_1900_);
lean_dec(v_snd_1880_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1899_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v_a_1876_ = v___x_1902_;
goto _start;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec(v_a_1895_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_fst_1879_);
lean_ctor_set(v___x_1904_, 1, v_snd_1880_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1904_);
v___x_1906_ = v___x_1897_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_snd_1880_);
lean_dec(v_fst_1879_);
v_a_1909_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1894_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1894_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
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
}
v___jp_1884_:
{
lean_object* v___x_1886_; 
if (v_isShared_1883_ == 0)
{
v___x_1886_ = v___x_1882_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_fst_1879_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_snd_1880_);
v___x_1886_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; 
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
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
v___x_2302_ = lean_nat_add(v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec(v___y_2300_);
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
lean_ctor_set(v___x_2306_, 3, v___y_2299_);
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
lean_ctor_set(v_reuseFailAlloc_2310_, 3, v___y_2299_);
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
v___y_2299_ = v___x_2323_;
v___y_2300_ = v___x_2324_;
v___y_2301_ = v_size_2325_;
goto v___jp_2298_;
}
else
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v___y_2299_ = v___x_2323_;
v___y_2300_ = v___x_2324_;
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
v___x_2460_ = lean_nat_add(v___y_2457_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec(v___y_2457_);
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
lean_ctor_set(v___x_2440_, 3, v___y_2458_);
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
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v___y_2458_);
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
v___y_2457_ = v___x_2472_;
v___y_2458_ = v___x_2471_;
v___y_2459_ = v_size_2473_;
goto v___jp_2456_;
}
else
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_unsigned_to_nat(0u);
v___y_2457_ = v___x_2472_;
v___y_2458_ = v___x_2471_;
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
v___x_2950_ = lean_st_ref_set(v_slot_2943_, v_snd_2949_);
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
v___x_3020_ = lean_st_ref_set(v___y_3019_, v_st_3018_);
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
v___x_3087_ = lean_st_ref_set(v_a_3063_, v___x_3086_);
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
v___x_3222_ = lean_st_ref_set(v___y_3191_, v___x_3221_);
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
v___x_3425_ = lean_st_ref_set(v_finished_3418_, v___x_3424_);
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
v___x_3476_ = lean_st_ref_set(v_a_3448_, v___x_3475_);
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
v___x_3506_ = lean_st_ref_set(v_finished_3499_, v___x_3505_);
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
lean_object* v___x_3599_; lean_object* v_producers_3600_; lean_object* v_waiters_3601_; lean_object* v_capacity_3602_; lean_object* v_size_3603_; lean_object* v_buffer_3604_; lean_object* v_write_3605_; lean_object* v_read_3606_; lean_object* v_receivers_3607_; lean_object* v_nextId_3608_; uint8_t v_closed_3609_; lean_object* v_pos_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3632_; 
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
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3612_ = v___x_3599_;
v_isShared_3613_ = v_isSharedCheck_3632_;
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
v_isShared_3613_ = v_isSharedCheck_3632_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3601_);
if (lean_obj_tag(v___x_3614_) == 1)
{
lean_object* v_val_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3629_; 
v_val_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3629_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_val_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3629_;
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
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_producers_3600_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_snd_3620_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v_capacity_3602_);
lean_ctor_set(v_reuseFailAlloc_3628_, 3, v_size_3603_);
lean_ctor_set(v_reuseFailAlloc_3628_, 4, v_buffer_3604_);
lean_ctor_set(v_reuseFailAlloc_3628_, 5, v_write_3605_);
lean_ctor_set(v_reuseFailAlloc_3628_, 6, v_read_3606_);
lean_ctor_set(v_reuseFailAlloc_3628_, 7, v_receivers_3607_);
lean_ctor_set(v_reuseFailAlloc_3628_, 8, v_nextId_3608_);
lean_ctor_set(v_reuseFailAlloc_3628_, 9, v_pos_3610_);
lean_ctor_set_uint8(v_reuseFailAlloc_3628_, sizeof(void*)*10, v_closed_3609_);
v___x_3623_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3624_; lean_object* v___x_3626_; 
v___x_3624_ = lean_st_ref_set(v___y_3597_, v___x_3623_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3624_);
v___x_3626_ = v___x_3617_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
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
v___x_3630_ = lean_box(0);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
uint8_t v_____do__lift_4156__boxed_3636_; lean_object* v_res_3637_; 
v_____do__lift_4156__boxed_3636_ = lean_unbox(v_____do__lift_3633_);
v_res_3637_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_4156__boxed_3636_, v___y_3634_);
lean_dec(v___y_3634_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3638_, lean_object* v___f_3639_, lean_object* v_id_3640_, uint8_t v_____do__lift_3641_, lean_object* v___y_3642_){
_start:
{
if (v_____do__lift_3641_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v_producers_3646_; lean_object* v_waiters_3647_; lean_object* v_capacity_3648_; lean_object* v_size_3649_; lean_object* v_buffer_3650_; lean_object* v_write_3651_; lean_object* v_read_3652_; lean_object* v_receivers_3653_; lean_object* v_nextId_3654_; uint8_t v_closed_3655_; lean_object* v_pos_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v_id_3640_);
v___x_3644_ = lean_io_promise_new();
v___x_3645_ = lean_st_ref_take(v___y_3642_);
v_producers_3646_ = lean_ctor_get(v___x_3645_, 0);
v_waiters_3647_ = lean_ctor_get(v___x_3645_, 1);
v_capacity_3648_ = lean_ctor_get(v___x_3645_, 2);
v_size_3649_ = lean_ctor_get(v___x_3645_, 3);
v_buffer_3650_ = lean_ctor_get(v___x_3645_, 4);
v_write_3651_ = lean_ctor_get(v___x_3645_, 5);
v_read_3652_ = lean_ctor_get(v___x_3645_, 6);
v_receivers_3653_ = lean_ctor_get(v___x_3645_, 7);
v_nextId_3654_ = lean_ctor_get(v___x_3645_, 8);
v_closed_3655_ = lean_ctor_get_uint8(v___x_3645_, sizeof(void*)*10);
v_pos_3656_ = lean_ctor_get(v___x_3645_, 9);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3658_ = v___x_3645_;
v_isShared_3659_ = v_isSharedCheck_3670_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_pos_3656_);
lean_inc(v_nextId_3654_);
lean_inc(v_receivers_3653_);
lean_inc(v_read_3652_);
lean_inc(v_write_3651_);
lean_inc(v_buffer_3650_);
lean_inc(v_size_3649_);
lean_inc(v_capacity_3648_);
lean_inc(v_waiters_3647_);
lean_inc(v_producers_3646_);
lean_dec(v___x_3645_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3670_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3664_; 
v___x_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3660_, 0, v_waiter_3638_);
lean_inc(v___x_3644_);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3644_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = l_Std_Queue_enqueue___redArg(v___x_3661_, v_waiters_3647_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 1, v___x_3662_);
v___x_3664_ = v___x_3658_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_producers_3646_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_capacity_3648_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_size_3649_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v_buffer_3650_);
lean_ctor_set(v_reuseFailAlloc_3669_, 5, v_write_3651_);
lean_ctor_set(v_reuseFailAlloc_3669_, 6, v_read_3652_);
lean_ctor_set(v_reuseFailAlloc_3669_, 7, v_receivers_3653_);
lean_ctor_set(v_reuseFailAlloc_3669_, 8, v_nextId_3654_);
lean_ctor_set(v_reuseFailAlloc_3669_, 9, v_pos_3656_);
lean_ctor_set_uint8(v_reuseFailAlloc_3669_, sizeof(void*)*10, v_closed_3655_);
v___x_3664_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3665_ = lean_st_ref_set(v___y_3642_, v___x_3664_);
v___x_3666_ = lean_io_promise_result_opt(v___x_3644_);
lean_dec(v___x_3644_);
v___x_3667_ = lean_unsigned_to_nat(0u);
v___x_3668_ = l_EIO_chainTask___redArg(v___x_3666_, v___f_3639_, v___x_3667_, v_____do__lift_3641_);
return v___x_3668_;
}
}
}
else
{
lean_object* v___x_3671_; lean_object* v_lose_3672_; lean_object* v___x_3673_; 
lean_dec_ref(v___f_3639_);
v___x_3671_ = lean_box(v_____do__lift_3641_);
v_lose_3672_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3672_, 0, v___x_3671_);
v___x_3673_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3640_, v_waiter_3638_, v_lose_3672_, v___y_3642_);
lean_dec_ref(v_waiter_3638_);
return v___x_3673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3674_, lean_object* v___f_3675_, lean_object* v_id_3676_, lean_object* v_____do__lift_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
uint8_t v_____do__lift_4212__boxed_3680_; lean_object* v_res_3681_; 
v_____do__lift_4212__boxed_3680_ = lean_unbox(v_____do__lift_3677_);
v_res_3681_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3674_, v___f_3675_, v_id_3676_, v_____do__lift_4212__boxed_3680_, v___y_3678_);
lean_dec(v___y_3678_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3684_, lean_object* v_ch_3685_, lean_object* v_res_x3f_3686_){
_start:
{
if (lean_obj_tag(v_res_x3f_3686_) == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_dec_ref(v_ch_3685_);
lean_dec_ref(v_waiter_3684_);
v___x_3688_ = lean_box(0);
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
else
{
lean_object* v_val_3690_; uint8_t v___x_3691_; 
v_val_3690_ = lean_ctor_get(v_res_x3f_3686_, 0);
v___x_3691_ = lean_unbox(v_val_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___f_3692_; lean_object* v___x_3693_; 
lean_dec_ref(v_ch_3685_);
v___f_3692_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3693_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3684_, v___f_3692_);
lean_dec_ref(v_waiter_3684_);
return v___x_3693_;
}
else
{
lean_object* v___x_3694_; 
v___x_3694_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3685_, v_waiter_3684_);
return v___x_3694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3695_, lean_object* v_ch_3696_, lean_object* v_res_x3f_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3695_, v_ch_3696_, v_res_x3f_3697_);
lean_dec(v_res_x3f_3697_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3700_, lean_object* v_waiter_3701_){
_start:
{
lean_object* v_state_3703_; lean_object* v_id_3704_; lean_object* v___f_3705_; lean_object* v___f_3706_; lean_object* v___f_3707_; lean_object* v___x_3708_; 
v_state_3703_ = lean_ctor_get(v_ch_3700_, 0);
lean_inc_ref(v_state_3703_);
v_id_3704_ = lean_ctor_get(v_ch_3700_, 1);
lean_inc_n(v_id_3704_, 2);
lean_inc_ref(v_waiter_3701_);
v___f_3705_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3705_, 0, v_waiter_3701_);
lean_closure_set(v___f_3705_, 1, v_ch_3700_);
v___f_3706_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3706_, 0, v_waiter_3701_);
lean_closure_set(v___f_3706_, 1, v___f_3705_);
lean_closure_set(v___f_3706_, 2, v_id_3704_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3707_, 0, v_id_3704_);
lean_closure_set(v___f_3707_, 1, v___f_3706_);
v___x_3708_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3703_, v___f_3707_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3709_, lean_object* v_waiter_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3709_, v_waiter_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3713_, lean_object* v_ch_3714_, lean_object* v_waiter_3715_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3714_, v_waiter_3715_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3718_, lean_object* v_ch_3719_, lean_object* v_waiter_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3718_, v_ch_3719_, v_waiter_3720_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3723_, lean_object* v_receiverId_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3724_, v_a_3725_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3728_, lean_object* v_receiverId_3729_, lean_object* v_a_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3728_, v_receiverId_3729_, v_a_3730_);
lean_dec(v_a_3730_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3733_, lean_object* v_x_3734_){
_start:
{
if (lean_obj_tag(v_x_3734_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3744_; 
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
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3757_; 
v_a_3745_ = lean_ctor_get(v_x_3734_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_x_3734_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3747_ = v_x_3734_;
v_isShared_3748_ = v_isSharedCheck_3757_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v_x_3734_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3757_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v_capacity_3749_; lean_object* v_buffer_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v_capacity_3749_ = lean_ctor_get(v_a_3745_, 2);
lean_inc(v_capacity_3749_);
v_buffer_3750_ = lean_ctor_get(v_a_3745_, 4);
lean_inc_ref(v_buffer_3750_);
lean_dec(v_a_3745_);
v___x_3751_ = lean_nat_mod(v_place_3733_, v_capacity_3749_);
lean_dec(v_capacity_3749_);
v___x_3752_ = lean_array_fget(v_buffer_3750_, v___x_3751_);
lean_dec(v___x_3751_);
lean_dec_ref(v_buffer_3750_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3752_);
v___x_3754_ = v___x_3747_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
return v___x_3755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3758_, lean_object* v_x_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3758_, v_x_3759_);
lean_dec(v_place_3758_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v___x_3765_; lean_object* v___f_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; lean_object* v___x_3771_; 
v___x_3765_ = lean_st_ref_get(v_a_3763_);
v___f_3766_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3766_, 0, v_place_3762_);
v___x_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3765_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
v___x_3769_ = lean_unsigned_to_nat(0u);
v___x_3770_ = 0;
v___x_3771_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3769_, v___x_3770_, v___x_3768_, v___f_3766_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3772_, lean_object* v_a_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3772_, v_a_3773_);
lean_dec(v_a_3773_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3776_, lean_object* v_place_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3777_, v_a_3778_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3781_, lean_object* v_place_3782_, lean_object* v_a_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3781_, v_place_3782_, v_a_3783_);
lean_dec(v_a_3783_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v_mutex_3786_, lean_object* v_x_3787_){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3789_ = lean_io_basemutex_unlock(v_mutex_3786_);
v___x_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed(lean_object* v_mutex_3792_, lean_object* v_x_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(v_mutex_3792_, v_x_3793_);
lean_dec(v_x_3793_);
lean_dec(v_mutex_3792_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_k_3796_, lean_object* v_ref_3797_, lean_object* v_x_3798_){
_start:
{
if (lean_obj_tag(v_x_3798_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3808_; 
lean_dec(v_ref_3797_);
lean_dec_ref(v_k_3796_);
v_a_3800_ = lean_ctor_get(v_x_3798_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_x_3798_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3802_ = v_x_3798_;
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v_x_3798_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3808_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
}
}
else
{
lean_object* v___x_3809_; 
lean_dec_ref_known(v_x_3798_, 1);
v___x_3809_ = lean_apply_2(v_k_3796_, v_ref_3797_, lean_box(0));
return v___x_3809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_k_3810_, lean_object* v_ref_3811_, lean_object* v_x_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_k_3810_, v_ref_3811_, v_x_3812_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_mutex_3815_, lean_object* v___f_3816_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; lean_object* v___x_3823_; 
v___x_3818_ = lean_io_basemutex_lock(v_mutex_3815_);
v___x_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
v___x_3821_ = lean_unsigned_to_nat(0u);
v___x_3822_ = 0;
v___x_3823_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3821_, v___x_3822_, v___x_3820_, v___f_3816_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_mutex_3824_, lean_object* v___f_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_mutex_3824_, v___f_3825_);
lean_dec(v_mutex_3824_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v___y_3828_){
_start:
{
if (lean_obj_tag(v___y_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
v_a_3829_ = lean_ctor_get(v___y_3828_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___y_3828_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___y_3828_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___y_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3845_; 
v_a_3837_ = lean_ctor_get(v___y_3828_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___y_3828_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3839_ = v___y_3828_;
v_isShared_3840_ = v_isSharedCheck_3845_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___y_3828_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3845_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_fst_3841_; lean_object* v___x_3843_; 
v_fst_3841_ = lean_ctor_get(v_a_3837_, 0);
lean_inc(v_fst_3841_);
lean_dec(v_a_3837_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v_fst_3841_);
v___x_3843_ = v___x_3839_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_fst_3841_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_3847_, lean_object* v_k_3848_){
_start:
{
lean_object* v_ref_3850_; lean_object* v_mutex_3851_; lean_object* v___f_3852_; lean_object* v___f_3853_; lean_object* v___f_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; lean_object* v___x_3857_; lean_object* v___y_3859_; 
v_ref_3850_ = lean_ctor_get(v_mutex_3847_, 0);
lean_inc(v_ref_3850_);
v_mutex_3851_ = lean_ctor_get(v_mutex_3847_, 1);
lean_inc_n(v_mutex_3851_, 2);
lean_dec_ref(v_mutex_3847_);
v___f_3852_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3852_, 0, v_mutex_3851_);
v___f_3853_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3853_, 0, v_k_3848_);
lean_closure_set(v___f_3853_, 1, v_ref_3850_);
v___f_3854_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_3854_, 0, v_mutex_3851_);
lean_closure_set(v___f_3854_, 1, v___f_3853_);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = 0;
v___x_3857_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_3854_, v___f_3852_, v___x_3855_, v___x_3856_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3861_; 
v_a_3861_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3857_, 1);
if (lean_obj_tag(v_a_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
v_a_3862_ = lean_ctor_get(v_a_3861_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v_a_3861_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v_a_3861_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v_a_3861_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
v___y_3859_ = v___x_3867_;
goto v___jp_3858_;
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3878_; 
v_a_3870_ = lean_ctor_get(v_a_3861_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_a_3861_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3872_ = v_a_3861_;
v_isShared_3873_ = v_isSharedCheck_3878_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v_a_3861_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3878_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v_fst_3874_; lean_object* v___x_3876_; 
v_fst_3874_ = lean_ctor_get(v_a_3870_, 0);
lean_inc(v_fst_3874_);
lean_dec(v_a_3870_);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 0, v_fst_3874_);
v___x_3876_ = v___x_3872_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_fst_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
v___y_3859_ = v___x_3876_;
goto v___jp_3858_;
}
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3888_; 
v_a_3879_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3881_ = v___x_3857_;
v_isShared_3882_ = v_isSharedCheck_3888_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3857_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3888_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___f_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___f_3883_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___x_3884_ = lean_task_map(v___f_3883_, v_a_3879_, v___x_3855_, v___x_3856_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3884_);
v___x_3886_ = v___x_3881_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
v___jp_3858_:
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3860_, 0, v___y_3859_);
return v___x_3860_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_3889_, lean_object* v_k_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3889_, v_k_3890_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_3893_, lean_object* v_00_u03b2_3894_, lean_object* v_mutex_3895_, lean_object* v_k_3896_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3895_, v_k_3896_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_3899_, lean_object* v_00_u03b2_3900_, lean_object* v_mutex_3901_, lean_object* v_k_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_3899_, v_00_u03b2_3900_, v_mutex_3901_, v_k_3902_);
return v_res_3904_;
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
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3937_; 
v_a_3927_ = lean_ctor_get(v_x_3916_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_x_3916_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3929_ = v_x_3916_;
v_isShared_3930_ = v_isSharedCheck_3937_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v_x_3916_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3937_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3931_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3931_, 0, v_producers_3905_);
lean_ctor_set(v___x_3931_, 1, v_a_3927_);
lean_ctor_set(v___x_3931_, 2, v_capacity_3906_);
lean_ctor_set(v___x_3931_, 3, v_size_3907_);
lean_ctor_set(v___x_3931_, 4, v_buffer_3908_);
lean_ctor_set(v___x_3931_, 5, v_write_3909_);
lean_ctor_set(v___x_3931_, 6, v_read_3910_);
lean_ctor_set(v___x_3931_, 7, v_receivers_3911_);
lean_ctor_set(v___x_3931_, 8, v_nextId_3912_);
lean_ctor_set(v___x_3931_, 9, v_pos_3914_);
lean_ctor_set_uint8(v___x_3931_, sizeof(void*)*10, v_closed_3913_);
v___x_3932_ = lean_st_ref_set(v___y_3915_, v___x_3931_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 0, v___x_3932_);
v___x_3934_ = v___x_3929_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3934_);
return v___x_3935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_3938_, lean_object* v_capacity_3939_, lean_object* v_size_3940_, lean_object* v_buffer_3941_, lean_object* v_write_3942_, lean_object* v_read_3943_, lean_object* v_receivers_3944_, lean_object* v_nextId_3945_, lean_object* v_closed_3946_, lean_object* v_pos_3947_, lean_object* v___y_3948_, lean_object* v_x_3949_, lean_object* v___y_3950_){
_start:
{
uint8_t v_closed_boxed_3951_; lean_object* v_res_3952_; 
v_closed_boxed_3951_ = lean_unbox(v_closed_3946_);
v_res_3952_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_3938_, v_capacity_3939_, v_size_3940_, v_buffer_3941_, v_write_3942_, v_read_3943_, v_receivers_3944_, v_nextId_3945_, v_closed_boxed_3951_, v_pos_3947_, v___y_3948_, v_x_3949_);
lean_dec(v___y_3948_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_3953_){
_start:
{
if (lean_obj_tag(v_x_3953_) == 0)
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v_x_3953_);
return v___x_3955_;
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3965_; 
v_a_3956_ = lean_ctor_get(v_x_3953_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_x_3953_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3958_ = v_x_3953_;
v_isShared_3959_ = v_isSharedCheck_3965_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v_x_3953_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3965_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = l_List_reverse___redArg(v_a_3956_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3960_);
v___x_3962_ = v___x_3958_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
return v___x_3963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_3966_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_3969_, lean_object* v___x_3970_, lean_object* v_x_3971_){
_start:
{
if (lean_obj_tag(v_x_3971_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v___x_3970_);
lean_dec(v_a_3969_);
v_a_3973_ = lean_ctor_get(v_x_3971_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_x_3971_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3975_ = v_x_3971_;
v_isShared_3976_ = v_isSharedCheck_3981_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v_x_3971_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3981_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3998_; 
v_a_3982_ = lean_ctor_get(v_x_3971_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v_x_3971_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3984_ = v_x_3971_;
v_isShared_3985_ = v_isSharedCheck_3998_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v_x_3971_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3998_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
uint8_t v___x_3986_; 
v___x_3986_ = l_List_isEmpty___redArg(v_a_3969_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3989_; 
lean_dec(v___x_3970_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v_a_3982_);
lean_ctor_set(v___x_3987_, 1, v_a_3969_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3987_);
v___x_3989_ = v___x_3984_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
}
else
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3995_; 
lean_dec(v_a_3969_);
v___x_3992_ = l_List_reverse___redArg(v_a_3982_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3970_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3993_);
v___x_3995_ = v___x_3984_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
return v___x_3996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_3999_, lean_object* v___x_4000_, lean_object* v_x_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_3999_, v___x_4000_, v_x_4001_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_4004_){
_start:
{
uint8_t v___y_4007_; 
if (lean_obj_tag(v_x_4004_) == 0)
{
lean_object* v___x_4011_; 
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v_x_4004_);
return v___x_4011_;
}
else
{
lean_object* v_a_4012_; uint8_t v___x_4013_; 
v_a_4012_ = lean_ctor_get(v_x_4004_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v_x_4004_, 1);
v___x_4013_ = lean_unbox(v_a_4012_);
lean_dec(v_a_4012_);
if (v___x_4013_ == 0)
{
uint8_t v___x_4014_; 
v___x_4014_ = 1;
v___y_4007_ = v___x_4014_;
goto v___jp_4006_;
}
else
{
uint8_t v___x_4015_; 
v___x_4015_ = 0;
v___y_4007_ = v___x_4015_;
goto v___jp_4006_;
}
}
v___jp_4006_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4008_ = lean_box(v___y_4007_);
v___x_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
v___x_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
return v___x_4010_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4016_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_4019_, lean_object* v_x_4020_, lean_object* v_head_4021_, lean_object* v_x_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4019_, v_x_4020_, v_head_4021_, v_x_4022_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_4031_, lean_object* v_x_4032_){
_start:
{
if (lean_obj_tag(v_x_4031_) == 0)
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v_x_4032_);
v___x_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
return v___x_4035_;
}
else
{
lean_object* v_head_4036_; lean_object* v_tail_4037_; lean_object* v_waiter_4038_; lean_object* v___f_4039_; lean_object* v_val_4041_; 
v_head_4036_ = lean_ctor_get(v_x_4031_, 0);
lean_inc(v_head_4036_);
v_tail_4037_ = lean_ctor_get(v_x_4031_, 1);
lean_inc(v_tail_4037_);
lean_dec_ref_known(v_x_4031_, 2);
v_waiter_4038_ = lean_ctor_get(v_head_4036_, 1);
lean_inc(v_waiter_4038_);
v___f_4039_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4039_, 0, v_tail_4037_);
lean_closure_set(v___f_4039_, 1, v_x_4032_);
lean_closure_set(v___f_4039_, 2, v_head_4036_);
if (lean_obj_tag(v_waiter_4038_) == 0)
{
lean_object* v___x_4045_; 
v___x_4045_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v_val_4041_ = v___x_4045_;
goto v___jp_4040_;
}
else
{
lean_object* v_val_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4060_; 
v_val_4046_ = lean_ctor_get(v_waiter_4038_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_waiter_4038_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4048_ = v_waiter_4038_;
v_isShared_4049_ = v_isSharedCheck_4060_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_val_4046_);
lean_dec(v_waiter_4038_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4060_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v_finished_4050_; lean_object* v___x_4051_; lean_object* v___f_4052_; lean_object* v___x_4054_; 
v_finished_4050_ = lean_ctor_get(v_val_4046_, 0);
lean_inc(v_finished_4050_);
lean_dec(v_val_4046_);
v___x_4051_ = lean_st_ref_get(v_finished_4050_);
lean_dec(v_finished_4050_);
v___f_4052_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4051_);
v___x_4054_ = v___x_4048_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4051_);
v___x_4054_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; lean_object* v___x_4058_; 
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
v___x_4056_ = lean_unsigned_to_nat(0u);
v___x_4057_ = 0;
v___x_4058_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4056_, v___x_4057_, v___x_4055_, v___f_4052_);
v_val_4041_ = v___x_4058_;
goto v___jp_4040_;
}
}
}
v___jp_4040_:
{
lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = 0;
v___x_4044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4042_, v___x_4043_, v_val_4041_, v___f_4039_);
return v___x_4044_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_4061_, lean_object* v_x_4062_, lean_object* v_head_4063_, lean_object* v_x_4064_){
_start:
{
if (lean_obj_tag(v_x_4064_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4074_; 
lean_dec_ref(v_head_4063_);
lean_dec(v_x_4062_);
lean_dec(v_tail_4061_);
v_a_4066_ = lean_ctor_get(v_x_4064_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_x_4064_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4068_ = v_x_4064_;
v_isShared_4069_ = v_isSharedCheck_4074_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v_x_4064_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4074_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
}
}
else
{
lean_object* v_a_4075_; uint8_t v___x_4076_; 
v_a_4075_ = lean_ctor_get(v_x_4064_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v_x_4064_, 1);
v___x_4076_ = lean_unbox(v_a_4075_);
lean_dec(v_a_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; 
lean_dec_ref(v_head_4063_);
v___x_4077_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4061_, v_x_4062_);
return v___x_4077_;
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4078_, 0, v_head_4063_);
lean_ctor_set(v___x_4078_, 1, v_x_4062_);
v___x_4079_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4061_, v___x_4078_);
return v___x_4079_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_4080_, lean_object* v_x_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4080_, v_x_4081_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_4084_, lean_object* v___x_4085_, lean_object* v___f_4086_, lean_object* v_x_4087_){
_start:
{
if (lean_obj_tag(v_x_4087_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4097_; 
lean_dec_ref(v___f_4086_);
lean_dec(v___x_4085_);
lean_dec(v_eList_4084_);
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
lean_object* v_a_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; lean_object* v___x_4102_; lean_object* v___f_4103_; lean_object* v___x_4104_; 
v_a_4098_ = lean_ctor_get(v_x_4087_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v_x_4087_, 1);
lean_inc(v___x_4085_);
v___x_4099_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4084_, v___x_4085_);
v___x_4100_ = lean_unsigned_to_nat(0u);
v___x_4101_ = 0;
v___x_4102_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4100_, v___x_4101_, v___x_4099_, v___f_4086_);
v___f_4103_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4103_, 0, v_a_4098_);
lean_closure_set(v___f_4103_, 1, v___x_4085_);
v___x_4104_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4100_, v___x_4101_, v___x_4102_, v___f_4103_);
return v___x_4104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_4105_, lean_object* v___x_4106_, lean_object* v___f_4107_, lean_object* v_x_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v_eList_4105_, v___x_4106_, v___f_4107_, v_x_4108_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_eList_4115_; lean_object* v_dList_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___f_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; lean_object* v___x_4122_; lean_object* v___f_4123_; lean_object* v___x_4124_; 
v_eList_4115_ = lean_ctor_get(v_q_4112_, 0);
lean_inc(v_eList_4115_);
v_dList_4116_ = lean_ctor_get(v_q_4112_, 1);
lean_inc(v_dList_4116_);
lean_dec_ref(v_q_4112_);
v___x_4117_ = lean_box(0);
v___x_4118_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4116_, v___x_4117_);
v___f_4119_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = 0;
v___x_4122_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4120_, v___x_4121_, v___x_4118_, v___f_4119_);
v___f_4123_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4123_, 0, v_eList_4115_);
lean_closure_set(v___f_4123_, 1, v___x_4117_);
lean_closure_set(v___f_4123_, 2, v___f_4119_);
v___x_4124_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4120_, v___x_4121_, v___x_4122_, v___f_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4125_, v___y_4126_);
lean_dec(v___y_4126_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4129_, lean_object* v_x_4130_){
_start:
{
if (lean_obj_tag(v_x_4130_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4140_; 
v_a_4132_ = lean_ctor_get(v_x_4130_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_x_4130_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4134_ = v_x_4130_;
v_isShared_4135_ = v_isSharedCheck_4140_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v_x_4130_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4140_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; 
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
return v___x_4138_;
}
}
}
else
{
lean_object* v_a_4141_; lean_object* v_producers_4142_; lean_object* v_waiters_4143_; lean_object* v_capacity_4144_; lean_object* v_size_4145_; lean_object* v_buffer_4146_; lean_object* v_write_4147_; lean_object* v_read_4148_; lean_object* v_receivers_4149_; lean_object* v_nextId_4150_; uint8_t v_closed_4151_; lean_object* v_pos_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___f_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; 
v_a_4141_ = lean_ctor_get(v_x_4130_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v_x_4130_, 1);
v_producers_4142_ = lean_ctor_get(v_a_4141_, 0);
lean_inc_ref(v_producers_4142_);
v_waiters_4143_ = lean_ctor_get(v_a_4141_, 1);
lean_inc_ref(v_waiters_4143_);
v_capacity_4144_ = lean_ctor_get(v_a_4141_, 2);
lean_inc(v_capacity_4144_);
v_size_4145_ = lean_ctor_get(v_a_4141_, 3);
lean_inc(v_size_4145_);
v_buffer_4146_ = lean_ctor_get(v_a_4141_, 4);
lean_inc_ref(v_buffer_4146_);
v_write_4147_ = lean_ctor_get(v_a_4141_, 5);
lean_inc(v_write_4147_);
v_read_4148_ = lean_ctor_get(v_a_4141_, 6);
lean_inc(v_read_4148_);
v_receivers_4149_ = lean_ctor_get(v_a_4141_, 7);
lean_inc(v_receivers_4149_);
v_nextId_4150_ = lean_ctor_get(v_a_4141_, 8);
lean_inc(v_nextId_4150_);
v_closed_4151_ = lean_ctor_get_uint8(v_a_4141_, sizeof(void*)*10);
v_pos_4152_ = lean_ctor_get(v_a_4141_, 9);
lean_inc(v_pos_4152_);
lean_dec(v_a_4141_);
v___x_4153_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4143_, v___y_4129_);
v___x_4154_ = lean_box(v_closed_4151_);
lean_inc(v___y_4129_);
v___f_4155_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4155_, 0, v_producers_4142_);
lean_closure_set(v___f_4155_, 1, v_capacity_4144_);
lean_closure_set(v___f_4155_, 2, v_size_4145_);
lean_closure_set(v___f_4155_, 3, v_buffer_4146_);
lean_closure_set(v___f_4155_, 4, v_write_4147_);
lean_closure_set(v___f_4155_, 5, v_read_4148_);
lean_closure_set(v___f_4155_, 6, v_receivers_4149_);
lean_closure_set(v___f_4155_, 7, v_nextId_4150_);
lean_closure_set(v___f_4155_, 8, v___x_4154_);
lean_closure_set(v___f_4155_, 9, v_pos_4152_);
lean_closure_set(v___f_4155_, 10, v___y_4129_);
v___x_4156_ = lean_unsigned_to_nat(0u);
v___x_4157_ = 0;
v___x_4158_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4156_, v___x_4157_, v___x_4153_, v___f_4155_);
return v___x_4158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4159_, lean_object* v_x_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4159_, v_x_4160_);
lean_dec(v___y_4159_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4163_){
_start:
{
lean_object* v___x_4165_; lean_object* v___f_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; lean_object* v___x_4171_; 
v___x_4165_ = lean_st_ref_get(v___y_4163_);
lean_inc(v___y_4163_);
v___f_4166_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4166_, 0, v___y_4163_);
v___x_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
v___x_4169_ = lean_unsigned_to_nat(0u);
v___x_4170_ = 0;
v___x_4171_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4169_, v___x_4170_, v___x_4168_, v___f_4166_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4172_);
lean_dec(v___y_4172_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4175_, lean_object* v_waiter_4176_){
_start:
{
lean_object* v_val_4179_; lean_object* v___x_4181_; 
v___x_4181_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4175_, v_waiter_4176_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4181_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4181_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
lean_ctor_set_tag(v___x_4184_, 1);
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
v_val_4179_ = v___x_4187_;
goto v___jp_4178_;
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
v_a_4190_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4181_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4181_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
lean_ctor_set_tag(v___x_4192_, 0);
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
v_val_4179_ = v___x_4195_;
goto v___jp_4178_;
}
}
}
v___jp_4178_:
{
lean_object* v___x_4180_; 
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v_val_4179_);
return v___x_4180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4198_, lean_object* v_waiter_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4198_, v_waiter_4199_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4202_){
_start:
{
if (lean_obj_tag(v_x_4202_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4212_; 
v_a_4204_ = lean_ctor_get(v_x_4202_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_x_4202_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4206_ = v_x_4202_;
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v_x_4202_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4212_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
return v___x_4210_;
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4222_; 
v_a_4213_ = lean_ctor_get(v_x_4202_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v_x_4202_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4215_ = v_x_4202_;
v_isShared_4216_ = v_isSharedCheck_4222_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v_x_4202_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4222_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
v___x_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4217_, 0, v_a_4213_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4217_);
v___x_4219_ = v___x_4215_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
lean_object* v___x_4220_; 
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
return v___x_4220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4223_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_val_4226_, lean_object* v_x_4227_){
_start:
{
if (lean_obj_tag(v_x_4227_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4237_; 
v_a_4229_ = lean_ctor_get(v_x_4227_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_x_4227_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4231_ = v_x_4227_;
v_isShared_4232_ = v_isSharedCheck_4237_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v_x_4227_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4237_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4229_);
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
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4249_; 
v_a_4238_ = lean_ctor_get(v_x_4227_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v_x_4227_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4240_ = v_x_4227_;
v_isShared_4241_ = v_isSharedCheck_4249_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v_x_4227_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4249_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v_pos_4242_; uint8_t v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4246_; 
v_pos_4242_ = lean_ctor_get(v_a_4238_, 1);
lean_inc(v_pos_4242_);
lean_dec(v_a_4238_);
v___x_4243_ = lean_nat_dec_eq(v_pos_4242_, v_val_4226_);
lean_dec(v_pos_4242_);
v___x_4244_ = lean_box(v___x_4243_);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4244_);
v___x_4246_ = v___x_4240_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4244_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_val_4250_, lean_object* v_x_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_val_4250_, v_x_4251_);
lean_dec(v_val_4250_);
return v_res_4253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v___x_4254_, uint8_t v_closed_4255_, lean_object* v___f_4256_, lean_object* v_x_4257_){
_start:
{
if (lean_obj_tag(v_x_4257_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref(v___f_4256_);
lean_dec(v___x_4254_);
v_a_4259_ = lean_ctor_get(v_x_4257_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_x_4257_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4261_ = v_x_4257_;
v_isShared_4262_ = v_isSharedCheck_4267_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v_x_4257_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4267_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
lean_object* v___x_4265_; 
v___x_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
return v___x_4265_;
}
}
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4278_; 
v_a_4268_ = lean_ctor_get(v_x_4257_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v_x_4257_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4270_ = v_x_4257_;
v_isShared_4271_ = v_isSharedCheck_4278_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v_x_4257_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4278_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4272_; lean_object* v___x_4274_; 
v___x_4272_ = lean_st_ref_get(v_a_4268_);
lean_dec(v_a_4268_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 0, v___x_4272_);
v___x_4274_ = v___x_4270_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
v___x_4276_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4254_, v_closed_4255_, v___x_4275_, v___f_4256_);
return v___x_4276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v___x_4279_, lean_object* v_closed_4280_, lean_object* v___f_4281_, lean_object* v_x_4282_, lean_object* v___y_4283_){
_start:
{
uint8_t v_closed_boxed_4284_; lean_object* v_res_4285_; 
v_closed_boxed_4284_ = lean_unbox(v_closed_4280_);
v_res_4285_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v___x_4279_, v_closed_boxed_4284_, v___f_4281_, v_x_4282_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v_id_4286_, lean_object* v___y_4287_, lean_object* v_x_4288_){
_start:
{
if (lean_obj_tag(v_x_4288_) == 0)
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4298_; 
v_a_4290_ = lean_ctor_get(v_x_4288_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v_x_4288_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4292_ = v_x_4288_;
v_isShared_4293_ = v_isSharedCheck_4298_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v_x_4288_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4298_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
lean_object* v___x_4296_; 
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4338_; 
v_a_4299_ = lean_ctor_get(v_x_4288_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_x_4288_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4301_ = v_x_4288_;
v_isShared_4302_ = v_isSharedCheck_4338_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v_x_4288_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4338_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
uint8_t v_closed_4303_; 
v_closed_4303_ = lean_ctor_get_uint8(v_a_4299_, sizeof(void*)*10);
if (v_closed_4303_ == 0)
{
lean_object* v_capacity_4304_; lean_object* v_size_4305_; lean_object* v_receivers_4306_; lean_object* v___x_4307_; 
v_capacity_4304_ = lean_ctor_get(v_a_4299_, 2);
lean_inc(v_capacity_4304_);
v_size_4305_ = lean_ctor_get(v_a_4299_, 3);
lean_inc(v_size_4305_);
v_receivers_4306_ = lean_ctor_get(v_a_4299_, 7);
lean_inc(v_receivers_4306_);
lean_dec(v_a_4299_);
v___x_4307_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4306_, v_id_4286_);
lean_dec(v_receivers_4306_);
if (lean_obj_tag(v___x_4307_) == 1)
{
lean_object* v_val_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4327_; 
v_val_4308_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4310_ = v___x_4307_;
v_isShared_4311_ = v_isSharedCheck_4327_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_val_4308_);
lean_dec(v___x_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4327_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4312_ = lean_unsigned_to_nat(0u);
v___x_4313_ = lean_nat_dec_eq(v_size_4305_, v___x_4312_);
lean_dec(v_size_4305_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___x_4317_; lean_object* v___f_4318_; lean_object* v___x_4319_; 
lean_del_object(v___x_4310_);
lean_del_object(v___x_4301_);
v___x_4314_ = lean_nat_mod(v_val_4308_, v_capacity_4304_);
lean_dec(v_capacity_4304_);
v___x_4315_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4314_, v___y_4287_);
v___f_4316_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4316_, 0, v_val_4308_);
v___x_4317_ = lean_box(v_closed_4303_);
v___f_4318_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_4318_, 0, v___x_4312_);
lean_closure_set(v___f_4318_, 1, v___x_4317_);
lean_closure_set(v___f_4318_, 2, v___f_4316_);
v___x_4319_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4312_, v_closed_4303_, v___x_4315_, v___f_4318_);
return v___x_4319_;
}
else
{
lean_object* v___x_4320_; lean_object* v___x_4322_; 
lean_dec(v_val_4308_);
lean_dec(v_capacity_4304_);
v___x_4320_ = lean_box(v_closed_4303_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4320_);
v___x_4322_ = v___x_4301_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4320_);
v___x_4322_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
lean_object* v___x_4324_; 
if (v_isShared_4311_ == 0)
{
lean_ctor_set_tag(v___x_4310_, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4322_);
v___x_4324_ = v___x_4310_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4322_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
else
{
lean_object* v___x_4328_; lean_object* v___x_4330_; 
lean_dec(v___x_4307_);
lean_dec(v_size_4305_);
lean_dec(v_capacity_4304_);
v___x_4328_ = lean_box(v_closed_4303_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4328_);
v___x_4330_ = v___x_4301_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4330_);
return v___x_4331_;
}
}
}
else
{
lean_object* v___x_4333_; lean_object* v___x_4335_; 
lean_dec(v_a_4299_);
v___x_4333_ = lean_box(v_closed_4303_);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 0, v___x_4333_);
v___x_4335_ = v___x_4301_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4333_);
v___x_4335_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4336_; 
v___x_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4335_);
return v___x_4336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v_id_4339_, lean_object* v___y_4340_, lean_object* v_x_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v_id_4339_, v___y_4340_, v_x_4341_);
lean_dec(v___y_4340_);
lean_dec(v_id_4339_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4344_, lean_object* v_x_4345_){
_start:
{
if (lean_obj_tag(v_x_4345_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4355_; 
lean_dec_ref(v_x_4344_);
v_a_4347_ = lean_ctor_get(v_x_4345_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v_x_4345_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4349_ = v_x_4345_;
v_isShared_4350_ = v_isSharedCheck_4355_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v_x_4345_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4355_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
lean_object* v___x_4353_; 
v___x_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4352_);
return v___x_4353_;
}
}
}
else
{
lean_object* v___x_4356_; 
lean_dec_ref_known(v_x_4345_, 1);
v___x_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4356_, 0, v_x_4344_);
return v___x_4356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4357_, lean_object* v_x_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4357_, v_x_4358_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4367_, lean_object* v_receiverId_4368_, lean_object* v_receivers_4369_, lean_object* v_x_4370_){
_start:
{
if (lean_obj_tag(v_x_4370_) == 0)
{
lean_object* v___x_4372_; 
lean_dec(v_receivers_4369_);
lean_dec(v_receiverId_4368_);
v___x_4372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4372_, 0, v_x_4370_);
return v___x_4372_;
}
else
{
lean_object* v_a_4373_; 
v_a_4373_ = lean_ctor_get(v_x_4370_, 0);
if (lean_obj_tag(v_a_4373_) == 1)
{
lean_object* v___x_4374_; lean_object* v_producers_4375_; lean_object* v_waiters_4376_; lean_object* v_capacity_4377_; lean_object* v_size_4378_; lean_object* v_buffer_4379_; lean_object* v_write_4380_; lean_object* v_read_4381_; lean_object* v_nextId_4382_; uint8_t v_closed_4383_; lean_object* v_pos_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4398_; 
v___x_4374_ = lean_st_ref_take(v_a_4367_);
v_producers_4375_ = lean_ctor_get(v___x_4374_, 0);
v_waiters_4376_ = lean_ctor_get(v___x_4374_, 1);
v_capacity_4377_ = lean_ctor_get(v___x_4374_, 2);
v_size_4378_ = lean_ctor_get(v___x_4374_, 3);
v_buffer_4379_ = lean_ctor_get(v___x_4374_, 4);
v_write_4380_ = lean_ctor_get(v___x_4374_, 5);
v_read_4381_ = lean_ctor_get(v___x_4374_, 6);
v_nextId_4382_ = lean_ctor_get(v___x_4374_, 8);
v_closed_4383_ = lean_ctor_get_uint8(v___x_4374_, sizeof(void*)*10);
v_pos_4384_ = lean_ctor_get(v___x_4374_, 9);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4398_ == 0)
{
lean_object* v_unused_4399_; 
v_unused_4399_ = lean_ctor_get(v___x_4374_, 7);
lean_dec(v_unused_4399_);
v___x_4386_ = v___x_4374_;
v_isShared_4387_ = v_isSharedCheck_4398_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_pos_4384_);
lean_inc(v_nextId_4382_);
lean_inc(v_read_4381_);
lean_inc(v_write_4380_);
lean_inc(v_buffer_4379_);
lean_inc(v_size_4378_);
lean_inc(v_capacity_4377_);
lean_inc(v_waiters_4376_);
lean_inc(v_producers_4375_);
lean_dec(v___x_4374_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4398_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4388_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4368_, v_receivers_4369_);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 7, v___x_4388_);
v___x_4390_ = v___x_4386_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_producers_4375_);
lean_ctor_set(v_reuseFailAlloc_4397_, 1, v_waiters_4376_);
lean_ctor_set(v_reuseFailAlloc_4397_, 2, v_capacity_4377_);
lean_ctor_set(v_reuseFailAlloc_4397_, 3, v_size_4378_);
lean_ctor_set(v_reuseFailAlloc_4397_, 4, v_buffer_4379_);
lean_ctor_set(v_reuseFailAlloc_4397_, 5, v_write_4380_);
lean_ctor_set(v_reuseFailAlloc_4397_, 6, v_read_4381_);
lean_ctor_set(v_reuseFailAlloc_4397_, 7, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4397_, 8, v_nextId_4382_);
lean_ctor_set(v_reuseFailAlloc_4397_, 9, v_pos_4384_);
lean_ctor_set_uint8(v_reuseFailAlloc_4397_, sizeof(void*)*10, v_closed_4383_);
v___x_4390_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___f_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; lean_object* v___x_4396_; 
v___x_4391_ = lean_st_ref_set(v_a_4367_, v___x_4390_);
v___f_4392_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4392_, 0, v_x_4370_);
v___x_4393_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_4394_ = lean_unsigned_to_nat(0u);
v___x_4395_ = 0;
v___x_4396_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4394_, v___x_4395_, v___x_4393_, v___f_4392_);
return v___x_4396_;
}
}
}
else
{
lean_object* v___x_4400_; 
lean_dec_ref_known(v_x_4370_, 1);
lean_dec(v_receivers_4369_);
lean_dec(v_receiverId_4368_);
v___x_4400_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4401_, lean_object* v_receiverId_4402_, lean_object* v_receivers_4403_, lean_object* v_x_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4401_, v_receiverId_4402_, v_receivers_4403_, v_x_4404_);
lean_dec(v_a_4401_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4407_){
_start:
{
if (lean_obj_tag(v_x_4407_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4417_; 
v_a_4409_ = lean_ctor_get(v_x_4407_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v_x_4407_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4411_ = v_x_4407_;
v_isShared_4412_ = v_isSharedCheck_4417_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v_x_4407_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4417_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4415_; 
v___x_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
return v___x_4415_;
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4430_; 
v_a_4418_ = lean_ctor_get(v_x_4407_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v_x_4407_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4420_ = v_x_4407_;
v_isShared_4421_ = v_isSharedCheck_4430_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v_x_4407_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4430_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v_size_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4427_; 
v_size_4422_ = lean_ctor_get(v_a_4418_, 3);
lean_inc(v_size_4422_);
lean_dec(v_a_4418_);
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = lean_nat_dec_eq(v_size_4422_, v___x_4423_);
lean_dec(v_size_4422_);
v___x_4425_ = lean_box(v___x_4424_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4425_);
v___x_4427_ = v___x_4420_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v___x_4425_);
v___x_4427_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
lean_object* v___x_4428_; 
v___x_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
return v___x_4428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4431_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4435_){
_start:
{
lean_object* v___x_4437_; lean_object* v___f_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; uint8_t v___x_4442_; lean_object* v___x_4443_; 
v___x_4437_ = lean_st_ref_get(v_a_4435_);
v___f_4438_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4437_);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
v___x_4441_ = lean_unsigned_to_nat(0u);
v___x_4442_ = 0;
v___x_4443_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4441_, v___x_4442_, v___x_4440_, v___f_4438_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4444_, lean_object* v___y_4445_){
_start:
{
lean_object* v_res_4446_; 
v_res_4446_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4444_);
lean_dec(v_a_4444_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4447_, lean_object* v_next_4448_){
_start:
{
lean_object* v___x_4450_; lean_object* v_fst_4452_; lean_object* v_snd_4453_; lean_object* v_value_4457_; lean_object* v_pos_4458_; lean_object* v_remaining_4459_; uint8_t v___x_4460_; 
v___x_4450_ = lean_st_ref_take(v_slot_4447_);
v_value_4457_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_value_4457_);
v_pos_4458_ = lean_ctor_get(v___x_4450_, 1);
lean_inc(v_pos_4458_);
v_remaining_4459_ = lean_ctor_get(v___x_4450_, 2);
lean_inc(v_remaining_4459_);
v___x_4460_ = lean_nat_dec_eq(v_next_4448_, v_pos_4458_);
if (v___x_4460_ == 0)
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
lean_dec(v_remaining_4459_);
lean_dec(v_pos_4458_);
lean_dec(v_value_4457_);
v___x_4461_ = lean_box(0);
v___x_4462_ = lean_box(v___x_4460_);
v___x_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4461_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
v_fst_4452_ = v___x_4463_;
v_snd_4453_ = v___x_4450_;
goto v___jp_4451_;
}
else
{
lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4482_; 
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4482_ == 0)
{
lean_object* v_unused_4483_; lean_object* v_unused_4484_; lean_object* v_unused_4485_; 
v_unused_4483_ = lean_ctor_get(v___x_4450_, 2);
lean_dec(v_unused_4483_);
v_unused_4484_ = lean_ctor_get(v___x_4450_, 1);
lean_dec(v_unused_4484_);
v_unused_4485_ = lean_ctor_get(v___x_4450_, 0);
lean_dec(v_unused_4485_);
v___x_4465_ = v___x_4450_;
v_isShared_4466_ = v_isSharedCheck_4482_;
goto v_resetjp_4464_;
}
else
{
lean_dec(v___x_4450_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4482_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4467_; uint8_t v___x_4468_; 
v___x_4467_ = lean_unsigned_to_nat(1u);
v___x_4468_ = lean_nat_dec_eq(v_remaining_4459_, v___x_4467_);
if (v___x_4468_ == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4473_; 
v___x_4469_ = lean_box(v___x_4468_);
lean_inc(v_value_4457_);
v___x_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4470_, 0, v_value_4457_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
v___x_4471_ = lean_nat_sub(v_remaining_4459_, v___x_4467_);
lean_dec(v_remaining_4459_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 2, v___x_4471_);
v___x_4473_ = v___x_4465_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_value_4457_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v_pos_4458_);
lean_ctor_set(v_reuseFailAlloc_4474_, 2, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
v_fst_4452_ = v___x_4470_;
v_snd_4453_ = v___x_4473_;
goto v___jp_4451_;
}
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4480_; 
lean_dec(v_remaining_4459_);
v___x_4475_ = lean_box(v___x_4460_);
v___x_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4476_, 0, v_value_4457_);
lean_ctor_set(v___x_4476_, 1, v___x_4475_);
v___x_4477_ = lean_box(0);
v___x_4478_ = lean_unsigned_to_nat(0u);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 2, v___x_4478_);
lean_ctor_set(v___x_4465_, 0, v___x_4477_);
v___x_4480_ = v___x_4465_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_pos_4458_);
lean_ctor_set(v_reuseFailAlloc_4481_, 2, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
v_fst_4452_ = v___x_4476_;
v_snd_4453_ = v___x_4480_;
goto v___jp_4451_;
}
}
}
}
v___jp_4451_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4454_ = lean_st_ref_set(v_slot_4447_, v_snd_4453_);
v___x_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4455_, 0, v_fst_4452_);
v___x_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4455_);
return v___x_4456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4486_, lean_object* v_next_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4486_, v_next_4487_);
lean_dec(v_next_4487_);
lean_dec(v_slot_4486_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4490_, uint8_t v_a_4491_, lean_object* v___f_4492_, lean_object* v_x_4493_){
_start:
{
if (lean_obj_tag(v_x_4493_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4503_; 
lean_dec_ref(v___f_4492_);
v_a_4495_ = lean_ctor_get(v_x_4493_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v_x_4493_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4497_ = v_x_4493_;
v_isShared_4498_ = v_isSharedCheck_4503_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v_x_4493_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4503_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
lean_object* v___x_4501_; 
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v_a_4504_ = lean_ctor_get(v_x_4493_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v_x_4493_, 1);
v___x_4505_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4504_, v_next_4490_);
lean_dec(v_a_4504_);
v___x_4506_ = lean_unsigned_to_nat(0u);
v___x_4507_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4506_, v_a_4491_, v___x_4505_, v___f_4492_);
return v___x_4507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4508_, lean_object* v_a_4509_, lean_object* v___f_4510_, lean_object* v_x_4511_, lean_object* v___y_4512_){
_start:
{
uint8_t v_a_12247__boxed_4513_; lean_object* v_res_4514_; 
v_a_12247__boxed_4513_ = lean_unbox(v_a_4509_);
v_res_4514_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4508_, v_a_12247__boxed_4513_, v___f_4510_, v_x_4511_);
lean_dec(v_next_4508_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4515_, lean_object* v___f_4516_, lean_object* v_____r_4517_, lean_object* v_st_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4521_ = lean_st_ref_set(v___y_4519_, v_st_4518_);
v___x_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
v___x_4524_ = lean_unsigned_to_nat(0u);
v___x_4525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4524_, v_a_4515_, v___x_4523_, v___f_4516_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4526_, lean_object* v___f_4527_, lean_object* v_____r_4528_, lean_object* v_st_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
uint8_t v_a_12285__boxed_4532_; lean_object* v_res_4533_; 
v_a_12285__boxed_4532_ = lean_unbox(v_a_4526_);
v_res_4533_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_12285__boxed_4532_, v___f_4527_, v_____r_4528_, v_st_4529_, v___y_4530_);
lean_dec(v___y_4530_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4534_, lean_object* v_waiters_4535_, lean_object* v_capacity_4536_, lean_object* v_size_4537_, lean_object* v_buffer_4538_, lean_object* v_write_4539_, lean_object* v_read_4540_, lean_object* v_receivers_4541_, lean_object* v_nextId_4542_, uint8_t v_closed_4543_, lean_object* v_pos_4544_, lean_object* v___f_4545_, lean_object* v_a_4546_, lean_object* v_x_4547_){
_start:
{
if (lean_obj_tag(v_x_4547_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4557_; 
lean_dec_ref(v___f_4545_);
lean_dec(v_pos_4544_);
lean_dec(v_nextId_4542_);
lean_dec(v_receivers_4541_);
lean_dec(v_read_4540_);
lean_dec(v_write_4539_);
lean_dec_ref(v_buffer_4538_);
lean_dec(v_size_4537_);
lean_dec(v_capacity_4536_);
lean_dec_ref(v_waiters_4535_);
lean_dec_ref(v_snd_4534_);
v_a_4549_ = lean_ctor_get(v_x_4547_, 0);
v_isSharedCheck_4557_ = !lean_is_exclusive(v_x_4547_);
if (v_isSharedCheck_4557_ == 0)
{
v___x_4551_ = v_x_4547_;
v_isShared_4552_ = v_isSharedCheck_4557_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v_x_4547_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4557_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4555_; 
v___x_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
return v___x_4555_;
}
}
}
else
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_dec_ref_known(v_x_4547_, 1);
v___x_4558_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4558_, 0, v_snd_4534_);
lean_ctor_set(v___x_4558_, 1, v_waiters_4535_);
lean_ctor_set(v___x_4558_, 2, v_capacity_4536_);
lean_ctor_set(v___x_4558_, 3, v_size_4537_);
lean_ctor_set(v___x_4558_, 4, v_buffer_4538_);
lean_ctor_set(v___x_4558_, 5, v_write_4539_);
lean_ctor_set(v___x_4558_, 6, v_read_4540_);
lean_ctor_set(v___x_4558_, 7, v_receivers_4541_);
lean_ctor_set(v___x_4558_, 8, v_nextId_4542_);
lean_ctor_set(v___x_4558_, 9, v_pos_4544_);
lean_ctor_set_uint8(v___x_4558_, sizeof(void*)*10, v_closed_4543_);
v___x_4559_ = lean_box(0);
lean_inc(v_a_4546_);
v___x_4560_ = lean_apply_4(v___f_4545_, v___x_4559_, v___x_4558_, v_a_4546_, lean_box(0));
return v___x_4560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4561_, lean_object* v_waiters_4562_, lean_object* v_capacity_4563_, lean_object* v_size_4564_, lean_object* v_buffer_4565_, lean_object* v_write_4566_, lean_object* v_read_4567_, lean_object* v_receivers_4568_, lean_object* v_nextId_4569_, lean_object* v_closed_4570_, lean_object* v_pos_4571_, lean_object* v___f_4572_, lean_object* v_a_4573_, lean_object* v_x_4574_, lean_object* v___y_4575_){
_start:
{
uint8_t v_closed_boxed_4576_; lean_object* v_res_4577_; 
v_closed_boxed_4576_ = lean_unbox(v_closed_4570_);
v_res_4577_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4561_, v_waiters_4562_, v_capacity_4563_, v_size_4564_, v_buffer_4565_, v_write_4566_, v_read_4567_, v_receivers_4568_, v_nextId_4569_, v_closed_boxed_4576_, v_pos_4571_, v___f_4572_, v_a_4573_, v_x_4574_);
lean_dec(v_a_4573_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4578_, lean_object* v_x_4579_){
_start:
{
if (lean_obj_tag(v_x_4579_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4589_; 
lean_dec(v_fst_4578_);
v_a_4581_ = lean_ctor_get(v_x_4579_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v_x_4579_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4583_ = v_x_4579_;
v_isShared_4584_ = v_isSharedCheck_4589_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v_x_4579_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4589_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4581_);
v___x_4586_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4587_; 
v___x_4587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4586_);
return v___x_4587_;
}
}
}
else
{
lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4597_; 
v_isSharedCheck_4597_ = !lean_is_exclusive(v_x_4579_);
if (v_isSharedCheck_4597_ == 0)
{
lean_object* v_unused_4598_; 
v_unused_4598_ = lean_ctor_get(v_x_4579_, 0);
lean_dec(v_unused_4598_);
v___x_4591_ = v_x_4579_;
v_isShared_4592_ = v_isSharedCheck_4597_;
goto v_resetjp_4590_;
}
else
{
lean_dec(v_x_4579_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4597_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 0, v_fst_4578_);
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_fst_4578_);
v___x_4594_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4595_; 
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
return v___x_4595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4599_, lean_object* v_x_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4599_, v_x_4600_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, uint8_t v___x_4606_, lean_object* v_x_4607_){
_start:
{
if (lean_obj_tag(v_x_4607_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4617_; 
lean_dec_ref(v_a_4604_);
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
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4665_; 
v_a_4618_ = lean_ctor_get(v_x_4607_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v_x_4607_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4620_ = v_x_4607_;
v_isShared_4621_ = v_isSharedCheck_4665_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v_x_4607_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4665_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v_fst_4622_; 
v_fst_4622_ = lean_ctor_get(v_a_4618_, 0);
lean_inc(v_fst_4622_);
if (lean_obj_tag(v_fst_4622_) == 1)
{
lean_object* v_snd_4623_; lean_object* v___f_4624_; lean_object* v___x_4625_; lean_object* v___f_4626_; uint8_t v___x_4627_; 
v_snd_4623_ = lean_ctor_get(v_a_4618_, 1);
lean_inc(v_snd_4623_);
lean_dec(v_a_4618_);
v___f_4624_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4624_, 0, v_fst_4622_);
v___x_4625_ = lean_box(v_a_4603_);
lean_inc_ref(v___f_4624_);
v___f_4626_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4626_, 0, v___x_4625_);
lean_closure_set(v___f_4626_, 1, v___f_4624_);
v___x_4627_ = lean_unbox(v_snd_4623_);
lean_dec(v_snd_4623_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; lean_object* v___x_4629_; 
lean_dec_ref(v___f_4626_);
lean_del_object(v___x_4620_);
v___x_4628_ = lean_box(0);
v___x_4629_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4603_, v___f_4624_, v___x_4628_, v_a_4604_, v_a_4605_);
return v___x_4629_;
}
else
{
lean_object* v___x_4630_; lean_object* v_producers_4631_; lean_object* v_waiters_4632_; lean_object* v_capacity_4633_; lean_object* v_size_4634_; lean_object* v_buffer_4635_; lean_object* v_write_4636_; lean_object* v_read_4637_; lean_object* v_receivers_4638_; lean_object* v_nextId_4639_; uint8_t v_closed_4640_; lean_object* v_pos_4641_; lean_object* v___x_4642_; 
v___x_4630_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4604_);
v_producers_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc_ref(v_producers_4631_);
v_waiters_4632_ = lean_ctor_get(v___x_4630_, 1);
lean_inc_ref(v_waiters_4632_);
v_capacity_4633_ = lean_ctor_get(v___x_4630_, 2);
lean_inc(v_capacity_4633_);
v_size_4634_ = lean_ctor_get(v___x_4630_, 3);
lean_inc(v_size_4634_);
v_buffer_4635_ = lean_ctor_get(v___x_4630_, 4);
lean_inc_ref(v_buffer_4635_);
v_write_4636_ = lean_ctor_get(v___x_4630_, 5);
lean_inc(v_write_4636_);
v_read_4637_ = lean_ctor_get(v___x_4630_, 6);
lean_inc(v_read_4637_);
v_receivers_4638_ = lean_ctor_get(v___x_4630_, 7);
lean_inc(v_receivers_4638_);
v_nextId_4639_ = lean_ctor_get(v___x_4630_, 8);
lean_inc(v_nextId_4639_);
v_closed_4640_ = lean_ctor_get_uint8(v___x_4630_, sizeof(void*)*10);
v_pos_4641_ = lean_ctor_get(v___x_4630_, 9);
lean_inc(v_pos_4641_);
v___x_4642_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4631_);
if (lean_obj_tag(v___x_4642_) == 1)
{
lean_object* v_val_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4661_; 
lean_dec_ref(v___x_4630_);
lean_dec_ref(v___f_4624_);
v_val_4643_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4645_ = v___x_4642_;
v_isShared_4646_ = v_isSharedCheck_4661_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_val_4643_);
lean_dec(v___x_4642_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4661_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v_fst_4647_; lean_object* v_snd_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___f_4652_; lean_object* v___x_4654_; 
v_fst_4647_ = lean_ctor_get(v_val_4643_, 0);
lean_inc(v_fst_4647_);
v_snd_4648_ = lean_ctor_get(v_val_4643_, 1);
lean_inc(v_snd_4648_);
lean_dec(v_val_4643_);
v___x_4649_ = lean_box(v___x_4606_);
v___x_4650_ = lean_io_promise_resolve(v___x_4649_, v_fst_4647_);
lean_dec(v_fst_4647_);
v___x_4651_ = lean_box(v_closed_4640_);
lean_inc(v_a_4605_);
v___f_4652_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4652_, 0, v_snd_4648_);
lean_closure_set(v___f_4652_, 1, v_waiters_4632_);
lean_closure_set(v___f_4652_, 2, v_capacity_4633_);
lean_closure_set(v___f_4652_, 3, v_size_4634_);
lean_closure_set(v___f_4652_, 4, v_buffer_4635_);
lean_closure_set(v___f_4652_, 5, v_write_4636_);
lean_closure_set(v___f_4652_, 6, v_read_4637_);
lean_closure_set(v___f_4652_, 7, v_receivers_4638_);
lean_closure_set(v___f_4652_, 8, v_nextId_4639_);
lean_closure_set(v___f_4652_, 9, v___x_4651_);
lean_closure_set(v___f_4652_, 10, v_pos_4641_);
lean_closure_set(v___f_4652_, 11, v___f_4626_);
lean_closure_set(v___f_4652_, 12, v_a_4605_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 0, v___x_4650_);
v___x_4654_ = v___x_4620_;
goto v_reusejp_4653_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v___x_4650_);
v___x_4654_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4653_;
}
v_reusejp_4653_:
{
lean_object* v___x_4656_; 
if (v_isShared_4646_ == 0)
{
lean_ctor_set_tag(v___x_4645_, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4654_);
v___x_4656_ = v___x_4645_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4654_);
v___x_4656_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_unsigned_to_nat(0u);
v___x_4658_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4657_, v_a_4603_, v___x_4656_, v___f_4652_);
return v___x_4658_;
}
}
}
}
else
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
lean_dec(v___x_4642_);
lean_dec(v_pos_4641_);
lean_dec(v_nextId_4639_);
lean_dec(v_receivers_4638_);
lean_dec(v_read_4637_);
lean_dec(v_write_4636_);
lean_dec_ref(v_buffer_4635_);
lean_dec(v_size_4634_);
lean_dec(v_capacity_4633_);
lean_dec_ref(v_waiters_4632_);
lean_dec_ref(v___f_4626_);
lean_del_object(v___x_4620_);
v___x_4662_ = lean_box(0);
v___x_4663_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4603_, v___f_4624_, v___x_4662_, v___x_4630_, v_a_4605_);
return v___x_4663_;
}
}
}
else
{
lean_object* v___x_4664_; 
lean_dec(v_fst_4622_);
lean_del_object(v___x_4620_);
lean_dec(v_a_4618_);
lean_dec_ref(v_a_4604_);
v___x_4664_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v___x_4669_, lean_object* v_x_4670_, lean_object* v___y_4671_){
_start:
{
uint8_t v_a_12397__boxed_4672_; uint8_t v___x_12399__boxed_4673_; lean_object* v_res_4674_; 
v_a_12397__boxed_4672_ = lean_unbox(v_a_4666_);
v___x_12399__boxed_4673_ = lean_unbox(v___x_4669_);
v_res_4674_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12397__boxed_4672_, v_a_4667_, v_a_4668_, v___x_12399__boxed_4673_, v_x_4670_);
lean_dec(v_a_4668_);
return v_res_4674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4675_, lean_object* v_next_4676_, lean_object* v_a_4677_, lean_object* v_x_4678_){
_start:
{
if (lean_obj_tag(v_x_4678_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4688_; 
lean_dec(v_next_4676_);
lean_dec_ref(v_a_4675_);
v_a_4680_ = lean_ctor_get(v_x_4678_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_x_4678_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4682_ = v_x_4678_;
v_isShared_4683_ = v_isSharedCheck_4688_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v_x_4678_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4688_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4683_ == 0)
{
v___x_4685_ = v___x_4682_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
lean_object* v___x_4686_; 
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
return v___x_4686_;
}
}
}
else
{
lean_object* v_a_4689_; uint8_t v___x_4690_; 
v_a_4689_ = lean_ctor_get(v_x_4678_, 0);
lean_inc(v_a_4689_);
lean_dec_ref_known(v_x_4678_, 1);
v___x_4690_ = lean_unbox(v_a_4689_);
if (v___x_4690_ == 0)
{
lean_object* v_capacity_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; uint8_t v___x_4694_; lean_object* v___x_4695_; lean_object* v___f_4696_; lean_object* v___f_4697_; lean_object* v___x_4698_; uint8_t v___x_4699_; lean_object* v___x_4700_; 
v_capacity_4691_ = lean_ctor_get(v_a_4675_, 2);
v___x_4692_ = lean_nat_mod(v_next_4676_, v_capacity_4691_);
v___x_4693_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4692_, v_a_4677_);
v___x_4694_ = 1;
v___x_4695_ = lean_box(v___x_4694_);
lean_inc(v_a_4677_);
lean_inc_n(v_a_4689_, 2);
v___f_4696_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4696_, 0, v_a_4689_);
lean_closure_set(v___f_4696_, 1, v_a_4675_);
lean_closure_set(v___f_4696_, 2, v_a_4677_);
lean_closure_set(v___f_4696_, 3, v___x_4695_);
v___f_4697_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4697_, 0, v_next_4676_);
lean_closure_set(v___f_4697_, 1, v_a_4689_);
lean_closure_set(v___f_4697_, 2, v___f_4696_);
v___x_4698_ = lean_unsigned_to_nat(0u);
v___x_4699_ = lean_unbox(v_a_4689_);
lean_dec(v_a_4689_);
v___x_4700_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4698_, v___x_4699_, v___x_4693_, v___f_4697_);
return v___x_4700_;
}
else
{
lean_object* v___x_4701_; 
lean_dec(v_a_4689_);
lean_dec(v_next_4676_);
lean_dec_ref(v_a_4675_);
v___x_4701_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4701_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4702_, lean_object* v_next_4703_, lean_object* v_a_4704_, lean_object* v_x_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4702_, v_next_4703_, v_a_4704_, v_x_4705_);
lean_dec(v_a_4704_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4708_, lean_object* v_next_4709_, lean_object* v_x_4710_){
_start:
{
if (lean_obj_tag(v_x_4710_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4720_; 
lean_dec(v_next_4709_);
v_a_4712_ = lean_ctor_get(v_x_4710_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v_x_4710_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4714_ = v_x_4710_;
v_isShared_4715_ = v_isSharedCheck_4720_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v_x_4710_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4720_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4718_; 
v___x_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4717_);
return v___x_4718_;
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4722_; lean_object* v___f_4723_; lean_object* v___x_4724_; uint8_t v___x_4725_; lean_object* v___x_4726_; 
v_a_4721_ = lean_ctor_get(v_x_4710_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v_x_4710_, 1);
v___x_4722_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4708_);
lean_inc(v_a_4708_);
v___f_4723_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4723_, 0, v_a_4721_);
lean_closure_set(v___f_4723_, 1, v_next_4709_);
lean_closure_set(v___f_4723_, 2, v_a_4708_);
v___x_4724_ = lean_unsigned_to_nat(0u);
v___x_4725_ = 0;
v___x_4726_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4724_, v___x_4725_, v___x_4722_, v___f_4723_);
return v___x_4726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4727_, lean_object* v_next_4728_, lean_object* v_x_4729_, lean_object* v___y_4730_){
_start:
{
lean_object* v_res_4731_; 
v_res_4731_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4727_, v_next_4728_, v_x_4729_);
lean_dec(v_a_4727_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v___x_4735_; lean_object* v___f_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; lean_object* v___x_4741_; 
v___x_4735_ = lean_st_ref_get(v_a_4733_);
lean_inc(v_a_4733_);
v___f_4736_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4736_, 0, v_a_4733_);
lean_closure_set(v___f_4736_, 1, v_next_4732_);
v___x_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4735_);
v___x_4738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
v___x_4739_ = lean_unsigned_to_nat(0u);
v___x_4740_ = 0;
v___x_4741_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4739_, v___x_4740_, v___x_4738_, v___f_4736_);
return v___x_4741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4742_, lean_object* v_a_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4742_, v_a_4743_);
lean_dec(v_a_4743_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4746_, lean_object* v_a_4747_, lean_object* v_x_4748_){
_start:
{
if (lean_obj_tag(v_x_4748_) == 0)
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4758_; 
lean_dec(v_receiverId_4746_);
v_a_4750_ = lean_ctor_get(v_x_4748_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v_x_4748_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4752_ = v_x_4748_;
v_isShared_4753_ = v_isSharedCheck_4758_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v_x_4748_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4758_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
lean_object* v___x_4756_; 
v___x_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
return v___x_4756_;
}
}
}
else
{
lean_object* v_a_4759_; lean_object* v_receivers_4760_; lean_object* v___x_4761_; 
v_a_4759_ = lean_ctor_get(v_x_4748_, 0);
lean_inc(v_a_4759_);
lean_dec_ref_known(v_x_4748_, 1);
v_receivers_4760_ = lean_ctor_get(v_a_4759_, 7);
lean_inc(v_receivers_4760_);
lean_dec(v_a_4759_);
v___x_4761_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4760_, v_receiverId_4746_);
if (lean_obj_tag(v___x_4761_) == 1)
{
lean_object* v_val_4762_; lean_object* v___x_4763_; lean_object* v___f_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; lean_object* v___x_4767_; 
v_val_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_val_4762_);
lean_dec_ref_known(v___x_4761_, 1);
v___x_4763_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4762_, v_a_4747_);
lean_inc(v_a_4747_);
v___f_4764_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4764_, 0, v_a_4747_);
lean_closure_set(v___f_4764_, 1, v_receiverId_4746_);
lean_closure_set(v___f_4764_, 2, v_receivers_4760_);
v___x_4765_ = lean_unsigned_to_nat(0u);
v___x_4766_ = 0;
v___x_4767_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4765_, v___x_4766_, v___x_4763_, v___f_4764_);
return v___x_4767_;
}
else
{
lean_object* v___x_4768_; 
lean_dec(v___x_4761_);
lean_dec(v_receivers_4760_);
lean_dec(v_receiverId_4746_);
v___x_4768_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4768_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4769_, lean_object* v_a_4770_, lean_object* v_x_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4769_, v_a_4770_, v_x_4771_);
lean_dec(v_a_4770_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4774_, lean_object* v_a_4775_){
_start:
{
lean_object* v___x_4777_; lean_object* v___f_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4783_; 
v___x_4777_ = lean_st_ref_get(v_a_4775_);
lean_inc(v_a_4775_);
v___f_4778_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4778_, 0, v_receiverId_4774_);
lean_closure_set(v___f_4778_, 1, v_a_4775_);
v___x_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4777_);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
v___x_4781_ = lean_unsigned_to_nat(0u);
v___x_4782_ = 0;
v___x_4783_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4781_, v___x_4782_, v___x_4780_, v___f_4778_);
return v___x_4783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4784_, lean_object* v_a_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4784_, v_a_4785_);
lean_dec(v_a_4785_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4792_, lean_object* v___y_4793_, lean_object* v___f_4794_, lean_object* v_x_4795_){
_start:
{
if (lean_obj_tag(v_x_4795_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4805_; 
lean_dec_ref(v___f_4794_);
lean_dec(v_id_4792_);
v_a_4797_ = lean_ctor_get(v_x_4795_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v_x_4795_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4799_ = v_x_4795_;
v_isShared_4800_ = v_isSharedCheck_4805_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v_x_4795_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4805_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4797_);
v___x_4802_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4803_; 
v___x_4803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4802_);
return v___x_4803_;
}
}
}
else
{
lean_object* v_a_4806_; uint8_t v___x_4807_; 
v_a_4806_ = lean_ctor_get(v_x_4795_, 0);
lean_inc(v_a_4806_);
lean_dec_ref_known(v_x_4795_, 1);
v___x_4807_ = lean_unbox(v_a_4806_);
lean_dec(v_a_4806_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; 
lean_dec_ref(v___f_4794_);
lean_dec(v_id_4792_);
v___x_4808_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1));
return v___x_4808_;
}
else
{
lean_object* v___x_4809_; lean_object* v___x_4810_; uint8_t v___x_4811_; lean_object* v___x_4812_; 
v___x_4809_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4792_, v___y_4793_);
v___x_4810_ = lean_unsigned_to_nat(0u);
v___x_4811_ = 0;
v___x_4812_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4810_, v___x_4811_, v___x_4809_, v___f_4794_);
return v___x_4812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4813_, lean_object* v___y_4814_, lean_object* v___f_4815_, lean_object* v_x_4816_, lean_object* v___y_4817_){
_start:
{
lean_object* v_res_4818_; 
v_res_4818_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4813_, v___y_4814_, v___f_4815_, v_x_4816_);
lean_dec(v___y_4814_);
return v_res_4818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4819_, lean_object* v___f_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; lean_object* v___f_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; uint8_t v___x_4828_; lean_object* v___x_4829_; lean_object* v___f_4830_; lean_object* v___x_4831_; 
v___x_4823_ = lean_st_ref_get(v___y_4821_);
lean_inc_n(v___y_4821_, 2);
lean_inc(v_id_4819_);
v___f_4824_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_4824_, 0, v_id_4819_);
lean_closure_set(v___f_4824_, 1, v___y_4821_);
v___x_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4823_);
v___x_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
v___x_4827_ = lean_unsigned_to_nat(0u);
v___x_4828_ = 0;
v___x_4829_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4827_, v___x_4828_, v___x_4826_, v___f_4824_);
v___f_4830_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4830_, 0, v_id_4819_);
lean_closure_set(v___f_4830_, 1, v___y_4821_);
lean_closure_set(v___f_4830_, 2, v___f_4820_);
v___x_4831_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4827_, v___x_4828_, v___x_4829_, v___f_4830_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4832_, lean_object* v___f_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4832_, v___f_4833_, v___y_4834_);
lean_dec(v___y_4834_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4839_){
_start:
{
lean_object* v_state_4840_; lean_object* v_id_4841_; lean_object* v___f_4842_; lean_object* v___f_4843_; lean_object* v___f_4844_; lean_object* v___f_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v_state_4840_ = lean_ctor_get(v_ch_4839_, 0);
lean_inc_ref_n(v_state_4840_, 2);
v_id_4841_ = lean_ctor_get(v_ch_4839_, 1);
lean_inc(v_id_4841_);
v___f_4842_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4843_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4843_, 0, v_ch_4839_);
v___f_4844_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4845_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4845_, 0, v_id_4841_);
lean_closure_set(v___f_4845_, 1, v___f_4844_);
v___x_4846_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4846_, 0, lean_box(0));
lean_closure_set(v___x_4846_, 1, lean_box(0));
lean_closure_set(v___x_4846_, 2, v_state_4840_);
lean_closure_set(v___x_4846_, 3, v___f_4845_);
v___x_4847_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4847_, 0, lean_box(0));
lean_closure_set(v___x_4847_, 1, lean_box(0));
lean_closure_set(v___x_4847_, 2, v_state_4840_);
lean_closure_set(v___x_4847_, 3, v___f_4842_);
v___x_4848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4846_);
lean_ctor_set(v___x_4848_, 1, v___f_4843_);
lean_ctor_set(v___x_4848_, 2, v___x_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4849_, lean_object* v_ch_4850_){
_start:
{
lean_object* v___x_4851_; 
v___x_4851_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4850_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4852_, lean_object* v_receiverId_4853_, lean_object* v_a_4854_){
_start:
{
lean_object* v___x_4856_; 
v___x_4856_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4853_, v_a_4854_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4857_, lean_object* v_receiverId_4858_, lean_object* v_a_4859_, lean_object* v___y_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4857_, v_receiverId_4858_, v_a_4859_);
lean_dec(v_a_4859_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4862_, lean_object* v_q_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4863_, v___y_4864_);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4867_, lean_object* v_q_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v_res_4871_; 
v_res_4871_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4867_, v_q_4868_, v___y_4869_);
lean_dec(v___y_4869_);
return v_res_4871_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4872_, lean_object* v_slot_4873_, lean_object* v_next_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4873_, v_next_4874_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4878_, lean_object* v_slot_4879_, lean_object* v_next_4880_, lean_object* v_a_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4878_, v_slot_4879_, v_next_4880_, v_a_4881_);
lean_dec(v_a_4881_);
lean_dec(v_next_4880_);
lean_dec(v_slot_4879_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v___x_4887_; 
v___x_4887_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4885_);
return v___x_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4888_, lean_object* v_a_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v_res_4891_; 
v_res_4891_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4888_, v_a_4889_);
lean_dec(v_a_4889_);
return v_res_4891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4892_, lean_object* v_next_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v___x_4896_; 
v___x_4896_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4893_, v_a_4894_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4897_, lean_object* v_next_4898_, lean_object* v_a_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4897_, v_next_4898_, v_a_4899_);
lean_dec(v_a_4899_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4902_, lean_object* v_x_4903_, lean_object* v_x_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4903_, v_x_4904_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4908_, lean_object* v_x_4909_, lean_object* v_x_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4908_, v_x_4909_, v_x_4910_, v___y_4911_);
lean_dec(v___y_4911_);
return v_res_4913_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4915_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4915_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4918_, lean_object* v_a_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_Std_Broadcast_new___redArg(v_capacity_4918_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4921_, lean_object* v_capacity_4922_, lean_object* v_h_4923_){
_start:
{
lean_object* v___x_4925_; 
v___x_4925_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4922_);
return v___x_4925_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4926_, lean_object* v_capacity_4927_, lean_object* v_h_4928_, lean_object* v_a_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_Std_Broadcast_new(v_00_u03b1_4926_, v_capacity_4927_, v_h_4928_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4931_, lean_object* v_v_4932_){
_start:
{
lean_object* v___x_4934_; 
v___x_4934_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4931_, v_v_4932_);
return v___x_4934_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4935_, lean_object* v_v_4936_, lean_object* v_a_4937_){
_start:
{
lean_object* v_res_4938_; 
v_res_4938_ = l_Std_Broadcast_trySend___redArg(v_ch_4935_, v_v_4936_);
return v_res_4938_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4939_, lean_object* v_ch_4940_, lean_object* v_v_4941_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4940_, v_v_4941_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4944_, lean_object* v_ch_4945_, lean_object* v_v_4946_, lean_object* v_a_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l_Std_Broadcast_trySend(v_00_u03b1_4944_, v_ch_4945_, v_v_4946_);
return v_res_4948_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4949_){
_start:
{
lean_object* v___x_4951_; 
v___x_4951_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4949_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4951_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4951_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
else
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
v_a_4960_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4951_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4951_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
if (v_isShared_4963_ == 0)
{
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4960_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_4968_, lean_object* v_a_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Std_Broadcast_subscribe___redArg(v_ch_4968_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_4971_, lean_object* v_ch_4972_){
_start:
{
lean_object* v___x_4974_; 
v___x_4974_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4972_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4982_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4977_ = v___x_4974_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4974_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
else
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4990_; 
v_a_4983_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4990_ == 0)
{
v___x_4985_ = v___x_4974_;
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4974_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4988_; 
if (v_isShared_4986_ == 0)
{
v___x_4988_ = v___x_4985_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_a_4983_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_4991_, lean_object* v_ch_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Std_Broadcast_subscribe(v_00_u03b1_4991_, v_ch_4992_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_4995_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_4995_);
if (lean_obj_tag(v___x_4997_) == 0)
{
lean_object* v_a_4998_; lean_object* v___x_5000_; uint8_t v_isShared_5001_; uint8_t v_isSharedCheck_5005_; 
v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_5000_ = v___x_4997_;
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
else
{
lean_inc(v_a_4998_);
lean_dec(v___x_4997_);
v___x_5000_ = lean_box(0);
v_isShared_5001_ = v_isSharedCheck_5005_;
goto v_resetjp_4999_;
}
v_resetjp_4999_:
{
lean_object* v___x_5003_; 
if (v_isShared_5001_ == 0)
{
v___x_5003_ = v___x_5000_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v_a_4998_);
v___x_5003_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
return v___x_5003_;
}
}
}
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5023_; 
v_a_5006_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5008_ = v___x_4997_;
v_isShared_5009_ = v_isSharedCheck_5023_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4997_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5023_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
uint8_t v___x_5010_; 
v___x_5010_ = lean_unbox(v_a_5006_);
lean_dec(v_a_5006_);
switch(v___x_5010_)
{
case 0:
{
lean_object* v___x_5011_; lean_object* v___x_5013_; 
v___x_5011_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5011_);
v___x_5013_ = v___x_5008_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5011_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
case 1:
{
lean_object* v___x_5015_; lean_object* v___x_5017_; 
v___x_5015_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5015_);
v___x_5017_ = v___x_5008_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5015_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
default: 
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5019_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5019_);
v___x_5021_ = v___x_5008_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5019_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5024_, lean_object* v_a_5025_){
_start:
{
lean_object* v_res_5026_; 
v_res_5026_ = l_Std_Broadcast_close___redArg(v_ch_5024_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5027_, lean_object* v_ch_5028_){
_start:
{
lean_object* v___x_5030_; 
v___x_5030_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5028_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5038_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5033_ = v___x_5030_;
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_a_5031_);
lean_dec(v___x_5030_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5038_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v_a_5031_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5056_; 
v_a_5039_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5041_ = v___x_5030_;
v_isShared_5042_ = v_isSharedCheck_5056_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5030_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5056_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
uint8_t v___x_5043_; 
v___x_5043_ = lean_unbox(v_a_5039_);
lean_dec(v_a_5039_);
switch(v___x_5043_)
{
case 0:
{
lean_object* v___x_5044_; lean_object* v___x_5046_; 
v___x_5044_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5044_);
v___x_5046_ = v___x_5041_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v___x_5044_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
case 1:
{
lean_object* v___x_5048_; lean_object* v___x_5050_; 
v___x_5048_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5048_);
v___x_5050_ = v___x_5041_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5048_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
default: 
{
lean_object* v___x_5052_; lean_object* v___x_5054_; 
v___x_5052_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 0, v___x_5052_);
v___x_5054_ = v___x_5041_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5052_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5057_, lean_object* v_ch_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_Std_Broadcast_close(v_00_u03b1_5057_, v_ch_5058_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5061_){
_start:
{
lean_object* v___y_5064_; 
if (lean_obj_tag(v_x_5061_) == 0)
{
lean_object* v_a_5068_; uint8_t v___x_5069_; 
v_a_5068_ = lean_ctor_get(v_x_5061_, 0);
lean_inc(v_a_5068_);
lean_dec_ref_known(v_x_5061_, 1);
v___x_5069_ = lean_unbox(v_a_5068_);
lean_dec(v_a_5068_);
switch(v___x_5069_)
{
case 0:
{
lean_object* v___x_5070_; 
v___x_5070_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5064_ = v___x_5070_;
goto v___jp_5063_;
}
case 1:
{
lean_object* v___x_5071_; 
v___x_5071_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5064_ = v___x_5071_;
goto v___jp_5063_;
}
default: 
{
lean_object* v___x_5072_; 
v___x_5072_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5064_ = v___x_5072_;
goto v___jp_5063_;
}
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5081_; 
v_a_5073_ = lean_ctor_get(v_x_5061_, 0);
v_isSharedCheck_5081_ = !lean_is_exclusive(v_x_5061_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5075_ = v_x_5061_;
v_isShared_5076_ = v_isSharedCheck_5081_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v_x_5061_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5081_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
lean_object* v___x_5079_; 
v___x_5079_ = lean_task_pure(v___x_5078_);
return v___x_5079_;
}
}
}
v___jp_5063_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
lean_inc_ref(v___y_5064_);
v___x_5065_ = lean_mk_io_user_error(v___y_5064_);
v___x_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5066_, 0, v___x_5065_);
v___x_5067_ = lean_task_pure(v___x_5066_);
return v___x_5067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5082_, lean_object* v___y_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5082_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5086_, lean_object* v_v_5087_){
_start:
{
lean_object* v___x_5089_; lean_object* v___f_5090_; lean_object* v___x_5091_; uint8_t v___x_5092_; lean_object* v___x_5093_; 
v___x_5089_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5086_, v_v_5087_);
v___f_5090_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5091_ = lean_unsigned_to_nat(0u);
v___x_5092_ = 1;
v___x_5093_ = lean_io_bind_task(v___x_5089_, v___f_5090_, v___x_5091_, v___x_5092_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5094_, lean_object* v_v_5095_, lean_object* v_a_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l_Std_Broadcast_send___redArg(v_ch_5094_, v_v_5095_);
return v_res_5097_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5098_, lean_object* v_ch_5099_, lean_object* v_v_5100_){
_start:
{
lean_object* v___x_5102_; lean_object* v___f_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; lean_object* v___x_5106_; 
v___x_5102_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5099_, v_v_5100_);
v___f_5103_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5104_ = lean_unsigned_to_nat(0u);
v___x_5105_ = 1;
v___x_5106_ = lean_io_bind_task(v___x_5102_, v___f_5103_, v___x_5104_, v___x_5105_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5107_, lean_object* v_ch_5108_, lean_object* v_v_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Std_Broadcast_send(v_00_u03b1_5107_, v_ch_5108_, v_v_5109_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5112_){
_start:
{
lean_object* v___x_5114_; 
v___x_5114_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5112_);
return v___x_5114_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5115_, lean_object* v_a_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5115_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5118_, lean_object* v_ch_5119_){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5119_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5122_, lean_object* v_ch_5123_, lean_object* v_a_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5122_, v_ch_5123_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5126_){
_start:
{
lean_object* v___x_5128_; 
v___x_5128_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5126_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5129_, lean_object* v_a_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5129_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5132_, lean_object* v_inst_5133_, lean_object* v_ch_5134_){
_start:
{
lean_object* v___x_5136_; 
v___x_5136_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5134_);
return v___x_5136_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5137_, lean_object* v_inst_5138_, lean_object* v_ch_5139_, lean_object* v_a_5140_){
_start:
{
lean_object* v_res_5141_; 
v_res_5141_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5137_, v_inst_5138_, v_ch_5139_);
lean_dec(v_inst_5138_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5142_){
_start:
{
lean_object* v___x_5143_; 
v___x_5143_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5142_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5144_, lean_object* v_inst_5145_, lean_object* v_ch_5146_){
_start:
{
lean_object* v___x_5147_; 
v___x_5147_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5146_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5148_, lean_object* v_inst_5149_, lean_object* v_ch_5150_){
_start:
{
lean_object* v_res_5151_; 
v_res_5151_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5148_, v_inst_5149_, v_ch_5150_);
lean_dec(v_inst_5149_);
return v_res_5151_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5152_){
_start:
{
lean_object* v___x_5154_; 
v___x_5154_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5152_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5155_, lean_object* v_a_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5155_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5158_, lean_object* v_ch_5159_){
_start:
{
lean_object* v___x_5161_; 
v___x_5161_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5159_);
return v___x_5161_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5162_, lean_object* v_ch_5163_, lean_object* v_a_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5162_, v_ch_5163_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5166_, lean_object* v_ch_5167_, lean_object* v_prio_5168_){
_start:
{
lean_object* v___x_5170_; 
v___x_5170_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5166_, v_ch_5167_, v_prio_5168_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5171_, lean_object* v_ch_5172_, lean_object* v_prio_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5171_, v_ch_5172_, v_prio_5173_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5176_, lean_object* v_f_5177_, lean_object* v_ch_5178_, lean_object* v_prio_5179_){
_start:
{
lean_object* v___x_5181_; 
v___x_5181_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5177_, v_ch_5178_, v_prio_5179_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5182_, lean_object* v_f_5183_, lean_object* v_ch_5184_, lean_object* v_prio_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5182_, v_f_5183_, v_ch_5184_, v_prio_5185_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5193_, lean_object* v_inst_5194_){
_start:
{
lean_object* v___x_5195_; 
v___x_5195_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5196_, lean_object* v_inst_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5196_, v_inst_5197_);
lean_dec(v_inst_5197_);
return v_res_5198_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_5199_){
_start:
{
lean_object* v___x_5200_; 
v___x_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5200_, 0, v_a_5199_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_5201_, lean_object* v_x_5202_){
_start:
{
if (lean_obj_tag(v_x_5202_) == 0)
{
lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5212_; 
lean_dec_ref(v___f_5201_);
v_a_5204_ = lean_ctor_get(v_x_5202_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v_x_5202_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5206_ = v_x_5202_;
v_isShared_5207_ = v_isSharedCheck_5212_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v_x_5202_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5212_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5209_; 
if (v_isShared_5207_ == 0)
{
v___x_5209_ = v___x_5206_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5204_);
v___x_5209_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
lean_object* v___x_5210_; 
v___x_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5209_);
return v___x_5210_;
}
}
}
else
{
lean_object* v_a_5213_; 
v_a_5213_ = lean_ctor_get(v_x_5202_, 0);
lean_inc(v_a_5213_);
lean_dec_ref_known(v_x_5202_, 1);
if (lean_obj_tag(v_a_5213_) == 0)
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5222_; 
lean_dec_ref(v___f_5201_);
v_a_5214_ = lean_ctor_get(v_a_5213_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v_a_5213_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5216_ = v_a_5213_;
v_isShared_5217_ = v_isSharedCheck_5222_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v_a_5213_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5222_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5219_; 
if (v_isShared_5217_ == 0)
{
v___x_5219_ = v___x_5216_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5221_; 
v_reuseFailAlloc_5221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5214_);
v___x_5219_ = v_reuseFailAlloc_5221_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
lean_object* v___x_5220_; 
v___x_5220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5219_);
return v___x_5220_;
}
}
}
else
{
lean_object* v_a_5223_; lean_object* v___x_5224_; uint8_t v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v_a_5223_ = lean_ctor_get(v_a_5213_, 0);
lean_inc(v_a_5223_);
lean_dec_ref_known(v_a_5213_, 1);
v___x_5224_ = lean_unsigned_to_nat(0u);
v___x_5225_ = 0;
v___x_5226_ = lean_task_map(v___f_5201_, v_a_5223_, v___x_5224_, v___x_5225_);
v___x_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5227_, 0, v___x_5226_);
return v___x_5227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_5228_, lean_object* v_x_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(v___f_5228_, v_x_5229_);
return v_res_5231_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_5232_, lean_object* v_receiver_5233_){
_start:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; uint8_t v___x_5240_; lean_object* v___x_5241_; 
v___x_5235_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5233_);
v___x_5236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5235_);
v___x_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5236_);
v___x_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5237_);
v___x_5239_ = lean_unsigned_to_nat(0u);
v___x_5240_ = 0;
v___x_5241_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5239_, v___x_5240_, v___x_5238_, v___f_5232_);
return v___x_5241_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_5242_, lean_object* v_receiver_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(v___f_5242_, v_receiver_5243_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5251_, lean_object* v_inst_5252_){
_start:
{
lean_object* v___f_5253_; 
v___f_5253_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2));
return v___f_5253_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5254_, lean_object* v_inst_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5254_, v_inst_5255_);
lean_dec(v_inst_5255_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__1(lean_object* v_a_5257_){
_start:
{
lean_object* v___x_5258_; 
v___x_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5258_, 0, v_a_5257_);
return v___x_5258_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_5263_, lean_object* v_x_5264_){
_start:
{
if (lean_obj_tag(v_x_5264_) == 0)
{
lean_object* v_a_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5274_; 
lean_dec_ref(v___f_5263_);
v_a_5266_ = lean_ctor_get(v_x_5264_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v_x_5264_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5268_ = v_x_5264_;
v_isShared_5269_ = v_isSharedCheck_5274_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_a_5266_);
lean_dec(v_x_5264_);
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
lean_object* v_a_5275_; lean_object* v___x_5276_; uint8_t v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v_a_5275_ = lean_ctor_get(v_x_5264_, 0);
lean_inc(v_a_5275_);
lean_dec_ref_known(v_x_5264_, 1);
v___x_5276_ = lean_unsigned_to_nat(0u);
v___x_5277_ = 0;
v___x_5278_ = lean_task_map(v___f_5263_, v_a_5275_, v___x_5276_, v___x_5277_);
v___x_5279_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1));
v___x_5280_ = lean_task_map(v___x_5279_, v___x_5278_, v___x_5276_, v___x_5277_);
v___x_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5281_, 0, v___x_5280_);
return v___x_5281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_5282_, lean_object* v_x_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(v___f_5282_, v_x_5283_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5286_, lean_object* v___f_5287_, lean_object* v_receiver_5288_, lean_object* v_x_5289_){
_start:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; uint8_t v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; uint8_t v___x_5297_; lean_object* v___x_5298_; 
v___x_5291_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5288_, v_x_5289_);
v___x_5292_ = lean_unsigned_to_nat(0u);
v___x_5293_ = 1;
v___x_5294_ = lean_io_bind_task(v___x_5291_, v___f_5286_, v___x_5292_, v___x_5293_);
v___x_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5294_);
v___x_5296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5295_);
v___x_5297_ = 0;
v___x_5298_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5292_, v___x_5297_, v___x_5296_, v___f_5287_);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5299_, lean_object* v___f_5300_, lean_object* v_receiver_5301_, lean_object* v_x_5302_, lean_object* v___y_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(v___f_5299_, v___f_5300_, v_receiver_5301_, v_x_5302_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(lean_object* v_x_5305_){
_start:
{
lean_object* v___x_5307_; 
v___x_5307_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v_x_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(v_x_5308_);
lean_dec_ref(v_x_5308_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_5311_, lean_object* v_socket_5312_, lean_object* v_x_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v___x_5316_; 
v___x_5316_ = lean_apply_3(v___f_5311_, v_socket_5312_, v___y_5314_, lean_box(0));
return v___x_5316_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_5317_, lean_object* v_socket_5318_, lean_object* v_x_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(v___f_5317_, v_socket_5318_, v_x_5319_, v___y_5320_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(lean_object* v___f_5323_, lean_object* v___x_5324_, lean_object* v_socket_5325_, lean_object* v_data_5326_){
_start:
{
lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; uint8_t v___x_5331_; 
v___x_5328_ = lean_unsigned_to_nat(0u);
v___x_5329_ = lean_array_get_size(v_data_5326_);
v___x_5330_ = lean_box(0);
v___x_5331_ = lean_nat_dec_lt(v___x_5328_, v___x_5329_);
if (v___x_5331_ == 0)
{
lean_object* v___x_5332_; 
lean_dec_ref(v_data_5326_);
lean_dec_ref(v_socket_5325_);
lean_dec_ref(v___x_5324_);
lean_dec_ref(v___f_5323_);
v___x_5332_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5332_;
}
else
{
lean_object* v___f_5333_; uint8_t v___x_5334_; 
v___f_5333_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5333_, 0, v___f_5323_);
lean_closure_set(v___f_5333_, 1, v_socket_5325_);
v___x_5334_ = lean_nat_dec_le(v___x_5329_, v___x_5329_);
if (v___x_5334_ == 0)
{
if (v___x_5331_ == 0)
{
lean_object* v___x_5335_; 
lean_dec_ref(v___f_5333_);
lean_dec_ref(v_data_5326_);
lean_dec_ref(v___x_5324_);
v___x_5335_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5335_;
}
else
{
size_t v___x_5336_; size_t v___x_5337_; lean_object* v___x_899__overap_5338_; lean_object* v___x_5339_; 
v___x_5336_ = ((size_t)0ULL);
v___x_5337_ = lean_usize_of_nat(v___x_5329_);
v___x_899__overap_5338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5324_, v___f_5333_, v_data_5326_, v___x_5336_, v___x_5337_, v___x_5330_);
v___x_5339_ = lean_apply_1(v___x_899__overap_5338_, lean_box(0));
return v___x_5339_;
}
}
else
{
size_t v___x_5340_; size_t v___x_5341_; lean_object* v___x_902__overap_5342_; lean_object* v___x_5343_; 
v___x_5340_ = ((size_t)0ULL);
v___x_5341_ = lean_usize_of_nat(v___x_5329_);
v___x_902__overap_5342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5324_, v___f_5333_, v_data_5326_, v___x_5340_, v___x_5341_, v___x_5330_);
v___x_5343_ = lean_apply_1(v___x_902__overap_5342_, lean_box(0));
return v___x_5343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed(lean_object* v___f_5344_, lean_object* v___x_5345_, lean_object* v_socket_5346_, lean_object* v_data_5347_, lean_object* v___y_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(v___f_5344_, v___x_5345_, v_socket_5346_, v_data_5347_);
return v_res_5349_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_5357_; 
v___x_5357_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_5357_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___x_5358_; lean_object* v___f_5359_; lean_object* v___f_5360_; 
v___x_5358_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4);
v___f_5359_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___f_5360_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed), 5, 2);
lean_closure_set(v___f_5360_, 0, v___f_5359_);
lean_closure_set(v___f_5360_, 1, v___x_5358_);
return v___f_5360_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6(void){
_start:
{
lean_object* v___f_5361_; lean_object* v___f_5362_; lean_object* v___f_5363_; lean_object* v___x_5364_; 
v___f_5361_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3));
v___f_5362_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5);
v___f_5363_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___x_5364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5364_, 0, v___f_5363_);
lean_ctor_set(v___x_5364_, 1, v___f_5362_);
lean_ctor_set(v___x_5364_, 2, v___f_5361_);
return v___x_5364_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5365_, lean_object* v_inst_5366_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6);
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5368_, lean_object* v_inst_5369_){
_start:
{
lean_object* v_res_5370_; 
v_res_5370_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5368_, v_inst_5369_);
lean_dec(v_inst_5369_);
return v_res_5370_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5371_; 
v___x_5371_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5371_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5372_){
_start:
{
lean_object* v___x_5374_; 
v___x_5374_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5372_);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5375_, lean_object* v_a_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5375_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5378_, lean_object* v_capacity_5379_, lean_object* v_h_5380_){
_start:
{
lean_object* v___x_5382_; 
v___x_5382_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5379_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5383_, lean_object* v_capacity_5384_, lean_object* v_h_5385_, lean_object* v_a_5386_){
_start:
{
lean_object* v_res_5387_; 
v_res_5387_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5383_, v_capacity_5384_, v_h_5385_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5388_, lean_object* v_v_5389_){
_start:
{
lean_object* v___x_5391_; 
v___x_5391_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5388_, v_v_5389_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5392_, lean_object* v_v_5393_, lean_object* v_a_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5392_, v_v_5393_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5396_, lean_object* v_ch_5397_, lean_object* v_v_5398_){
_start:
{
lean_object* v___x_5400_; 
v___x_5400_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5397_, v_v_5398_);
return v___x_5400_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5401_, lean_object* v_ch_5402_, lean_object* v_v_5403_, lean_object* v_a_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5401_, v_ch_5402_, v_v_5403_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5407_, lean_object* v_v_5408_){
_start:
{
lean_object* v___x_5410_; lean_object* v___f_5411_; lean_object* v___x_5412_; uint8_t v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5410_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5407_, v_v_5408_);
v___f_5411_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5412_ = lean_unsigned_to_nat(0u);
v___x_5413_ = 1;
v___x_5414_ = lean_io_bind_task(v___x_5410_, v___f_5411_, v___x_5412_, v___x_5413_);
v___x_5415_ = lean_io_wait(v___x_5414_);
v___x_5416_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5417_ = l_IO_ofExcept___redArg(v___x_5416_, v___x_5415_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5418_, lean_object* v_v_5419_, lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5418_, v_v_5419_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5422_, lean_object* v_ch_5423_, lean_object* v_v_5424_){
_start:
{
lean_object* v___x_5426_; lean_object* v___f_5427_; lean_object* v___x_5428_; uint8_t v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5426_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5423_, v_v_5424_);
v___f_5427_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5428_ = lean_unsigned_to_nat(0u);
v___x_5429_ = 1;
v___x_5430_ = lean_io_bind_task(v___x_5426_, v___f_5427_, v___x_5428_, v___x_5429_);
v___x_5431_ = lean_io_wait(v___x_5430_);
v___x_5432_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5433_ = l_IO_ofExcept___redArg(v___x_5432_, v___x_5431_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5434_, lean_object* v_ch_5435_, lean_object* v_v_5436_, lean_object* v_a_5437_){
_start:
{
lean_object* v_res_5438_; 
v_res_5438_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5434_, v_ch_5435_, v_v_5436_);
return v_res_5438_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5439_){
_start:
{
lean_object* v___x_5441_; 
v___x_5441_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5439_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5442_, lean_object* v_a_5443_){
_start:
{
lean_object* v_res_5444_; 
v_res_5444_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5442_);
return v_res_5444_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5445_, lean_object* v_ch_5446_){
_start:
{
lean_object* v___x_5448_; 
v___x_5448_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5446_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5449_, lean_object* v_ch_5450_, lean_object* v_a_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5449_, v_ch_5450_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5453_){
_start:
{
lean_object* v___x_5455_; lean_object* v___x_5456_; 
v___x_5455_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5453_);
v___x_5456_ = lean_io_wait(v___x_5455_);
return v___x_5456_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5457_, lean_object* v_a_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5457_);
return v_res_5459_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5460_, lean_object* v_inst_5461_, lean_object* v_ch_5462_){
_start:
{
lean_object* v___x_5464_; 
v___x_5464_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5462_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5465_, lean_object* v_inst_5466_, lean_object* v_ch_5467_, lean_object* v_a_5468_){
_start:
{
lean_object* v_res_5469_; 
v_res_5469_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5465_, v_inst_5466_, v_ch_5467_);
lean_dec(v_inst_5466_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5470_, lean_object* v_b_5471_, lean_object* v_f_5472_, lean_object* v_toBind_5473_, lean_object* v___f_5474_, lean_object* v_a_5475_){
_start:
{
if (lean_obj_tag(v_a_5475_) == 0)
{
lean_object* v___x_5476_; 
lean_dec(v___f_5474_);
lean_dec(v_toBind_5473_);
lean_dec(v_f_5472_);
v___x_5476_ = lean_apply_2(v_toPure_5470_, lean_box(0), v_b_5471_);
return v___x_5476_;
}
else
{
lean_object* v_val_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; 
lean_dec(v_toPure_5470_);
v_val_5477_ = lean_ctor_get(v_a_5475_, 0);
lean_inc(v_val_5477_);
lean_dec_ref_known(v_a_5475_, 1);
v___x_5478_ = lean_apply_2(v_f_5472_, v_val_5477_, v_b_5471_);
v___x_5479_ = lean_apply_4(v_toBind_5473_, lean_box(0), lean_box(0), v___x_5478_, v___f_5474_);
return v___x_5479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5480_, lean_object* v_inst_5481_, lean_object* v_inst_5482_, lean_object* v_ch_5483_, lean_object* v_f_5484_, lean_object* v_b_5485_){
_start:
{
lean_object* v_toApplicative_5486_; lean_object* v_toBind_5487_; lean_object* v_toPure_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___f_5491_; lean_object* v___f_5492_; lean_object* v___x_5493_; 
v_toApplicative_5486_ = lean_ctor_get(v_inst_5481_, 0);
v_toBind_5487_ = lean_ctor_get(v_inst_5481_, 1);
lean_inc_n(v_toBind_5487_, 2);
v_toPure_5488_ = lean_ctor_get(v_toApplicative_5486_, 1);
lean_inc_n(v_toPure_5488_, 2);
lean_inc_ref(v_ch_5483_);
lean_inc(v_inst_5480_);
v___x_5489_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5489_, 0, lean_box(0));
lean_closure_set(v___x_5489_, 1, v_inst_5480_);
lean_closure_set(v___x_5489_, 2, v_ch_5483_);
lean_inc(v_inst_5482_);
v___x_5490_ = lean_apply_2(v_inst_5482_, lean_box(0), v___x_5489_);
lean_inc(v_f_5484_);
v___f_5491_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5491_, 0, v_toPure_5488_);
lean_closure_set(v___f_5491_, 1, v_inst_5480_);
lean_closure_set(v___f_5491_, 2, v_inst_5481_);
lean_closure_set(v___f_5491_, 3, v_inst_5482_);
lean_closure_set(v___f_5491_, 4, v_ch_5483_);
lean_closure_set(v___f_5491_, 5, v_f_5484_);
v___f_5492_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5492_, 0, v_toPure_5488_);
lean_closure_set(v___f_5492_, 1, v_b_5485_);
lean_closure_set(v___f_5492_, 2, v_f_5484_);
lean_closure_set(v___f_5492_, 3, v_toBind_5487_);
lean_closure_set(v___f_5492_, 4, v___f_5491_);
v___x_5493_ = lean_apply_4(v_toBind_5487_, lean_box(0), lean_box(0), v___x_5490_, v___f_5492_);
return v___x_5493_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5494_, lean_object* v_inst_5495_, lean_object* v_inst_5496_, lean_object* v_inst_5497_, lean_object* v_ch_5498_, lean_object* v_f_5499_, lean_object* v_____do__lift_5500_){
_start:
{
if (lean_obj_tag(v_____do__lift_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v___x_5502_; 
lean_dec(v_f_5499_);
lean_dec_ref(v_ch_5498_);
lean_dec(v_inst_5497_);
lean_dec_ref(v_inst_5496_);
lean_dec(v_inst_5495_);
v_a_5501_ = lean_ctor_get(v_____do__lift_5500_, 0);
lean_inc(v_a_5501_);
lean_dec_ref_known(v_____do__lift_5500_, 1);
v___x_5502_ = lean_apply_2(v_toPure_5494_, lean_box(0), v_a_5501_);
return v___x_5502_;
}
else
{
lean_object* v_a_5503_; lean_object* v___x_5504_; 
lean_dec(v_toPure_5494_);
v_a_5503_ = lean_ctor_get(v_____do__lift_5500_, 0);
lean_inc(v_a_5503_);
lean_dec_ref_known(v_____do__lift_5500_, 1);
v___x_5504_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5495_, v_inst_5496_, v_inst_5497_, v_ch_5498_, v_f_5499_, v_a_5503_);
return v___x_5504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5505_, lean_object* v_m_5506_, lean_object* v_00_u03b2_5507_, lean_object* v_inst_5508_, lean_object* v_inst_5509_, lean_object* v_inst_5510_, lean_object* v_ch_5511_, lean_object* v_f_5512_, lean_object* v_b_5513_){
_start:
{
lean_object* v___x_5514_; 
v___x_5514_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5508_, v_inst_5509_, v_inst_5510_, v_ch_5511_, v_f_5512_, v_b_5513_);
return v___x_5514_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5515_, lean_object* v_inst_5516_, lean_object* v_inst_5517_, lean_object* v_00_u03b2_5518_, lean_object* v_ch_5519_, lean_object* v_b_5520_, lean_object* v_f_5521_){
_start:
{
lean_object* v___x_5522_; 
v___x_5522_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5515_, v_inst_5516_, v_inst_5517_, v_ch_5519_, v_f_5521_, v_b_5520_);
return v___x_5522_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5523_, lean_object* v_inst_5524_, lean_object* v_inst_5525_){
_start:
{
lean_object* v___f_5526_; 
v___f_5526_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5526_, 0, v_inst_5523_);
lean_closure_set(v___f_5526_, 1, v_inst_5524_);
lean_closure_set(v___f_5526_, 2, v_inst_5525_);
return v___f_5526_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5527_, lean_object* v_m_5528_, lean_object* v_inst_5529_, lean_object* v_inst_5530_, lean_object* v_inst_5531_){
_start:
{
lean_object* v___f_5532_; 
v___f_5532_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5532_, 0, v_inst_5529_);
lean_closure_set(v___f_5532_, 1, v_inst_5530_);
lean_closure_set(v___f_5532_, 2, v_inst_5531_);
return v___f_5532_;
}
}
lean_object* runtime_initialize_Std_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_IO(uint8_t builtin);
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

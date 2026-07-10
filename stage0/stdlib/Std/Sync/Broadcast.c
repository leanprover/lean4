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
uint8_t lean_bool_not(uint8_t);
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
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object* v_next_1477_, lean_object* v_slot_1478_){
_start:
{
lean_object* v_value_1479_; lean_object* v_pos_1480_; lean_object* v_remaining_1481_; uint8_t v___x_1482_; uint8_t v___x_1483_; 
v_value_1479_ = lean_ctor_get(v_slot_1478_, 0);
v_pos_1480_ = lean_ctor_get(v_slot_1478_, 1);
v_remaining_1481_ = lean_ctor_get(v_slot_1478_, 2);
v___x_1482_ = lean_nat_dec_eq(v_next_1477_, v_pos_1480_);
v___x_1483_ = lean_bool_not(v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1504_; 
lean_inc(v_remaining_1481_);
lean_inc(v_pos_1480_);
lean_inc(v_value_1479_);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_slot_1478_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1505_ = lean_ctor_get(v_slot_1478_, 2);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_slot_1478_, 1);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_slot_1478_, 0);
lean_dec(v_unused_1507_);
v___x_1485_ = v_slot_1478_;
v_isShared_1486_ = v_isSharedCheck_1504_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v_slot_1478_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1504_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_dec_eq(v_remaining_1481_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1489_ = lean_box(v___x_1488_);
lean_inc(v_value_1479_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_value_1479_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = lean_nat_sub(v_remaining_1481_, v___x_1487_);
lean_dec(v_remaining_1481_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 2, v___x_1491_);
v___x_1493_ = v___x_1485_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_value_1479_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_pos_1480_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1490_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
return v___x_1494_;
}
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_dec(v_remaining_1481_);
v___x_1496_ = lean_box(v___x_1488_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_value_1479_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_unsigned_to_nat(0u);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 2, v___x_1499_);
lean_ctor_set(v___x_1485_, 0, v___x_1498_);
v___x_1501_ = v___x_1485_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_pos_1480_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1497_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
return v___x_1502_;
}
}
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___closed__0));
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v_slot_1478_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object* v_next_1510_, lean_object* v_slot_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(v_next_1510_, v_slot_1511_);
lean_dec(v_next_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object* v_inst_1513_, lean_object* v_slot_1514_, lean_object* v_next_1515_){
_start:
{
lean_object* v___f_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___f_1516_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1516_, 0, v_next_1515_);
v___x_1517_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1517_, 0, lean_box(0));
lean_closure_set(v___x_1517_, 1, lean_box(0));
lean_closure_set(v___x_1517_, 2, lean_box(0));
lean_closure_set(v___x_1517_, 3, v_slot_1514_);
lean_closure_set(v___x_1517_, 4, v___f_1516_);
v___x_1518_ = lean_apply_2(v_inst_1513_, lean_box(0), v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object* v_m_1519_, lean_object* v_00_u03b1_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_slot_1523_, lean_object* v_next_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1522_, v_slot_1523_, v_next_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object* v_m_1527_, lean_object* v_00_u03b1_1528_, lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_slot_1531_, lean_object* v_next_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(v_m_1527_, v_00_u03b1_1528_, v_inst_1529_, v_inst_1530_, v_slot_1531_, v_next_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_inst_1529_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object* v_toApplicative_1535_, lean_object* v_fst_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_toPure_1538_; lean_object* v___x_1539_; 
v_toPure_1538_ = lean_ctor_get(v_toApplicative_1535_, 1);
lean_inc(v_toPure_1538_);
lean_dec_ref(v_toApplicative_1535_);
v___x_1539_ = lean_apply_2(v_toPure_1538_, lean_box(0), v_fst_1536_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object* v_inst_1540_, lean_object* v_toBind_1541_, lean_object* v___f_1542_, lean_object* v_____r_1543_, lean_object* v_st_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_inc(v___y_1545_);
v___x_1546_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1546_, 0, lean_box(0));
lean_closure_set(v___x_1546_, 1, lean_box(0));
lean_closure_set(v___x_1546_, 2, v___y_1545_);
lean_closure_set(v___x_1546_, 3, v_st_1544_);
v___x_1547_ = lean_apply_2(v_inst_1540_, lean_box(0), v___x_1546_);
v___x_1548_ = lean_apply_4(v_toBind_1541_, lean_box(0), lean_box(0), v___x_1547_, v___f_1542_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed(lean_object* v_inst_1549_, lean_object* v_toBind_1550_, lean_object* v___f_1551_, lean_object* v_____r_1552_, lean_object* v_st_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1549_, v_toBind_1550_, v___f_1551_, v_____r_1552_, v_st_1553_, v___y_1554_);
lean_dec(v___y_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object* v_snd_1556_, lean_object* v_waiters_1557_, lean_object* v_capacity_1558_, lean_object* v_size_1559_, lean_object* v_buffer_1560_, lean_object* v_write_1561_, lean_object* v_read_1562_, lean_object* v_receivers_1563_, lean_object* v_nextId_1564_, uint8_t v_closed_1565_, lean_object* v_pos_1566_, lean_object* v___f_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1570_, 0, v_snd_1556_);
lean_ctor_set(v___x_1570_, 1, v_waiters_1557_);
lean_ctor_set(v___x_1570_, 2, v_capacity_1558_);
lean_ctor_set(v___x_1570_, 3, v_size_1559_);
lean_ctor_set(v___x_1570_, 4, v_buffer_1560_);
lean_ctor_set(v___x_1570_, 5, v_write_1561_);
lean_ctor_set(v___x_1570_, 6, v_read_1562_);
lean_ctor_set(v___x_1570_, 7, v_receivers_1563_);
lean_ctor_set(v___x_1570_, 8, v_nextId_1564_);
lean_ctor_set(v___x_1570_, 9, v_pos_1566_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*10, v_closed_1565_);
v___x_1571_ = lean_box(0);
lean_inc(v_a_1568_);
v___x_1572_ = lean_apply_3(v___f_1567_, v___x_1571_, v___x_1570_, v_a_1568_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object* v_snd_1573_, lean_object* v_waiters_1574_, lean_object* v_capacity_1575_, lean_object* v_size_1576_, lean_object* v_buffer_1577_, lean_object* v_write_1578_, lean_object* v_read_1579_, lean_object* v_receivers_1580_, lean_object* v_nextId_1581_, lean_object* v_closed_1582_, lean_object* v_pos_1583_, lean_object* v___f_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
uint8_t v_closed_boxed_1587_; lean_object* v_res_1588_; 
v_closed_boxed_1587_ = lean_unbox(v_closed_1582_);
v_res_1588_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1573_, v_waiters_1574_, v_capacity_1575_, v_size_1576_, v_buffer_1577_, v_write_1578_, v_read_1579_, v_receivers_1580_, v_nextId_1581_, v_closed_boxed_1587_, v_pos_1583_, v___f_1584_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object* v_toApplicative_1589_, lean_object* v_inst_1590_, lean_object* v_toBind_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, uint8_t v___x_1594_, lean_object* v_inst_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_fst_1597_; 
v_fst_1597_ = lean_ctor_get(v_a_1596_, 0);
lean_inc(v_fst_1597_);
if (lean_obj_tag(v_fst_1597_) == 1)
{
lean_object* v_snd_1598_; lean_object* v___f_1599_; lean_object* v___f_1600_; uint8_t v___x_1601_; 
v_snd_1598_ = lean_ctor_get(v_a_1596_, 1);
lean_inc(v_snd_1598_);
lean_dec_ref(v_a_1596_);
v___f_1599_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1599_, 0, v_toApplicative_1589_);
lean_closure_set(v___f_1599_, 1, v_fst_1597_);
lean_inc_ref(v___f_1599_);
lean_inc(v_toBind_1591_);
lean_inc(v_inst_1590_);
v___f_1600_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1600_, 0, v_inst_1590_);
lean_closure_set(v___f_1600_, 1, v_toBind_1591_);
lean_closure_set(v___f_1600_, 2, v___f_1599_);
v___x_1601_ = lean_unbox(v_snd_1598_);
lean_dec(v_snd_1598_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref(v___f_1600_);
lean_dec(v_inst_1595_);
v___x_1602_ = lean_box(0);
v___x_1603_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1590_, v_toBind_1591_, v___f_1599_, v___x_1602_, v_a_1592_, v_a_1593_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; lean_object* v_producers_1605_; lean_object* v_waiters_1606_; lean_object* v_capacity_1607_; lean_object* v_size_1608_; lean_object* v_buffer_1609_; lean_object* v_write_1610_; lean_object* v_read_1611_; lean_object* v_receivers_1612_; lean_object* v_nextId_1613_; uint8_t v_closed_1614_; lean_object* v_pos_1615_; lean_object* v___x_1616_; 
v___x_1604_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_1592_);
v_producers_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc_ref(v_producers_1605_);
v_waiters_1606_ = lean_ctor_get(v___x_1604_, 1);
lean_inc_ref(v_waiters_1606_);
v_capacity_1607_ = lean_ctor_get(v___x_1604_, 2);
lean_inc(v_capacity_1607_);
v_size_1608_ = lean_ctor_get(v___x_1604_, 3);
lean_inc(v_size_1608_);
v_buffer_1609_ = lean_ctor_get(v___x_1604_, 4);
lean_inc_ref(v_buffer_1609_);
v_write_1610_ = lean_ctor_get(v___x_1604_, 5);
lean_inc(v_write_1610_);
v_read_1611_ = lean_ctor_get(v___x_1604_, 6);
lean_inc(v_read_1611_);
v_receivers_1612_ = lean_ctor_get(v___x_1604_, 7);
lean_inc(v_receivers_1612_);
v_nextId_1613_ = lean_ctor_get(v___x_1604_, 8);
lean_inc(v_nextId_1613_);
v_closed_1614_ = lean_ctor_get_uint8(v___x_1604_, sizeof(void*)*10);
v_pos_1615_ = lean_ctor_get(v___x_1604_, 9);
lean_inc(v_pos_1615_);
v___x_1616_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1605_);
if (lean_obj_tag(v___x_1616_) == 1)
{
lean_object* v_val_1617_; lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec_ref(v___x_1604_);
lean_dec_ref(v___f_1599_);
lean_dec(v_inst_1590_);
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v_fst_1618_ = lean_ctor_get(v_val_1617_, 0);
lean_inc(v_fst_1618_);
v_snd_1619_ = lean_ctor_get(v_val_1617_, 1);
lean_inc(v_snd_1619_);
lean_dec(v_val_1617_);
v___x_1620_ = lean_box(v_closed_1614_);
lean_inc(v_a_1593_);
v___f_1621_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1621_, 0, v_snd_1619_);
lean_closure_set(v___f_1621_, 1, v_waiters_1606_);
lean_closure_set(v___f_1621_, 2, v_capacity_1607_);
lean_closure_set(v___f_1621_, 3, v_size_1608_);
lean_closure_set(v___f_1621_, 4, v_buffer_1609_);
lean_closure_set(v___f_1621_, 5, v_write_1610_);
lean_closure_set(v___f_1621_, 6, v_read_1611_);
lean_closure_set(v___f_1621_, 7, v_receivers_1612_);
lean_closure_set(v___f_1621_, 8, v_nextId_1613_);
lean_closure_set(v___f_1621_, 9, v___x_1620_);
lean_closure_set(v___f_1621_, 10, v_pos_1615_);
lean_closure_set(v___f_1621_, 11, v___f_1600_);
lean_closure_set(v___f_1621_, 12, v_a_1593_);
v___x_1622_ = lean_box(v___x_1594_);
v___x_1623_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1623_, 0, lean_box(0));
lean_closure_set(v___x_1623_, 1, v___x_1622_);
lean_closure_set(v___x_1623_, 2, v_fst_1618_);
v___x_1624_ = lean_apply_2(v_inst_1595_, lean_box(0), v___x_1623_);
v___x_1625_ = lean_apply_4(v_toBind_1591_, lean_box(0), lean_box(0), v___x_1624_, v___f_1621_);
return v___x_1625_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v___x_1616_);
lean_dec(v_pos_1615_);
lean_dec(v_nextId_1613_);
lean_dec(v_receivers_1612_);
lean_dec(v_read_1611_);
lean_dec(v_write_1610_);
lean_dec_ref(v_buffer_1609_);
lean_dec(v_size_1608_);
lean_dec(v_capacity_1607_);
lean_dec_ref(v_waiters_1606_);
lean_dec_ref(v___f_1600_);
lean_dec(v_inst_1595_);
v___x_1626_ = lean_box(0);
v___x_1627_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1590_, v_toBind_1591_, v___f_1599_, v___x_1626_, v___x_1604_, v_a_1593_);
return v___x_1627_;
}
}
}
else
{
lean_object* v_toPure_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec(v_fst_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_inst_1595_);
lean_dec_ref(v_a_1592_);
lean_dec(v_toBind_1591_);
lean_dec(v_inst_1590_);
v_toPure_1628_ = lean_ctor_get(v_toApplicative_1589_, 1);
lean_inc(v_toPure_1628_);
lean_dec_ref(v_toApplicative_1589_);
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_apply_2(v_toPure_1628_, lean_box(0), v___x_1629_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object* v_toApplicative_1631_, lean_object* v_inst_1632_, lean_object* v_toBind_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v___x_1636_, lean_object* v_inst_1637_, lean_object* v_a_1638_){
_start:
{
uint8_t v___x_1069__boxed_1639_; lean_object* v_res_1640_; 
v___x_1069__boxed_1639_ = lean_unbox(v___x_1636_);
v_res_1640_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1631_, v_inst_1632_, v_toBind_1633_, v_a_1634_, v_a_1635_, v___x_1069__boxed_1639_, v_inst_1637_, v_a_1638_);
lean_dec(v_a_1635_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object* v_inst_1641_, lean_object* v_next_1642_, lean_object* v_toBind_1643_, lean_object* v___f_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1641_, v_a_1645_, v_next_1642_);
v___x_1647_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1646_, v___f_1644_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object* v_a_1648_, lean_object* v_toApplicative_1649_, lean_object* v_inst_1650_, lean_object* v_toBind_1651_, lean_object* v_a_1652_, lean_object* v_inst_1653_, lean_object* v_next_1654_, lean_object* v_inst_1655_, uint8_t v_a_1656_){
_start:
{
if (v_a_1656_ == 0)
{
lean_object* v_capacity_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___f_1660_; lean_object* v___f_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_capacity_1657_ = lean_ctor_get(v_a_1648_, 2);
lean_inc(v_capacity_1657_);
v___x_1658_ = 1;
v___x_1659_ = lean_box(v___x_1658_);
lean_inc(v_a_1652_);
lean_inc_n(v_toBind_1651_, 2);
lean_inc_n(v_inst_1650_, 2);
v___f_1660_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1660_, 0, v_toApplicative_1649_);
lean_closure_set(v___f_1660_, 1, v_inst_1650_);
lean_closure_set(v___f_1660_, 2, v_toBind_1651_);
lean_closure_set(v___f_1660_, 3, v_a_1648_);
lean_closure_set(v___f_1660_, 4, v_a_1652_);
lean_closure_set(v___f_1660_, 5, v___x_1659_);
lean_closure_set(v___f_1660_, 6, v_inst_1653_);
lean_inc(v_next_1654_);
v___f_1661_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1661_, 0, v_inst_1650_);
lean_closure_set(v___f_1661_, 1, v_next_1654_);
lean_closure_set(v___f_1661_, 2, v_toBind_1651_);
lean_closure_set(v___f_1661_, 3, v___f_1660_);
v___x_1662_ = lean_nat_mod(v_next_1654_, v_capacity_1657_);
lean_dec(v_capacity_1657_);
lean_dec(v_next_1654_);
v___x_1663_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1655_, v_inst_1650_, v___x_1662_, v_a_1652_);
v___x_1664_ = lean_apply_4(v_toBind_1651_, lean_box(0), lean_box(0), v___x_1663_, v___f_1661_);
return v___x_1664_;
}
else
{
lean_object* v_toPure_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec_ref(v_inst_1655_);
lean_dec(v_next_1654_);
lean_dec(v_inst_1653_);
lean_dec(v_toBind_1651_);
lean_dec(v_inst_1650_);
lean_dec_ref(v_a_1648_);
v_toPure_1665_ = lean_ctor_get(v_toApplicative_1649_, 1);
lean_inc(v_toPure_1665_);
lean_dec_ref(v_toApplicative_1649_);
v___x_1666_ = lean_box(0);
v___x_1667_ = lean_apply_2(v_toPure_1665_, lean_box(0), v___x_1666_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object* v_a_1668_, lean_object* v_toApplicative_1669_, lean_object* v_inst_1670_, lean_object* v_toBind_1671_, lean_object* v_a_1672_, lean_object* v_inst_1673_, lean_object* v_next_1674_, lean_object* v_inst_1675_, lean_object* v_a_1676_){
_start:
{
uint8_t v_a_boxed_1677_; lean_object* v_res_1678_; 
v_a_boxed_1677_ = lean_unbox(v_a_1676_);
v_res_1678_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1668_, v_toApplicative_1669_, v_inst_1670_, v_toBind_1671_, v_a_1672_, v_inst_1673_, v_next_1674_, v_inst_1675_, v_a_boxed_1677_);
lean_dec(v_a_1672_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object* v_toApplicative_1679_, lean_object* v_inst_1680_, lean_object* v_toBind_1681_, lean_object* v_a_1682_, lean_object* v_inst_1683_, lean_object* v_next_1684_, lean_object* v_inst_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___f_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
lean_inc_ref(v_inst_1685_);
lean_inc(v_a_1682_);
lean_inc(v_toBind_1681_);
lean_inc(v_inst_1680_);
v___f_1687_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_1687_, 0, v_a_1686_);
lean_closure_set(v___f_1687_, 1, v_toApplicative_1679_);
lean_closure_set(v___f_1687_, 2, v_inst_1680_);
lean_closure_set(v___f_1687_, 3, v_toBind_1681_);
lean_closure_set(v___f_1687_, 4, v_a_1682_);
lean_closure_set(v___f_1687_, 5, v_inst_1683_);
lean_closure_set(v___f_1687_, 6, v_next_1684_);
lean_closure_set(v___f_1687_, 7, v_inst_1685_);
v___x_1688_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_1685_, v_inst_1680_, v_a_1682_);
v___x_1689_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v___x_1688_, v___f_1687_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed(lean_object* v_toApplicative_1690_, lean_object* v_inst_1691_, lean_object* v_toBind_1692_, lean_object* v_a_1693_, lean_object* v_inst_1694_, lean_object* v_next_1695_, lean_object* v_inst_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(v_toApplicative_1690_, v_inst_1691_, v_toBind_1692_, v_a_1693_, v_inst_1694_, v_next_1695_, v_inst_1696_, v_a_1697_);
lean_dec(v_a_1693_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_next_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_toApplicative_1704_; lean_object* v_toBind_1705_; lean_object* v___f_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_toApplicative_1704_ = lean_ctor_get(v_inst_1699_, 0);
lean_inc_ref(v_toApplicative_1704_);
v_toBind_1705_ = lean_ctor_get(v_inst_1699_, 1);
lean_inc_n(v_toBind_1705_, 2);
lean_inc_n(v_a_1703_, 2);
lean_inc(v_inst_1700_);
v___f_1706_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_1706_, 0, v_toApplicative_1704_);
lean_closure_set(v___f_1706_, 1, v_inst_1700_);
lean_closure_set(v___f_1706_, 2, v_toBind_1705_);
lean_closure_set(v___f_1706_, 3, v_a_1703_);
lean_closure_set(v___f_1706_, 4, v_inst_1701_);
lean_closure_set(v___f_1706_, 5, v_next_1702_);
lean_closure_set(v___f_1706_, 6, v_inst_1699_);
v___x_1707_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1707_, 0, lean_box(0));
lean_closure_set(v___x_1707_, 1, lean_box(0));
lean_closure_set(v___x_1707_, 2, v_a_1703_);
v___x_1708_ = lean_apply_2(v_inst_1700_, lean_box(0), v___x_1707_);
v___x_1709_ = lean_apply_4(v_toBind_1705_, lean_box(0), lean_box(0), v___x_1708_, v___f_1706_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___boxed(lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_next_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1710_, v_inst_1711_, v_inst_1712_, v_next_1713_, v_a_1714_);
lean_dec(v_a_1714_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object* v_m_1716_, lean_object* v_00_u03b1_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_next_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1718_, v_inst_1719_, v_inst_1720_, v_next_1721_, v_a_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___boxed(lean_object* v_m_1724_, lean_object* v_00_u03b1_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_next_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(v_m_1724_, v_00_u03b1_1725_, v_inst_1726_, v_inst_1727_, v_inst_1728_, v_next_1729_, v_a_1730_);
lean_dec(v_a_1730_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___x_1735_; lean_object* v_capacity_1736_; lean_object* v_buffer_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1735_ = lean_st_ref_get(v_a_1733_);
v_capacity_1736_ = lean_ctor_get(v___x_1735_, 2);
lean_inc(v_capacity_1736_);
v_buffer_1737_ = lean_ctor_get(v___x_1735_, 4);
lean_inc_ref(v_buffer_1737_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_nat_mod(v_place_1732_, v_capacity_1736_);
lean_dec(v_capacity_1736_);
v___x_1739_ = lean_array_fget(v_buffer_1737_, v___x_1738_);
lean_dec(v___x_1738_);
lean_dec_ref(v_buffer_1737_);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_1741_, lean_object* v_a_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec(v_place_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1747_; lean_object* v_size_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1747_ = lean_st_ref_get(v_a_1745_);
v_size_1748_ = lean_ctor_get(v___x_1747_, 3);
lean_inc(v_size_1748_);
lean_dec(v___x_1747_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_nat_dec_eq(v_size_1748_, v___x_1749_);
lean_dec(v_size_1748_);
v___x_1751_ = lean_box(v___x_1750_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1753_);
lean_dec(v_a_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_1756_, lean_object* v_next_1757_){
_start:
{
lean_object* v___x_1759_; lean_object* v_fst_1761_; lean_object* v_snd_1762_; lean_object* v_value_1765_; lean_object* v_pos_1766_; lean_object* v_remaining_1767_; uint8_t v___x_1768_; uint8_t v___x_1769_; 
v___x_1759_ = lean_st_ref_take(v_slot_1756_);
v_value_1765_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_value_1765_);
v_pos_1766_ = lean_ctor_get(v___x_1759_, 1);
lean_inc(v_pos_1766_);
v_remaining_1767_ = lean_ctor_get(v___x_1759_, 2);
lean_inc(v_remaining_1767_);
v___x_1768_ = lean_nat_dec_eq(v_next_1757_, v_pos_1766_);
v___x_1769_ = lean_bool_not(v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1788_; 
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; 
v_unused_1789_ = lean_ctor_get(v___x_1759_, 2);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v___x_1759_, 1);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v___x_1759_, 0);
lean_dec(v_unused_1791_);
v___x_1771_ = v___x_1759_;
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v___x_1759_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = lean_unsigned_to_nat(1u);
v___x_1774_ = lean_nat_dec_eq(v_remaining_1767_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1775_ = lean_box(v___x_1774_);
lean_inc(v_value_1765_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_value_1765_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_nat_sub(v_remaining_1767_, v___x_1773_);
lean_dec(v_remaining_1767_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 2, v___x_1777_);
v___x_1779_ = v___x_1771_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_value_1765_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_pos_1766_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
v_fst_1761_ = v___x_1776_;
v_snd_1762_ = v___x_1779_;
goto v___jp_1760_;
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec(v_remaining_1767_);
v___x_1781_ = lean_box(v___x_1774_);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v_value_1765_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_unsigned_to_nat(0u);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 2, v___x_1784_);
lean_ctor_set(v___x_1771_, 0, v___x_1783_);
v___x_1786_ = v___x_1771_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_pos_1766_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
v_fst_1761_ = v___x_1782_;
v_snd_1762_ = v___x_1786_;
goto v___jp_1760_;
}
}
}
}
else
{
lean_object* v___x_1792_; 
lean_dec(v_remaining_1767_);
lean_dec(v_pos_1766_);
lean_dec(v_value_1765_);
v___x_1792_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___closed__0));
v_fst_1761_ = v___x_1792_;
v_snd_1762_ = v___x_1759_;
goto v___jp_1760_;
}
v___jp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = lean_st_ref_set(v_slot_1756_, v_snd_1762_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_fst_1761_);
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_1793_, lean_object* v_next_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_1793_, v_next_1794_);
lean_dec(v_next_1794_);
lean_dec(v_slot_1793_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1873_; 
v___x_1800_ = lean_st_ref_get(v_a_1798_);
v___x_1801_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1798_);
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1873_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1873_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
uint8_t v___x_1806_; 
v___x_1806_ = lean_unbox(v_a_1802_);
lean_dec(v_a_1802_);
if (v___x_1806_ == 0)
{
lean_object* v_capacity_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1804_);
v_capacity_1807_ = lean_ctor_get(v___x_1800_, 2);
lean_inc(v_capacity_1807_);
v___x_1808_ = lean_nat_mod(v_next_1797_, v_capacity_1807_);
lean_dec(v_capacity_1807_);
v___x_1809_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_1808_, v_a_1798_);
lean_dec(v___x_1808_);
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1868_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1868_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1867_; 
v___x_1814_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_1810_, v_next_1797_);
lean_dec(v_a_1810_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1867_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1867_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v_st_1822_; lean_object* v___y_1823_; 
v_fst_1819_ = lean_ctor_get(v_a_1815_, 0);
lean_inc(v_fst_1819_);
v_snd_1820_ = lean_ctor_get(v_a_1815_, 1);
lean_inc(v_snd_1820_);
lean_dec(v_a_1815_);
if (lean_obj_tag(v_fst_1819_) == 1)
{
uint8_t v___x_1828_; 
lean_del_object(v___x_1812_);
v___x_1828_ = lean_unbox(v_snd_1820_);
if (v___x_1828_ == 0)
{
lean_dec(v_snd_1820_);
v_st_1822_ = v___x_1800_;
v___y_1823_ = v_a_1798_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1829_; lean_object* v_producers_1830_; lean_object* v_waiters_1831_; lean_object* v_capacity_1832_; lean_object* v_size_1833_; lean_object* v_buffer_1834_; lean_object* v_write_1835_; lean_object* v_read_1836_; lean_object* v_receivers_1837_; lean_object* v_nextId_1838_; uint8_t v_closed_1839_; lean_object* v_pos_1840_; lean_object* v___x_1841_; 
v___x_1829_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_1800_);
v_producers_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc_ref(v_producers_1830_);
v_waiters_1831_ = lean_ctor_get(v___x_1829_, 1);
lean_inc_ref(v_waiters_1831_);
v_capacity_1832_ = lean_ctor_get(v___x_1829_, 2);
lean_inc(v_capacity_1832_);
v_size_1833_ = lean_ctor_get(v___x_1829_, 3);
lean_inc(v_size_1833_);
v_buffer_1834_ = lean_ctor_get(v___x_1829_, 4);
lean_inc_ref(v_buffer_1834_);
v_write_1835_ = lean_ctor_get(v___x_1829_, 5);
lean_inc(v_write_1835_);
v_read_1836_ = lean_ctor_get(v___x_1829_, 6);
lean_inc(v_read_1836_);
v_receivers_1837_ = lean_ctor_get(v___x_1829_, 7);
lean_inc(v_receivers_1837_);
v_nextId_1838_ = lean_ctor_get(v___x_1829_, 8);
lean_inc(v_nextId_1838_);
v_closed_1839_ = lean_ctor_get_uint8(v___x_1829_, sizeof(void*)*10);
v_pos_1840_ = lean_ctor_get(v___x_1829_, 9);
lean_inc(v_pos_1840_);
v___x_1841_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1830_);
if (lean_obj_tag(v___x_1841_) == 1)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1852_; 
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; 
v_unused_1853_ = lean_ctor_get(v___x_1829_, 9);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v___x_1829_, 8);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v___x_1829_, 7);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v___x_1829_, 6);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v___x_1829_, 5);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v___x_1829_, 4);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v___x_1829_, 3);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v___x_1829_, 2);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v___x_1829_, 1);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1862_);
v___x_1843_ = v___x_1829_;
v_isShared_1844_ = v_isSharedCheck_1852_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v___x_1829_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1852_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_val_1845_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v_val_1845_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_val_1845_);
lean_dec_ref_known(v___x_1841_, 1);
v_fst_1846_ = lean_ctor_get(v_val_1845_, 0);
lean_inc(v_fst_1846_);
v_snd_1847_ = lean_ctor_get(v_val_1845_, 1);
lean_inc(v_snd_1847_);
lean_dec(v_val_1845_);
v___x_1848_ = lean_io_promise_resolve(v_snd_1820_, v_fst_1846_);
lean_dec(v_fst_1846_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v_snd_1847_);
v___x_1850_ = v___x_1843_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_snd_1847_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_waiters_1831_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_capacity_1832_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_size_1833_);
lean_ctor_set(v_reuseFailAlloc_1851_, 4, v_buffer_1834_);
lean_ctor_set(v_reuseFailAlloc_1851_, 5, v_write_1835_);
lean_ctor_set(v_reuseFailAlloc_1851_, 6, v_read_1836_);
lean_ctor_set(v_reuseFailAlloc_1851_, 7, v_receivers_1837_);
lean_ctor_set(v_reuseFailAlloc_1851_, 8, v_nextId_1838_);
lean_ctor_set(v_reuseFailAlloc_1851_, 9, v_pos_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1851_, sizeof(void*)*10, v_closed_1839_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
v_st_1822_ = v___x_1850_;
v___y_1823_ = v_a_1798_;
goto v___jp_1821_;
}
}
}
else
{
lean_dec(v___x_1841_);
lean_dec(v_pos_1840_);
lean_dec(v_nextId_1838_);
lean_dec(v_receivers_1837_);
lean_dec(v_read_1836_);
lean_dec(v_write_1835_);
lean_dec_ref(v_buffer_1834_);
lean_dec(v_size_1833_);
lean_dec(v_capacity_1832_);
lean_dec_ref(v_waiters_1831_);
lean_dec(v_snd_1820_);
v_st_1822_ = v___x_1829_;
v___y_1823_ = v_a_1798_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_dec(v_snd_1820_);
lean_dec(v_fst_1819_);
lean_del_object(v___x_1817_);
lean_dec(v___x_1800_);
v___x_1863_ = lean_box(0);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1863_);
v___x_1865_ = v___x_1812_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
v___jp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_st_ref_set(v___y_1823_, v_st_1822_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v_fst_1819_);
v___x_1826_ = v___x_1817_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_fst_1819_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec(v___x_1800_);
v___x_1869_ = lean_box(0);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1869_);
v___x_1871_ = v___x_1804_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_1874_, lean_object* v_a_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec(v_next_1874_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_a_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1919_; 
v_fst_1881_ = lean_ctor_get(v_a_1878_, 0);
v_snd_1882_ = lean_ctor_get(v_a_1878_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_a_1878_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1884_ = v_a_1878_;
v_isShared_1885_ = v_isSharedCheck_1919_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_snd_1882_);
lean_inc(v_fst_1881_);
lean_dec(v_a_1878_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1919_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v_size_1891_; lean_object* v_pos_1892_; uint8_t v___x_1893_; 
v_size_1891_ = lean_ctor_get(v_fst_1881_, 3);
v_pos_1892_ = lean_ctor_get(v_fst_1881_, 9);
v___x_1893_ = lean_nat_dec_lt(v_snd_1882_, v_pos_1892_);
if (v___x_1893_ == 0)
{
goto v___jp_1886_;
}
else
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = lean_nat_dec_lt(v___x_1894_, v_size_1891_);
if (v___x_1895_ == 0)
{
goto v___jp_1886_;
}
else
{
lean_object* v___x_1896_; 
lean_del_object(v___x_1884_);
v___x_1896_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_1882_, v___y_1879_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1910_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1910_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1910_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
if (lean_obj_tag(v_a_1897_) == 1)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec_ref_known(v_a_1897_, 1);
lean_del_object(v___x_1899_);
lean_dec(v_fst_1881_);
v___x_1901_ = lean_st_ref_get(v___y_1879_);
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_nat_add(v_snd_1882_, v___x_1902_);
lean_dec(v_snd_1882_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v_a_1878_ = v___x_1904_;
goto _start;
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
lean_dec(v_a_1897_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_fst_1881_);
lean_ctor_set(v___x_1906_, 1, v_snd_1882_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1906_);
v___x_1908_ = v___x_1899_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_snd_1882_);
lean_dec(v_fst_1881_);
v_a_1911_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1896_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1896_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
v___jp_1886_:
{
lean_object* v___x_1888_; 
if (v_isShared_1885_ == 0)
{
v___x_1888_ = v___x_1884_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_fst_1881_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_snd_1882_);
v___x_1888_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_a_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_1920_, v___y_1921_);
lean_dec(v___y_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_1924_, lean_object* v_k_1925_){
_start:
{
if (lean_obj_tag(v_t_1924_) == 0)
{
lean_object* v_k_1926_; lean_object* v_v_1927_; lean_object* v_l_1928_; lean_object* v_r_1929_; uint8_t v___x_1930_; 
v_k_1926_ = lean_ctor_get(v_t_1924_, 1);
v_v_1927_ = lean_ctor_get(v_t_1924_, 2);
v_l_1928_ = lean_ctor_get(v_t_1924_, 3);
v_r_1929_ = lean_ctor_get(v_t_1924_, 4);
v___x_1930_ = lean_nat_dec_lt(v_k_1925_, v_k_1926_);
if (v___x_1930_ == 0)
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_nat_dec_eq(v_k_1925_, v_k_1926_);
if (v___x_1931_ == 0)
{
v_t_1924_ = v_r_1929_;
goto _start;
}
else
{
lean_object* v___x_1933_; 
lean_inc(v_v_1927_);
v___x_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_v_1927_);
return v___x_1933_;
}
}
else
{
v_t_1924_ = v_l_1928_;
goto _start;
}
}
else
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_box(0);
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_1936_, lean_object* v_k_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_1936_, v_k_1937_);
lean_dec(v_k_1937_);
lean_dec(v_t_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_1939_, lean_object* v_t_1940_){
_start:
{
if (lean_obj_tag(v_t_1940_) == 0)
{
lean_object* v_k_1941_; lean_object* v_v_1942_; lean_object* v_l_1943_; lean_object* v_r_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_2599_; 
v_k_1941_ = lean_ctor_get(v_t_1940_, 1);
v_v_1942_ = lean_ctor_get(v_t_1940_, 2);
v_l_1943_ = lean_ctor_get(v_t_1940_, 3);
v_r_1944_ = lean_ctor_get(v_t_1940_, 4);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_t_1940_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v_t_1940_, 0);
lean_dec(v_unused_2600_);
v___x_1946_ = v_t_1940_;
v_isShared_1947_ = v_isSharedCheck_2599_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_r_1944_);
lean_inc(v_l_1943_);
lean_inc(v_v_1942_);
lean_inc(v_k_1941_);
lean_dec(v_t_1940_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_2599_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
uint8_t v___x_1948_; 
v___x_1948_ = lean_nat_dec_lt(v_k_1939_, v_k_1941_);
if (v___x_1948_ == 0)
{
uint8_t v___x_1949_; 
v___x_1949_ = lean_nat_dec_eq(v_k_1939_, v_k_1941_);
if (v___x_1949_ == 0)
{
lean_object* v_impl_1950_; lean_object* v___x_1951_; 
v_impl_1950_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1939_, v_r_1944_);
v___x_1951_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1950_) == 0)
{
if (lean_obj_tag(v_l_1943_) == 0)
{
lean_object* v_size_1952_; lean_object* v_size_1953_; lean_object* v_k_1954_; lean_object* v_v_1955_; lean_object* v_l_1956_; lean_object* v_r_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_size_1952_ = lean_ctor_get(v_impl_1950_, 0);
lean_inc(v_size_1952_);
v_size_1953_ = lean_ctor_get(v_l_1943_, 0);
v_k_1954_ = lean_ctor_get(v_l_1943_, 1);
v_v_1955_ = lean_ctor_get(v_l_1943_, 2);
v_l_1956_ = lean_ctor_get(v_l_1943_, 3);
v_r_1957_ = lean_ctor_get(v_l_1943_, 4);
lean_inc(v_r_1957_);
v___x_1958_ = lean_unsigned_to_nat(3u);
v___x_1959_ = lean_nat_mul(v___x_1958_, v_size_1952_);
v___x_1960_ = lean_nat_dec_lt(v___x_1959_, v_size_1953_);
lean_dec(v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec(v_r_1957_);
v___x_1961_ = lean_nat_add(v___x_1951_, v_size_1953_);
v___x_1962_ = lean_nat_add(v___x_1961_, v_size_1952_);
lean_dec(v_size_1952_);
lean_dec(v___x_1961_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_impl_1950_);
lean_ctor_set(v___x_1946_, 0, v___x_1962_);
v___x_1964_ = v___x_1946_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_1965_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_1965_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_1965_, 4, v_impl_1950_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2031_; 
lean_inc(v_l_1956_);
lean_inc(v_v_1955_);
lean_inc(v_k_1954_);
lean_inc(v_size_1953_);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; lean_object* v_unused_2033_; lean_object* v_unused_2034_; lean_object* v_unused_2035_; lean_object* v_unused_2036_; 
v_unused_2032_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_l_1943_, 2);
lean_dec(v_unused_2034_);
v_unused_2035_ = lean_ctor_get(v_l_1943_, 1);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_l_1943_, 0);
lean_dec(v_unused_2036_);
v___x_1967_ = v_l_1943_;
v_isShared_1968_ = v_isSharedCheck_2031_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v_l_1943_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2031_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_size_1969_; lean_object* v_size_1970_; lean_object* v_k_1971_; lean_object* v_v_1972_; lean_object* v_l_1973_; lean_object* v_r_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_size_1969_ = lean_ctor_get(v_l_1956_, 0);
v_size_1970_ = lean_ctor_get(v_r_1957_, 0);
v_k_1971_ = lean_ctor_get(v_r_1957_, 1);
v_v_1972_ = lean_ctor_get(v_r_1957_, 2);
v_l_1973_ = lean_ctor_get(v_r_1957_, 3);
v_r_1974_ = lean_ctor_get(v_r_1957_, 4);
v___x_1975_ = lean_unsigned_to_nat(2u);
v___x_1976_ = lean_nat_mul(v___x_1975_, v_size_1969_);
v___x_1977_ = lean_nat_dec_lt(v_size_1970_, v___x_1976_);
lean_dec(v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2006_; 
lean_inc(v_r_1974_);
lean_inc(v_l_1973_);
lean_inc(v_v_1972_);
lean_inc(v_k_1971_);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_r_1957_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; lean_object* v_unused_2008_; lean_object* v_unused_2009_; lean_object* v_unused_2010_; lean_object* v_unused_2011_; 
v_unused_2007_ = lean_ctor_get(v_r_1957_, 4);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_r_1957_, 3);
lean_dec(v_unused_2008_);
v_unused_2009_ = lean_ctor_get(v_r_1957_, 2);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_r_1957_, 1);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_r_1957_, 0);
lean_dec(v_unused_2011_);
v___x_1979_ = v_r_1957_;
v_isShared_1980_ = v_isSharedCheck_2006_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_r_1957_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2006_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___x_1994_; lean_object* v___y_1996_; 
v___x_1981_ = lean_nat_add(v___x_1951_, v_size_1953_);
lean_dec(v_size_1953_);
v___x_1982_ = lean_nat_add(v___x_1981_, v_size_1952_);
lean_dec(v___x_1981_);
v___x_1994_ = lean_nat_add(v___x_1951_, v_size_1969_);
if (lean_obj_tag(v_l_1973_) == 0)
{
lean_object* v_size_2004_; 
v_size_2004_ = lean_ctor_get(v_l_1973_, 0);
lean_inc(v_size_2004_);
v___y_1996_ = v_size_2004_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2005_; 
v___x_2005_ = lean_unsigned_to_nat(0u);
v___y_1996_ = v___x_2005_;
goto v___jp_1995_;
}
v___jp_1983_:
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1987_ = lean_nat_add(v___y_1984_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec(v___y_1984_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v_impl_1950_);
lean_ctor_set(v___x_1979_, 3, v_r_1974_);
lean_ctor_set(v___x_1979_, 2, v_v_1942_);
lean_ctor_set(v___x_1979_, 1, v_k_1941_);
lean_ctor_set(v___x_1979_, 0, v___x_1987_);
v___x_1989_ = v___x_1979_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_r_1974_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_impl_1950_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 4, v___x_1989_);
lean_ctor_set(v___x_1967_, 3, v___y_1985_);
lean_ctor_set(v___x_1967_, 2, v_v_1972_);
lean_ctor_set(v___x_1967_, 1, v_k_1971_);
lean_ctor_set(v___x_1967_, 0, v___x_1982_);
v___x_1991_ = v___x_1967_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_k_1971_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_v_1972_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v___y_1985_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
v___jp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = lean_nat_add(v___x_1994_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec(v___x_1994_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_l_1973_);
lean_ctor_set(v___x_1946_, 3, v_l_1956_);
lean_ctor_set(v___x_1946_, 2, v_v_1955_);
lean_ctor_set(v___x_1946_, 1, v_k_1954_);
lean_ctor_set(v___x_1946_, 0, v___x_1997_);
v___x_1999_ = v___x_1946_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1954_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1955_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_l_1956_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_l_1973_);
v___x_1999_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_nat_add(v___x_1951_, v_size_1952_);
lean_dec(v_size_1952_);
if (lean_obj_tag(v_r_1974_) == 0)
{
lean_object* v_size_2001_; 
v_size_2001_ = lean_ctor_get(v_r_1974_, 0);
lean_inc(v_size_2001_);
v___y_1984_ = v___x_2000_;
v___y_1985_ = v___x_1999_;
v___y_1986_ = v_size_2001_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_unsigned_to_nat(0u);
v___y_1984_ = v___x_2000_;
v___y_1985_ = v___x_1999_;
v___y_1986_ = v___x_2002_;
goto v___jp_1983_;
}
}
}
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
lean_del_object(v___x_1946_);
v___x_2012_ = lean_nat_add(v___x_1951_, v_size_1953_);
lean_dec(v_size_1953_);
v___x_2013_ = lean_nat_add(v___x_2012_, v_size_1952_);
lean_dec(v___x_2012_);
v___x_2014_ = lean_nat_add(v___x_1951_, v_size_1952_);
lean_dec(v_size_1952_);
v___x_2015_ = lean_nat_add(v___x_2014_, v_size_1970_);
lean_dec(v___x_2014_);
lean_inc_ref(v_impl_1950_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 4, v_impl_1950_);
lean_ctor_set(v___x_1967_, 3, v_r_1957_);
lean_ctor_set(v___x_1967_, 2, v_v_1942_);
lean_ctor_set(v___x_1967_, 1, v_k_1941_);
lean_ctor_set(v___x_1967_, 0, v___x_2015_);
v___x_2017_ = v___x_1967_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2030_, 3, v_r_1957_);
lean_ctor_set(v_reuseFailAlloc_2030_, 4, v_impl_1950_);
v___x_2017_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
v_isSharedCheck_2024_ = !lean_is_exclusive(v_impl_1950_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; lean_object* v_unused_2026_; lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; 
v_unused_2025_ = lean_ctor_get(v_impl_1950_, 4);
lean_dec(v_unused_2025_);
v_unused_2026_ = lean_ctor_get(v_impl_1950_, 3);
lean_dec(v_unused_2026_);
v_unused_2027_ = lean_ctor_get(v_impl_1950_, 2);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_impl_1950_, 1);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_impl_1950_, 0);
lean_dec(v_unused_2029_);
v___x_2019_ = v_impl_1950_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_dec(v_impl_1950_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 4, v___x_2017_);
lean_ctor_set(v___x_2019_, 3, v_l_1956_);
lean_ctor_set(v___x_2019_, 2, v_v_1955_);
lean_ctor_set(v___x_2019_, 1, v_k_1954_);
lean_ctor_set(v___x_2019_, 0, v___x_2013_);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_k_1954_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_v_1955_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_l_1956_);
lean_ctor_set(v_reuseFailAlloc_2023_, 4, v___x_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v_size_2037_ = lean_ctor_get(v_impl_1950_, 0);
lean_inc(v_size_2037_);
v___x_2038_ = lean_nat_add(v___x_1951_, v_size_2037_);
lean_dec(v_size_2037_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_impl_1950_);
lean_ctor_set(v___x_1946_, 0, v___x_2038_);
v___x_2040_ = v___x_1946_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_impl_1950_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
if (lean_obj_tag(v_l_1943_) == 0)
{
lean_object* v_l_2042_; 
v_l_2042_ = lean_ctor_get(v_l_1943_, 3);
if (lean_obj_tag(v_l_2042_) == 0)
{
lean_object* v_r_2043_; 
lean_inc_ref(v_l_2042_);
v_r_2043_ = lean_ctor_get(v_l_1943_, 4);
lean_inc(v_r_2043_);
if (lean_obj_tag(v_r_2043_) == 0)
{
lean_object* v_size_2044_; lean_object* v_k_2045_; lean_object* v_v_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2059_; 
v_size_2044_ = lean_ctor_get(v_l_1943_, 0);
v_k_2045_ = lean_ctor_get(v_l_1943_, 1);
v_v_2046_ = lean_ctor_get(v_l_1943_, 2);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; lean_object* v_unused_2061_; 
v_unused_2060_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2060_);
v_unused_2061_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2061_);
v___x_2048_ = v_l_1943_;
v_isShared_2049_ = v_isSharedCheck_2059_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_v_2046_);
lean_inc(v_k_2045_);
lean_inc(v_size_2044_);
lean_dec(v_l_1943_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2059_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v_size_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v_size_2050_ = lean_ctor_get(v_r_2043_, 0);
v___x_2051_ = lean_nat_add(v___x_1951_, v_size_2044_);
lean_dec(v_size_2044_);
v___x_2052_ = lean_nat_add(v___x_1951_, v_size_2050_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 4, v_impl_1950_);
lean_ctor_set(v___x_2048_, 3, v_r_2043_);
lean_ctor_set(v___x_2048_, 2, v_v_1942_);
lean_ctor_set(v___x_2048_, 1, v_k_1941_);
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2058_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2058_, 3, v_r_2043_);
lean_ctor_set(v_reuseFailAlloc_2058_, 4, v_impl_1950_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_2054_);
lean_ctor_set(v___x_1946_, 3, v_l_2042_);
lean_ctor_set(v___x_1946_, 2, v_v_2046_);
lean_ctor_set(v___x_1946_, 1, v_k_2045_);
lean_ctor_set(v___x_1946_, 0, v___x_2051_);
v___x_2056_ = v___x_1946_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_k_2045_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_v_2046_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_l_2042_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_k_2062_; lean_object* v_v_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
v_k_2062_ = lean_ctor_get(v_l_1943_, 1);
v_v_2063_ = lean_ctor_get(v_l_1943_, 2);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; lean_object* v_unused_2076_; lean_object* v_unused_2077_; 
v_unused_2075_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2075_);
v_unused_2076_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_l_1943_, 0);
lean_dec(v_unused_2077_);
v___x_2065_ = v_l_1943_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_v_2063_);
lean_inc(v_k_2062_);
lean_dec(v_l_1943_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_unsigned_to_nat(3u);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 3, v_r_2043_);
lean_ctor_set(v___x_2065_, 2, v_v_1942_);
lean_ctor_set(v___x_2065_, 1, v_k_1941_);
lean_ctor_set(v___x_2065_, 0, v___x_1951_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_r_2043_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_r_2043_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_2069_);
lean_ctor_set(v___x_1946_, 3, v_l_2042_);
lean_ctor_set(v___x_1946_, 2, v_v_2063_);
lean_ctor_set(v___x_1946_, 1, v_k_2062_);
lean_ctor_set(v___x_1946_, 0, v___x_2067_);
v___x_2071_ = v___x_1946_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v_l_2042_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v_r_2078_; 
v_r_2078_ = lean_ctor_get(v_l_1943_, 4);
lean_inc(v_r_2078_);
if (lean_obj_tag(v_r_2078_) == 0)
{
lean_object* v_k_2079_; lean_object* v_v_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2103_; 
lean_inc(v_l_2042_);
v_k_2079_ = lean_ctor_get(v_l_1943_, 1);
v_v_2080_ = lean_ctor_get(v_l_1943_, 2);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; lean_object* v_unused_2105_; lean_object* v_unused_2106_; 
v_unused_2104_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_l_1943_, 0);
lean_dec(v_unused_2106_);
v___x_2082_ = v_l_1943_;
v_isShared_2083_ = v_isSharedCheck_2103_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_v_2080_);
lean_inc(v_k_2079_);
lean_dec(v_l_1943_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2103_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2099_; 
v_k_2084_ = lean_ctor_get(v_r_2078_, 1);
v_v_2085_ = lean_ctor_get(v_r_2078_, 2);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_r_2078_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; lean_object* v_unused_2101_; lean_object* v_unused_2102_; 
v_unused_2100_ = lean_ctor_get(v_r_2078_, 4);
lean_dec(v_unused_2100_);
v_unused_2101_ = lean_ctor_get(v_r_2078_, 3);
lean_dec(v_unused_2101_);
v_unused_2102_ = lean_ctor_get(v_r_2078_, 0);
lean_dec(v_unused_2102_);
v___x_2087_ = v_r_2078_;
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_dec(v_r_2078_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2099_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_unsigned_to_nat(3u);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 4, v_l_2042_);
lean_ctor_set(v___x_2087_, 3, v_l_2042_);
lean_ctor_set(v___x_2087_, 2, v_v_2080_);
lean_ctor_set(v___x_2087_, 1, v_k_2079_);
lean_ctor_set(v___x_2087_, 0, v___x_1951_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_k_2079_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_v_2080_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v_l_2042_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_l_2042_);
v___x_2091_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 4, v_l_2042_);
lean_ctor_set(v___x_2082_, 2, v_v_1942_);
lean_ctor_set(v___x_2082_, 1, v_k_1941_);
lean_ctor_set(v___x_2082_, 0, v___x_1951_);
v___x_2093_ = v___x_2082_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_l_2042_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_l_2042_);
v___x_2093_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_2093_);
lean_ctor_set(v___x_1946_, 3, v___x_2091_);
lean_ctor_set(v___x_1946_, 2, v_v_2085_);
lean_ctor_set(v___x_1946_, 1, v_k_2084_);
lean_ctor_set(v___x_1946_, 0, v___x_2089_);
v___x_2095_ = v___x_1946_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_unsigned_to_nat(2u);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_r_2078_);
lean_ctor_set(v___x_1946_, 0, v___x_2107_);
v___x_2109_ = v___x_1946_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_2110_, 4, v_r_2078_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v___x_2112_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_l_1943_);
lean_ctor_set(v___x_1946_, 0, v___x_1951_);
v___x_2112_ = v___x_1946_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_l_1943_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_del_object(v___x_1946_);
lean_dec(v_v_1942_);
lean_dec(v_k_1941_);
if (lean_obj_tag(v_l_1943_) == 0)
{
if (lean_obj_tag(v_r_1944_) == 0)
{
lean_object* v_size_2114_; lean_object* v_k_2115_; lean_object* v_v_2116_; lean_object* v_l_2117_; lean_object* v_r_2118_; lean_object* v_size_2119_; lean_object* v_k_2120_; lean_object* v_v_2121_; lean_object* v_l_2122_; lean_object* v_r_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_size_2114_ = lean_ctor_get(v_l_1943_, 0);
v_k_2115_ = lean_ctor_get(v_l_1943_, 1);
v_v_2116_ = lean_ctor_get(v_l_1943_, 2);
v_l_2117_ = lean_ctor_get(v_l_1943_, 3);
v_r_2118_ = lean_ctor_get(v_l_1943_, 4);
lean_inc(v_r_2118_);
v_size_2119_ = lean_ctor_get(v_r_1944_, 0);
v_k_2120_ = lean_ctor_get(v_r_1944_, 1);
v_v_2121_ = lean_ctor_get(v_r_1944_, 2);
v_l_2122_ = lean_ctor_get(v_r_1944_, 3);
lean_inc(v_l_2122_);
v_r_2123_ = lean_ctor_get(v_r_1944_, 4);
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_nat_dec_lt(v_size_2114_, v_size_2119_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2261_; 
lean_inc(v_l_2117_);
lean_inc(v_v_2116_);
lean_inc(v_k_2115_);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; lean_object* v_unused_2263_; lean_object* v_unused_2264_; lean_object* v_unused_2265_; lean_object* v_unused_2266_; 
v_unused_2262_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2263_);
v_unused_2264_ = lean_ctor_get(v_l_1943_, 2);
lean_dec(v_unused_2264_);
v_unused_2265_ = lean_ctor_get(v_l_1943_, 1);
lean_dec(v_unused_2265_);
v_unused_2266_ = lean_ctor_get(v_l_1943_, 0);
lean_dec(v_unused_2266_);
v___x_2127_ = v_l_1943_;
v_isShared_2128_ = v_isSharedCheck_2261_;
goto v_resetjp_2126_;
}
else
{
lean_dec(v_l_1943_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2261_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v_tree_2130_; 
v___x_2129_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2115_, v_v_2116_, v_l_2117_, v_r_2118_);
v_tree_2130_ = lean_ctor_get(v___x_2129_, 2);
lean_inc(v_tree_2130_);
if (lean_obj_tag(v_tree_2130_) == 0)
{
lean_object* v_k_2131_; lean_object* v_v_2132_; lean_object* v_size_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v_k_2131_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_k_2131_);
v_v_2132_ = lean_ctor_get(v___x_2129_, 1);
lean_inc(v_v_2132_);
lean_dec_ref(v___x_2129_);
v_size_2133_ = lean_ctor_get(v_tree_2130_, 0);
v___x_2134_ = lean_unsigned_to_nat(3u);
v___x_2135_ = lean_nat_mul(v___x_2134_, v_size_2133_);
v___x_2136_ = lean_nat_dec_lt(v___x_2135_, v_size_2119_);
lean_dec(v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
lean_dec(v_l_2122_);
v___x_2137_ = lean_nat_add(v___x_2124_, v_size_2133_);
v___x_2138_ = lean_nat_add(v___x_2137_, v_size_2119_);
lean_dec(v___x_2137_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v_r_1944_);
lean_ctor_set(v___x_2127_, 3, v_tree_2130_);
lean_ctor_set(v___x_2127_, 2, v_v_2132_);
lean_ctor_set(v___x_2127_, 1, v_k_2131_);
lean_ctor_set(v___x_2127_, 0, v___x_2138_);
v___x_2140_ = v___x_2127_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_k_2131_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_v_2132_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_tree_2130_);
lean_ctor_set(v_reuseFailAlloc_2141_, 4, v_r_1944_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
else
{
lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2196_; 
lean_inc(v_r_2123_);
lean_inc(v_v_2121_);
lean_inc(v_k_2120_);
lean_inc(v_size_2119_);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; lean_object* v_unused_2198_; lean_object* v_unused_2199_; lean_object* v_unused_2200_; lean_object* v_unused_2201_; 
v_unused_2197_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2197_);
v_unused_2198_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2198_);
v_unused_2199_ = lean_ctor_get(v_r_1944_, 2);
lean_dec(v_unused_2199_);
v_unused_2200_ = lean_ctor_get(v_r_1944_, 1);
lean_dec(v_unused_2200_);
v_unused_2201_ = lean_ctor_get(v_r_1944_, 0);
lean_dec(v_unused_2201_);
v___x_2143_ = v_r_1944_;
v_isShared_2144_ = v_isSharedCheck_2196_;
goto v_resetjp_2142_;
}
else
{
lean_dec(v_r_1944_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2196_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_size_2145_; lean_object* v_k_2146_; lean_object* v_v_2147_; lean_object* v_l_2148_; lean_object* v_r_2149_; lean_object* v_size_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v_size_2145_ = lean_ctor_get(v_l_2122_, 0);
v_k_2146_ = lean_ctor_get(v_l_2122_, 1);
v_v_2147_ = lean_ctor_get(v_l_2122_, 2);
v_l_2148_ = lean_ctor_get(v_l_2122_, 3);
v_r_2149_ = lean_ctor_get(v_l_2122_, 4);
v_size_2150_ = lean_ctor_get(v_r_2123_, 0);
v___x_2151_ = lean_unsigned_to_nat(2u);
v___x_2152_ = lean_nat_mul(v___x_2151_, v_size_2150_);
v___x_2153_ = lean_nat_dec_lt(v_size_2145_, v___x_2152_);
lean_dec(v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2181_; 
lean_inc(v_r_2149_);
lean_inc(v_l_2148_);
lean_inc(v_v_2147_);
lean_inc(v_k_2146_);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_l_2122_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; 
v_unused_2182_ = lean_ctor_get(v_l_2122_, 4);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_l_2122_, 3);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_l_2122_, 2);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_l_2122_, 1);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_l_2122_, 0);
lean_dec(v_unused_2186_);
v___x_2155_ = v_l_2122_;
v_isShared_2156_ = v_isSharedCheck_2181_;
goto v_resetjp_2154_;
}
else
{
lean_dec(v_l_2122_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2181_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2171_; 
v___x_2157_ = lean_nat_add(v___x_2124_, v_size_2133_);
v___x_2158_ = lean_nat_add(v___x_2157_, v_size_2119_);
lean_dec(v_size_2119_);
if (lean_obj_tag(v_l_2148_) == 0)
{
lean_object* v_size_2179_; 
v_size_2179_ = lean_ctor_get(v_l_2148_, 0);
lean_inc(v_size_2179_);
v___y_2171_ = v_size_2179_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_unsigned_to_nat(0u);
v___y_2171_ = v___x_2180_;
goto v___jp_2170_;
}
v___jp_2159_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = lean_nat_add(v___y_2160_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec(v___y_2160_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 4, v_r_2123_);
lean_ctor_set(v___x_2155_, 3, v_r_2149_);
lean_ctor_set(v___x_2155_, 2, v_v_2121_);
lean_ctor_set(v___x_2155_, 1, v_k_2120_);
lean_ctor_set(v___x_2155_, 0, v___x_2163_);
v___x_2165_ = v___x_2155_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_k_2120_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_v_2121_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_r_2149_);
lean_ctor_set(v_reuseFailAlloc_2169_, 4, v_r_2123_);
v___x_2165_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 4, v___x_2165_);
lean_ctor_set(v___x_2143_, 3, v___y_2161_);
lean_ctor_set(v___x_2143_, 2, v_v_2147_);
lean_ctor_set(v___x_2143_, 1, v_k_2146_);
lean_ctor_set(v___x_2143_, 0, v___x_2158_);
v___x_2167_ = v___x_2143_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_k_2146_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_v_2147_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v___y_2161_);
lean_ctor_set(v_reuseFailAlloc_2168_, 4, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
v___jp_2170_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = lean_nat_add(v___x_2157_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec(v___x_2157_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v_l_2148_);
lean_ctor_set(v___x_2127_, 3, v_tree_2130_);
lean_ctor_set(v___x_2127_, 2, v_v_2132_);
lean_ctor_set(v___x_2127_, 1, v_k_2131_);
lean_ctor_set(v___x_2127_, 0, v___x_2172_);
v___x_2174_ = v___x_2127_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2172_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_k_2131_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_v_2132_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v_tree_2130_);
lean_ctor_set(v_reuseFailAlloc_2178_, 4, v_l_2148_);
v___x_2174_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_nat_add(v___x_2124_, v_size_2150_);
if (lean_obj_tag(v_r_2149_) == 0)
{
lean_object* v_size_2176_; 
v_size_2176_ = lean_ctor_get(v_r_2149_, 0);
lean_inc(v_size_2176_);
v___y_2160_ = v___x_2175_;
v___y_2161_ = v___x_2174_;
v___y_2162_ = v_size_2176_;
goto v___jp_2159_;
}
else
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_unsigned_to_nat(0u);
v___y_2160_ = v___x_2175_;
v___y_2161_ = v___x_2174_;
v___y_2162_ = v___x_2177_;
goto v___jp_2159_;
}
}
}
}
}
else
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v___x_2187_ = lean_nat_add(v___x_2124_, v_size_2133_);
v___x_2188_ = lean_nat_add(v___x_2187_, v_size_2119_);
lean_dec(v_size_2119_);
v___x_2189_ = lean_nat_add(v___x_2187_, v_size_2145_);
lean_dec(v___x_2187_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 4, v_l_2122_);
lean_ctor_set(v___x_2143_, 3, v_tree_2130_);
lean_ctor_set(v___x_2143_, 2, v_v_2132_);
lean_ctor_set(v___x_2143_, 1, v_k_2131_);
lean_ctor_set(v___x_2143_, 0, v___x_2189_);
v___x_2191_ = v___x_2143_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_k_2131_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_v_2132_);
lean_ctor_set(v_reuseFailAlloc_2195_, 3, v_tree_2130_);
lean_ctor_set(v_reuseFailAlloc_2195_, 4, v_l_2122_);
v___x_2191_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v_r_2123_);
lean_ctor_set(v___x_2127_, 3, v___x_2191_);
lean_ctor_set(v___x_2127_, 2, v_v_2121_);
lean_ctor_set(v___x_2127_, 1, v_k_2120_);
lean_ctor_set(v___x_2127_, 0, v___x_2188_);
v___x_2193_ = v___x_2127_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_k_2120_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_v_2121_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2194_, 4, v_r_2123_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
else
{
lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2255_; 
lean_inc(v_r_2123_);
lean_inc(v_v_2121_);
lean_inc(v_k_2120_);
lean_inc(v_size_2119_);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; lean_object* v_unused_2257_; lean_object* v_unused_2258_; lean_object* v_unused_2259_; lean_object* v_unused_2260_; 
v_unused_2256_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_r_1944_, 2);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_r_1944_, 1);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_r_1944_, 0);
lean_dec(v_unused_2260_);
v___x_2203_ = v_r_1944_;
v_isShared_2204_ = v_isSharedCheck_2255_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v_r_1944_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2255_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
if (lean_obj_tag(v_l_2122_) == 0)
{
if (lean_obj_tag(v_r_2123_) == 0)
{
lean_object* v_k_2205_; lean_object* v_v_2206_; lean_object* v_size_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v_k_2205_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_k_2205_);
v_v_2206_ = lean_ctor_get(v___x_2129_, 1);
lean_inc(v_v_2206_);
lean_dec_ref(v___x_2129_);
v_size_2207_ = lean_ctor_get(v_l_2122_, 0);
v___x_2208_ = lean_nat_add(v___x_2124_, v_size_2119_);
lean_dec(v_size_2119_);
v___x_2209_ = lean_nat_add(v___x_2124_, v_size_2207_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 4, v_l_2122_);
lean_ctor_set(v___x_2203_, 3, v_tree_2130_);
lean_ctor_set(v___x_2203_, 2, v_v_2206_);
lean_ctor_set(v___x_2203_, 1, v_k_2205_);
lean_ctor_set(v___x_2203_, 0, v___x_2209_);
v___x_2211_ = v___x_2203_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_k_2205_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_v_2206_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_tree_2130_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_l_2122_);
v___x_2211_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2213_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v_r_2123_);
lean_ctor_set(v___x_2127_, 3, v___x_2211_);
lean_ctor_set(v___x_2127_, 2, v_v_2121_);
lean_ctor_set(v___x_2127_, 1, v_k_2120_);
lean_ctor_set(v___x_2127_, 0, v___x_2208_);
v___x_2213_ = v___x_2127_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_k_2120_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_v_2121_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_r_2123_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_object* v_k_2216_; lean_object* v_v_2217_; lean_object* v_k_2218_; lean_object* v_v_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_size_2119_);
v_k_2216_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_k_2216_);
v_v_2217_ = lean_ctor_get(v___x_2129_, 1);
lean_inc(v_v_2217_);
lean_dec_ref(v___x_2129_);
v_k_2218_ = lean_ctor_get(v_l_2122_, 1);
v_v_2219_ = lean_ctor_get(v_l_2122_, 2);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_l_2122_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; lean_object* v_unused_2235_; lean_object* v_unused_2236_; 
v_unused_2234_ = lean_ctor_get(v_l_2122_, 4);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_l_2122_, 3);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v_l_2122_, 0);
lean_dec(v_unused_2236_);
v___x_2221_ = v_l_2122_;
v_isShared_2222_ = v_isSharedCheck_2233_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_v_2219_);
lean_inc(v_k_2218_);
lean_dec(v_l_2122_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2233_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_unsigned_to_nat(3u);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 4, v_r_2123_);
lean_ctor_set(v___x_2221_, 3, v_r_2123_);
lean_ctor_set(v___x_2221_, 2, v_v_2217_);
lean_ctor_set(v___x_2221_, 1, v_k_2216_);
lean_ctor_set(v___x_2221_, 0, v___x_2124_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_k_2216_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_v_2217_);
lean_ctor_set(v_reuseFailAlloc_2232_, 3, v_r_2123_);
lean_ctor_set(v_reuseFailAlloc_2232_, 4, v_r_2123_);
v___x_2225_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 3, v_r_2123_);
lean_ctor_set(v___x_2203_, 0, v___x_2124_);
v___x_2227_ = v___x_2203_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_k_2120_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_v_2121_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_r_2123_);
lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_r_2123_);
v___x_2227_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2229_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v___x_2227_);
lean_ctor_set(v___x_2127_, 3, v___x_2225_);
lean_ctor_set(v___x_2127_, 2, v_v_2219_);
lean_ctor_set(v___x_2127_, 1, v_k_2218_);
lean_ctor_set(v___x_2127_, 0, v___x_2223_);
v___x_2229_ = v___x_2127_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_k_2218_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_v_2219_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2123_) == 0)
{
lean_object* v_k_2237_; lean_object* v_v_2238_; lean_object* v___x_2239_; lean_object* v___x_2241_; 
lean_dec(v_size_2119_);
v_k_2237_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_k_2237_);
v_v_2238_ = lean_ctor_get(v___x_2129_, 1);
lean_inc(v_v_2238_);
lean_dec_ref(v___x_2129_);
v___x_2239_ = lean_unsigned_to_nat(3u);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 4, v_l_2122_);
lean_ctor_set(v___x_2203_, 2, v_v_2238_);
lean_ctor_set(v___x_2203_, 1, v_k_2237_);
lean_ctor_set(v___x_2203_, 0, v___x_2124_);
v___x_2241_ = v___x_2203_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_k_2237_);
lean_ctor_set(v_reuseFailAlloc_2245_, 2, v_v_2238_);
lean_ctor_set(v_reuseFailAlloc_2245_, 3, v_l_2122_);
lean_ctor_set(v_reuseFailAlloc_2245_, 4, v_l_2122_);
v___x_2241_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
lean_object* v___x_2243_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v_r_2123_);
lean_ctor_set(v___x_2127_, 3, v___x_2241_);
lean_ctor_set(v___x_2127_, 2, v_v_2121_);
lean_ctor_set(v___x_2127_, 1, v_k_2120_);
lean_ctor_set(v___x_2127_, 0, v___x_2239_);
v___x_2243_ = v___x_2127_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_k_2120_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_v_2121_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_r_2123_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
else
{
lean_object* v_k_2246_; lean_object* v_v_2247_; lean_object* v___x_2249_; 
v_k_2246_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_k_2246_);
v_v_2247_ = lean_ctor_get(v___x_2129_, 1);
lean_inc(v_v_2247_);
lean_dec_ref(v___x_2129_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 3, v_r_2123_);
v___x_2249_ = v___x_2203_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_size_2119_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2120_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2121_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_r_2123_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_r_2123_);
v___x_2249_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_unsigned_to_nat(2u);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v___x_2249_);
lean_ctor_set(v___x_2127_, 3, v_r_2123_);
lean_ctor_set(v___x_2127_, 2, v_v_2247_);
lean_ctor_set(v___x_2127_, 1, v_k_2246_);
lean_ctor_set(v___x_2127_, 0, v___x_2250_);
v___x_2252_ = v___x_2127_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_k_2246_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_v_2247_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_r_2123_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v___x_2249_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
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
lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2419_; 
lean_inc(v_r_2123_);
lean_inc(v_v_2121_);
lean_inc(v_k_2120_);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; lean_object* v_unused_2421_; lean_object* v_unused_2422_; lean_object* v_unused_2423_; lean_object* v_unused_2424_; 
v_unused_2420_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_r_1944_, 2);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_r_1944_, 1);
lean_dec(v_unused_2423_);
v_unused_2424_ = lean_ctor_get(v_r_1944_, 0);
lean_dec(v_unused_2424_);
v___x_2268_ = v_r_1944_;
v_isShared_2269_ = v_isSharedCheck_2419_;
goto v_resetjp_2267_;
}
else
{
lean_dec(v_r_1944_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2419_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v_tree_2271_; 
v___x_2270_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2120_, v_v_2121_, v_l_2122_, v_r_2123_);
v_tree_2271_ = lean_ctor_get(v___x_2270_, 2);
lean_inc(v_tree_2271_);
if (lean_obj_tag(v_tree_2271_) == 0)
{
lean_object* v_k_2272_; lean_object* v_v_2273_; lean_object* v_size_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_k_2272_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_k_2272_);
v_v_2273_ = lean_ctor_get(v___x_2270_, 1);
lean_inc(v_v_2273_);
lean_dec_ref(v___x_2270_);
v_size_2274_ = lean_ctor_get(v_tree_2271_, 0);
v___x_2275_ = lean_unsigned_to_nat(3u);
v___x_2276_ = lean_nat_mul(v___x_2275_, v_size_2274_);
v___x_2277_ = lean_nat_dec_lt(v___x_2276_, v_size_2114_);
lean_dec(v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2281_; 
lean_dec(v_r_2118_);
v___x_2278_ = lean_nat_add(v___x_2124_, v_size_2114_);
v___x_2279_ = lean_nat_add(v___x_2278_, v_size_2274_);
lean_dec(v___x_2278_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_tree_2271_);
lean_ctor_set(v___x_2268_, 3, v_l_1943_);
lean_ctor_set(v___x_2268_, 2, v_v_2273_);
lean_ctor_set(v___x_2268_, 1, v_k_2272_);
lean_ctor_set(v___x_2268_, 0, v___x_2279_);
v___x_2281_ = v___x_2268_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_k_2272_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_v_2273_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_tree_2271_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
else
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2348_; 
lean_inc(v_l_2117_);
lean_inc(v_v_2116_);
lean_inc(v_k_2115_);
lean_inc(v_size_2114_);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2348_ == 0)
{
lean_object* v_unused_2349_; lean_object* v_unused_2350_; lean_object* v_unused_2351_; lean_object* v_unused_2352_; lean_object* v_unused_2353_; 
v_unused_2349_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2349_);
v_unused_2350_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2350_);
v_unused_2351_ = lean_ctor_get(v_l_1943_, 2);
lean_dec(v_unused_2351_);
v_unused_2352_ = lean_ctor_get(v_l_1943_, 1);
lean_dec(v_unused_2352_);
v_unused_2353_ = lean_ctor_get(v_l_1943_, 0);
lean_dec(v_unused_2353_);
v___x_2284_ = v_l_1943_;
v_isShared_2285_ = v_isSharedCheck_2348_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v_l_1943_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2348_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_size_2286_; lean_object* v_size_2287_; lean_object* v_k_2288_; lean_object* v_v_2289_; lean_object* v_l_2290_; lean_object* v_r_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v_size_2286_ = lean_ctor_get(v_l_2117_, 0);
v_size_2287_ = lean_ctor_get(v_r_2118_, 0);
v_k_2288_ = lean_ctor_get(v_r_2118_, 1);
v_v_2289_ = lean_ctor_get(v_r_2118_, 2);
v_l_2290_ = lean_ctor_get(v_r_2118_, 3);
v_r_2291_ = lean_ctor_get(v_r_2118_, 4);
v___x_2292_ = lean_unsigned_to_nat(2u);
v___x_2293_ = lean_nat_mul(v___x_2292_, v_size_2286_);
v___x_2294_ = lean_nat_dec_lt(v_size_2287_, v___x_2293_);
lean_dec(v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2332_; 
lean_inc(v_r_2291_);
lean_inc(v_l_2290_);
lean_inc(v_v_2289_);
lean_inc(v_k_2288_);
lean_del_object(v___x_2284_);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_r_2118_);
if (v_isSharedCheck_2332_ == 0)
{
lean_object* v_unused_2333_; lean_object* v_unused_2334_; lean_object* v_unused_2335_; lean_object* v_unused_2336_; lean_object* v_unused_2337_; 
v_unused_2333_ = lean_ctor_get(v_r_2118_, 4);
lean_dec(v_unused_2333_);
v_unused_2334_ = lean_ctor_get(v_r_2118_, 3);
lean_dec(v_unused_2334_);
v_unused_2335_ = lean_ctor_get(v_r_2118_, 2);
lean_dec(v_unused_2335_);
v_unused_2336_ = lean_ctor_get(v_r_2118_, 1);
lean_dec(v_unused_2336_);
v_unused_2337_ = lean_ctor_get(v_r_2118_, 0);
lean_dec(v_unused_2337_);
v___x_2296_ = v_r_2118_;
v_isShared_2297_ = v_isSharedCheck_2332_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v_r_2118_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2332_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___x_2320_; lean_object* v___y_2322_; 
v___x_2298_ = lean_nat_add(v___x_2124_, v_size_2114_);
lean_dec(v_size_2114_);
v___x_2299_ = lean_nat_add(v___x_2298_, v_size_2274_);
lean_dec(v___x_2298_);
v___x_2320_ = lean_nat_add(v___x_2124_, v_size_2286_);
if (lean_obj_tag(v_l_2290_) == 0)
{
lean_object* v_size_2330_; 
v_size_2330_ = lean_ctor_get(v_l_2290_, 0);
lean_inc(v_size_2330_);
v___y_2322_ = v_size_2330_;
goto v___jp_2321_;
}
else
{
lean_object* v___x_2331_; 
v___x_2331_ = lean_unsigned_to_nat(0u);
v___y_2322_ = v___x_2331_;
goto v___jp_2321_;
}
v___jp_2300_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_nat_add(v___y_2301_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec(v___y_2301_);
lean_inc_ref(v_tree_2271_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 4, v_tree_2271_);
lean_ctor_set(v___x_2296_, 3, v_r_2291_);
lean_ctor_set(v___x_2296_, 2, v_v_2273_);
lean_ctor_set(v___x_2296_, 1, v_k_2272_);
lean_ctor_set(v___x_2296_, 0, v___x_2304_);
v___x_2306_ = v___x_2296_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_k_2272_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_v_2273_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_r_2291_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_tree_2271_);
v___x_2306_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
v_isSharedCheck_2313_ = !lean_is_exclusive(v_tree_2271_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; lean_object* v_unused_2315_; lean_object* v_unused_2316_; lean_object* v_unused_2317_; lean_object* v_unused_2318_; 
v_unused_2314_ = lean_ctor_get(v_tree_2271_, 4);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_tree_2271_, 3);
lean_dec(v_unused_2315_);
v_unused_2316_ = lean_ctor_get(v_tree_2271_, 2);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_tree_2271_, 1);
lean_dec(v_unused_2317_);
v_unused_2318_ = lean_ctor_get(v_tree_2271_, 0);
lean_dec(v_unused_2318_);
v___x_2308_ = v_tree_2271_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_dec(v_tree_2271_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 4, v___x_2306_);
lean_ctor_set(v___x_2308_, 3, v___y_2302_);
lean_ctor_set(v___x_2308_, 2, v_v_2289_);
lean_ctor_set(v___x_2308_, 1, v_k_2288_);
lean_ctor_set(v___x_2308_, 0, v___x_2299_);
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_k_2288_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_v_2289_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v___y_2302_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v___x_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
v___jp_2321_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = lean_nat_add(v___x_2320_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec(v___x_2320_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_l_2290_);
lean_ctor_set(v___x_2268_, 3, v_l_2117_);
lean_ctor_set(v___x_2268_, 2, v_v_2116_);
lean_ctor_set(v___x_2268_, 1, v_k_2115_);
lean_ctor_set(v___x_2268_, 0, v___x_2323_);
v___x_2325_ = v___x_2268_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2329_, 3, v_l_2117_);
lean_ctor_set(v_reuseFailAlloc_2329_, 4, v_l_2290_);
v___x_2325_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; 
v___x_2326_ = lean_nat_add(v___x_2124_, v_size_2274_);
if (lean_obj_tag(v_r_2291_) == 0)
{
lean_object* v_size_2327_; 
v_size_2327_ = lean_ctor_get(v_r_2291_, 0);
lean_inc(v_size_2327_);
v___y_2301_ = v___x_2326_;
v___y_2302_ = v___x_2325_;
v___y_2303_ = v_size_2327_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_unsigned_to_nat(0u);
v___y_2301_ = v___x_2326_;
v___y_2302_ = v___x_2325_;
v___y_2303_ = v___x_2328_;
goto v___jp_2300_;
}
}
}
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2338_ = lean_nat_add(v___x_2124_, v_size_2114_);
lean_dec(v_size_2114_);
v___x_2339_ = lean_nat_add(v___x_2338_, v_size_2274_);
lean_dec(v___x_2338_);
v___x_2340_ = lean_nat_add(v___x_2124_, v_size_2274_);
v___x_2341_ = lean_nat_add(v___x_2340_, v_size_2287_);
lean_dec(v___x_2340_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_tree_2271_);
lean_ctor_set(v___x_2268_, 3, v_r_2118_);
lean_ctor_set(v___x_2268_, 2, v_v_2273_);
lean_ctor_set(v___x_2268_, 1, v_k_2272_);
lean_ctor_set(v___x_2268_, 0, v___x_2341_);
v___x_2343_ = v___x_2268_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_k_2272_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_v_2273_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_r_2118_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_tree_2271_);
v___x_2343_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 4, v___x_2343_);
lean_ctor_set(v___x_2284_, 0, v___x_2339_);
v___x_2345_ = v___x_2284_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v_l_2117_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2117_) == 0)
{
lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2377_; 
lean_inc_ref(v_l_2117_);
lean_inc(v_v_2116_);
lean_inc(v_k_2115_);
lean_inc(v_size_2114_);
v_isSharedCheck_2377_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; lean_object* v_unused_2382_; 
v_unused_2378_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_l_1943_, 2);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_l_1943_, 1);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_l_1943_, 0);
lean_dec(v_unused_2382_);
v___x_2355_ = v_l_1943_;
v_isShared_2356_ = v_isSharedCheck_2377_;
goto v_resetjp_2354_;
}
else
{
lean_dec(v_l_1943_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2377_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
if (lean_obj_tag(v_r_2118_) == 0)
{
lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v_size_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v_k_2357_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_k_2357_);
v_v_2358_ = lean_ctor_get(v___x_2270_, 1);
lean_inc(v_v_2358_);
lean_dec_ref(v___x_2270_);
v_size_2359_ = lean_ctor_get(v_r_2118_, 0);
v___x_2360_ = lean_nat_add(v___x_2124_, v_size_2114_);
lean_dec(v_size_2114_);
v___x_2361_ = lean_nat_add(v___x_2124_, v_size_2359_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_tree_2271_);
lean_ctor_set(v___x_2268_, 3, v_r_2118_);
lean_ctor_set(v___x_2268_, 2, v_v_2358_);
lean_ctor_set(v___x_2268_, 1, v_k_2357_);
lean_ctor_set(v___x_2268_, 0, v___x_2361_);
v___x_2363_ = v___x_2268_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_k_2357_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v_v_2358_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v_r_2118_);
lean_ctor_set(v_reuseFailAlloc_2367_, 4, v_tree_2271_);
v___x_2363_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 4, v___x_2363_);
lean_ctor_set(v___x_2355_, 0, v___x_2360_);
v___x_2365_ = v___x_2355_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_l_2117_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_object* v_k_2368_; lean_object* v_v_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
lean_dec(v_size_2114_);
v_k_2368_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_k_2368_);
v_v_2369_ = lean_ctor_get(v___x_2270_, 1);
lean_inc(v_v_2369_);
lean_dec_ref(v___x_2270_);
v___x_2370_ = lean_unsigned_to_nat(3u);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_r_2118_);
lean_ctor_set(v___x_2268_, 3, v_r_2118_);
lean_ctor_set(v___x_2268_, 2, v_v_2369_);
lean_ctor_set(v___x_2268_, 1, v_k_2368_);
lean_ctor_set(v___x_2268_, 0, v___x_2124_);
v___x_2372_ = v___x_2268_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_k_2368_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_v_2369_);
lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_r_2118_);
lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_r_2118_);
v___x_2372_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2374_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 4, v___x_2372_);
lean_ctor_set(v___x_2355_, 0, v___x_2370_);
v___x_2374_ = v___x_2355_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_l_2117_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2118_) == 0)
{
lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2407_; 
lean_inc(v_l_2117_);
lean_inc(v_v_2116_);
lean_inc(v_k_2115_);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_l_1943_);
if (v_isSharedCheck_2407_ == 0)
{
lean_object* v_unused_2408_; lean_object* v_unused_2409_; lean_object* v_unused_2410_; lean_object* v_unused_2411_; lean_object* v_unused_2412_; 
v_unused_2408_ = lean_ctor_get(v_l_1943_, 4);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_l_1943_, 3);
lean_dec(v_unused_2409_);
v_unused_2410_ = lean_ctor_get(v_l_1943_, 2);
lean_dec(v_unused_2410_);
v_unused_2411_ = lean_ctor_get(v_l_1943_, 1);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_l_1943_, 0);
lean_dec(v_unused_2412_);
v___x_2384_ = v_l_1943_;
v_isShared_2385_ = v_isSharedCheck_2407_;
goto v_resetjp_2383_;
}
else
{
lean_dec(v_l_1943_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2407_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_k_2386_; lean_object* v_v_2387_; lean_object* v_k_2388_; lean_object* v_v_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2403_; 
v_k_2386_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_k_2386_);
v_v_2387_ = lean_ctor_get(v___x_2270_, 1);
lean_inc(v_v_2387_);
lean_dec_ref(v___x_2270_);
v_k_2388_ = lean_ctor_get(v_r_2118_, 1);
v_v_2389_ = lean_ctor_get(v_r_2118_, 2);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_r_2118_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; lean_object* v_unused_2405_; lean_object* v_unused_2406_; 
v_unused_2404_ = lean_ctor_get(v_r_2118_, 4);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_r_2118_, 3);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_r_2118_, 0);
lean_dec(v_unused_2406_);
v___x_2391_ = v_r_2118_;
v_isShared_2392_ = v_isSharedCheck_2403_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_v_2389_);
lean_inc(v_k_2388_);
lean_dec(v_r_2118_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2403_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = lean_unsigned_to_nat(3u);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 4, v_l_2117_);
lean_ctor_set(v___x_2391_, 3, v_l_2117_);
lean_ctor_set(v___x_2391_, 2, v_v_2116_);
lean_ctor_set(v___x_2391_, 1, v_k_2115_);
lean_ctor_set(v___x_2391_, 0, v___x_2124_);
v___x_2395_ = v___x_2391_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_k_2115_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v_v_2116_);
lean_ctor_set(v_reuseFailAlloc_2402_, 3, v_l_2117_);
lean_ctor_set(v_reuseFailAlloc_2402_, 4, v_l_2117_);
v___x_2395_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2397_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_l_2117_);
lean_ctor_set(v___x_2268_, 3, v_l_2117_);
lean_ctor_set(v___x_2268_, 2, v_v_2387_);
lean_ctor_set(v___x_2268_, 1, v_k_2386_);
lean_ctor_set(v___x_2268_, 0, v___x_2124_);
v___x_2397_ = v___x_2268_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_k_2386_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_v_2387_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_l_2117_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_l_2117_);
v___x_2397_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2399_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 4, v___x_2397_);
lean_ctor_set(v___x_2384_, 3, v___x_2395_);
lean_ctor_set(v___x_2384_, 2, v_v_2389_);
lean_ctor_set(v___x_2384_, 1, v_k_2388_);
lean_ctor_set(v___x_2384_, 0, v___x_2393_);
v___x_2399_ = v___x_2384_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_k_2388_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_v_2389_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
}
else
{
lean_object* v_k_2413_; lean_object* v_v_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v_k_2413_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_k_2413_);
v_v_2414_ = lean_ctor_get(v___x_2270_, 1);
lean_inc(v_v_2414_);
lean_dec_ref(v___x_2270_);
v___x_2415_ = lean_unsigned_to_nat(2u);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_r_2118_);
lean_ctor_set(v___x_2268_, 3, v_l_1943_);
lean_ctor_set(v___x_2268_, 2, v_v_2414_);
lean_ctor_set(v___x_2268_, 1, v_k_2413_);
lean_ctor_set(v___x_2268_, 0, v___x_2415_);
v___x_2417_ = v___x_2268_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_k_2413_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_v_2414_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_l_1943_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_r_2118_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
}
}
else
{
return v_l_1943_;
}
}
else
{
return v_r_1944_;
}
}
}
else
{
lean_object* v_impl_2425_; lean_object* v___x_2426_; 
v_impl_2425_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1939_, v_l_1943_);
v___x_2426_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2425_) == 0)
{
if (lean_obj_tag(v_r_1944_) == 0)
{
lean_object* v_size_2427_; lean_object* v_size_2428_; lean_object* v_k_2429_; lean_object* v_v_2430_; lean_object* v_l_2431_; lean_object* v_r_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v_size_2427_ = lean_ctor_get(v_impl_2425_, 0);
lean_inc(v_size_2427_);
v_size_2428_ = lean_ctor_get(v_r_1944_, 0);
v_k_2429_ = lean_ctor_get(v_r_1944_, 1);
v_v_2430_ = lean_ctor_get(v_r_1944_, 2);
v_l_2431_ = lean_ctor_get(v_r_1944_, 3);
lean_inc(v_l_2431_);
v_r_2432_ = lean_ctor_get(v_r_1944_, 4);
v___x_2433_ = lean_unsigned_to_nat(3u);
v___x_2434_ = lean_nat_mul(v___x_2433_, v_size_2427_);
v___x_2435_ = lean_nat_dec_lt(v___x_2434_, v_size_2428_);
lean_dec(v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
lean_dec(v_l_2431_);
v___x_2436_ = lean_nat_add(v___x_2426_, v_size_2427_);
lean_dec(v_size_2427_);
v___x_2437_ = lean_nat_add(v___x_2436_, v_size_2428_);
lean_dec(v___x_2436_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 3, v_impl_2425_);
lean_ctor_set(v___x_1946_, 0, v___x_2437_);
v___x_2439_ = v___x_1946_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_impl_2425_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_r_1944_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
else
{
lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2504_; 
lean_inc(v_r_2432_);
lean_inc(v_v_2430_);
lean_inc(v_k_2429_);
lean_inc(v_size_2428_);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; lean_object* v_unused_2509_; 
v_unused_2505_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_r_1944_, 2);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_r_1944_, 1);
lean_dec(v_unused_2508_);
v_unused_2509_ = lean_ctor_get(v_r_1944_, 0);
lean_dec(v_unused_2509_);
v___x_2442_ = v_r_1944_;
v_isShared_2443_ = v_isSharedCheck_2504_;
goto v_resetjp_2441_;
}
else
{
lean_dec(v_r_1944_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2504_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v_size_2444_; lean_object* v_k_2445_; lean_object* v_v_2446_; lean_object* v_l_2447_; lean_object* v_r_2448_; lean_object* v_size_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; 
v_size_2444_ = lean_ctor_get(v_l_2431_, 0);
v_k_2445_ = lean_ctor_get(v_l_2431_, 1);
v_v_2446_ = lean_ctor_get(v_l_2431_, 2);
v_l_2447_ = lean_ctor_get(v_l_2431_, 3);
v_r_2448_ = lean_ctor_get(v_l_2431_, 4);
v_size_2449_ = lean_ctor_get(v_r_2432_, 0);
v___x_2450_ = lean_unsigned_to_nat(2u);
v___x_2451_ = lean_nat_mul(v___x_2450_, v_size_2449_);
v___x_2452_ = lean_nat_dec_lt(v_size_2444_, v___x_2451_);
lean_dec(v___x_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2480_; 
lean_inc(v_r_2448_);
lean_inc(v_l_2447_);
lean_inc(v_v_2446_);
lean_inc(v_k_2445_);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_l_2431_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; lean_object* v_unused_2482_; lean_object* v_unused_2483_; lean_object* v_unused_2484_; lean_object* v_unused_2485_; 
v_unused_2481_ = lean_ctor_get(v_l_2431_, 4);
lean_dec(v_unused_2481_);
v_unused_2482_ = lean_ctor_get(v_l_2431_, 3);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_l_2431_, 2);
lean_dec(v_unused_2483_);
v_unused_2484_ = lean_ctor_get(v_l_2431_, 1);
lean_dec(v_unused_2484_);
v_unused_2485_ = lean_ctor_get(v_l_2431_, 0);
lean_dec(v_unused_2485_);
v___x_2454_ = v_l_2431_;
v_isShared_2455_ = v_isSharedCheck_2480_;
goto v_resetjp_2453_;
}
else
{
lean_dec(v_l_2431_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2480_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2470_; 
v___x_2456_ = lean_nat_add(v___x_2426_, v_size_2427_);
lean_dec(v_size_2427_);
v___x_2457_ = lean_nat_add(v___x_2456_, v_size_2428_);
lean_dec(v_size_2428_);
if (lean_obj_tag(v_l_2447_) == 0)
{
lean_object* v_size_2478_; 
v_size_2478_ = lean_ctor_get(v_l_2447_, 0);
lean_inc(v_size_2478_);
v___y_2470_ = v_size_2478_;
goto v___jp_2469_;
}
else
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_unsigned_to_nat(0u);
v___y_2470_ = v___x_2479_;
goto v___jp_2469_;
}
v___jp_2458_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2462_ = lean_nat_add(v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 4, v_r_2432_);
lean_ctor_set(v___x_2454_, 3, v_r_2448_);
lean_ctor_set(v___x_2454_, 2, v_v_2430_);
lean_ctor_set(v___x_2454_, 1, v_k_2429_);
lean_ctor_set(v___x_2454_, 0, v___x_2462_);
v___x_2464_ = v___x_2454_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_k_2429_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_v_2430_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_r_2448_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_r_2432_);
v___x_2464_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2466_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 4, v___x_2464_);
lean_ctor_set(v___x_2442_, 3, v___y_2459_);
lean_ctor_set(v___x_2442_, 2, v_v_2446_);
lean_ctor_set(v___x_2442_, 1, v_k_2445_);
lean_ctor_set(v___x_2442_, 0, v___x_2457_);
v___x_2466_ = v___x_2442_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_k_2445_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_v_2446_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v___y_2459_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
v___jp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2471_ = lean_nat_add(v___x_2456_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec(v___x_2456_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_l_2447_);
lean_ctor_set(v___x_1946_, 3, v_impl_2425_);
lean_ctor_set(v___x_1946_, 0, v___x_2471_);
v___x_2473_ = v___x_1946_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_impl_2425_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_l_2447_);
v___x_2473_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_nat_add(v___x_2426_, v_size_2449_);
if (lean_obj_tag(v_r_2448_) == 0)
{
lean_object* v_size_2475_; 
v_size_2475_ = lean_ctor_get(v_r_2448_, 0);
lean_inc(v_size_2475_);
v___y_2459_ = v___x_2473_;
v___y_2460_ = v___x_2474_;
v___y_2461_ = v_size_2475_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_unsigned_to_nat(0u);
v___y_2459_ = v___x_2473_;
v___y_2460_ = v___x_2474_;
v___y_2461_ = v___x_2476_;
goto v___jp_2458_;
}
}
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
lean_del_object(v___x_1946_);
v___x_2486_ = lean_nat_add(v___x_2426_, v_size_2427_);
lean_dec(v_size_2427_);
v___x_2487_ = lean_nat_add(v___x_2486_, v_size_2428_);
lean_dec(v_size_2428_);
v___x_2488_ = lean_nat_add(v___x_2486_, v_size_2444_);
lean_dec(v___x_2486_);
lean_inc_ref(v_impl_2425_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 4, v_l_2431_);
lean_ctor_set(v___x_2442_, 3, v_impl_2425_);
lean_ctor_set(v___x_2442_, 2, v_v_1942_);
lean_ctor_set(v___x_2442_, 1, v_k_1941_);
lean_ctor_set(v___x_2442_, 0, v___x_2488_);
v___x_2490_ = v___x_2442_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2503_, 3, v_impl_2425_);
lean_ctor_set(v_reuseFailAlloc_2503_, 4, v_l_2431_);
v___x_2490_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
v_isSharedCheck_2497_ = !lean_is_exclusive(v_impl_2425_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; lean_object* v_unused_2499_; lean_object* v_unused_2500_; lean_object* v_unused_2501_; lean_object* v_unused_2502_; 
v_unused_2498_ = lean_ctor_get(v_impl_2425_, 4);
lean_dec(v_unused_2498_);
v_unused_2499_ = lean_ctor_get(v_impl_2425_, 3);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_impl_2425_, 2);
lean_dec(v_unused_2500_);
v_unused_2501_ = lean_ctor_get(v_impl_2425_, 1);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_impl_2425_, 0);
lean_dec(v_unused_2502_);
v___x_2492_ = v_impl_2425_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_dec(v_impl_2425_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 4, v_r_2432_);
lean_ctor_set(v___x_2492_, 3, v___x_2490_);
lean_ctor_set(v___x_2492_, 2, v_v_2430_);
lean_ctor_set(v___x_2492_, 1, v_k_2429_);
lean_ctor_set(v___x_2492_, 0, v___x_2487_);
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_k_2429_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_v_2430_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_r_2432_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2510_; lean_object* v___x_2511_; lean_object* v___x_2513_; 
v_size_2510_ = lean_ctor_get(v_impl_2425_, 0);
lean_inc(v_size_2510_);
v___x_2511_ = lean_nat_add(v___x_2426_, v_size_2510_);
lean_dec(v_size_2510_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 3, v_impl_2425_);
lean_ctor_set(v___x_1946_, 0, v___x_2511_);
v___x_2513_ = v___x_1946_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_impl_2425_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_r_1944_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
else
{
if (lean_obj_tag(v_r_1944_) == 0)
{
lean_object* v_l_2515_; 
v_l_2515_ = lean_ctor_get(v_r_1944_, 3);
lean_inc(v_l_2515_);
if (lean_obj_tag(v_l_2515_) == 0)
{
lean_object* v_r_2516_; 
v_r_2516_ = lean_ctor_get(v_r_1944_, 4);
lean_inc(v_r_2516_);
if (lean_obj_tag(v_r_2516_) == 0)
{
lean_object* v_size_2517_; lean_object* v_k_2518_; lean_object* v_v_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2532_; 
v_size_2517_ = lean_ctor_get(v_r_1944_, 0);
v_k_2518_ = lean_ctor_get(v_r_1944_, 1);
v_v_2519_ = lean_ctor_get(v_r_1944_, 2);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; 
v_unused_2533_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2534_);
v___x_2521_ = v_r_1944_;
v_isShared_2522_ = v_isSharedCheck_2532_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_v_2519_);
lean_inc(v_k_2518_);
lean_inc(v_size_2517_);
lean_dec(v_r_1944_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2532_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v_size_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v_size_2523_ = lean_ctor_get(v_l_2515_, 0);
v___x_2524_ = lean_nat_add(v___x_2426_, v_size_2517_);
lean_dec(v_size_2517_);
v___x_2525_ = lean_nat_add(v___x_2426_, v_size_2523_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 4, v_l_2515_);
lean_ctor_set(v___x_2521_, 3, v_impl_2425_);
lean_ctor_set(v___x_2521_, 2, v_v_1942_);
lean_ctor_set(v___x_2521_, 1, v_k_1941_);
lean_ctor_set(v___x_2521_, 0, v___x_2525_);
v___x_2527_ = v___x_2521_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_impl_2425_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_l_2515_);
v___x_2527_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2529_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_r_2516_);
lean_ctor_set(v___x_1946_, 3, v___x_2527_);
lean_ctor_set(v___x_1946_, 2, v_v_2519_);
lean_ctor_set(v___x_1946_, 1, v_k_2518_);
lean_ctor_set(v___x_1946_, 0, v___x_2524_);
v___x_2529_ = v___x_1946_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2524_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_k_2518_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_v_2519_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_r_2516_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v_k_2535_; lean_object* v_v_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2559_; 
v_k_2535_ = lean_ctor_get(v_r_1944_, 1);
v_v_2536_ = lean_ctor_get(v_r_1944_, 2);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; lean_object* v_unused_2561_; lean_object* v_unused_2562_; 
v_unused_2560_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_r_1944_, 0);
lean_dec(v_unused_2562_);
v___x_2538_ = v_r_1944_;
v_isShared_2539_ = v_isSharedCheck_2559_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_v_2536_);
lean_inc(v_k_2535_);
lean_dec(v_r_1944_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2559_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_k_2540_; lean_object* v_v_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2555_; 
v_k_2540_ = lean_ctor_get(v_l_2515_, 1);
v_v_2541_ = lean_ctor_get(v_l_2515_, 2);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_l_2515_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; lean_object* v_unused_2557_; lean_object* v_unused_2558_; 
v_unused_2556_ = lean_ctor_get(v_l_2515_, 4);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_l_2515_, 3);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_l_2515_, 0);
lean_dec(v_unused_2558_);
v___x_2543_ = v_l_2515_;
v_isShared_2544_ = v_isSharedCheck_2555_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_v_2541_);
lean_inc(v_k_2540_);
lean_dec(v_l_2515_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2555_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(3u);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 4, v_r_2516_);
lean_ctor_set(v___x_2543_, 3, v_r_2516_);
lean_ctor_set(v___x_2543_, 2, v_v_1942_);
lean_ctor_set(v___x_2543_, 1, v_k_1941_);
lean_ctor_set(v___x_2543_, 0, v___x_2426_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_r_2516_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_r_2516_);
v___x_2547_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2549_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 3, v_r_2516_);
lean_ctor_set(v___x_2538_, 0, v___x_2426_);
v___x_2549_ = v___x_2538_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_k_2535_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_v_2536_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_r_2516_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_r_2516_);
v___x_2549_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_2549_);
lean_ctor_set(v___x_1946_, 3, v___x_2547_);
lean_ctor_set(v___x_1946_, 2, v_v_2541_);
lean_ctor_set(v___x_1946_, 1, v_k_2540_);
lean_ctor_set(v___x_1946_, 0, v___x_2545_);
v___x_2551_ = v___x_1946_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_k_2540_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_v_2541_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2563_; 
v_r_2563_ = lean_ctor_get(v_r_1944_, 4);
lean_inc(v_r_2563_);
if (lean_obj_tag(v_r_2563_) == 0)
{
lean_object* v_k_2564_; lean_object* v_v_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2576_; 
v_k_2564_ = lean_ctor_get(v_r_1944_, 1);
v_v_2565_ = lean_ctor_get(v_r_1944_, 2);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2576_ == 0)
{
lean_object* v_unused_2577_; lean_object* v_unused_2578_; lean_object* v_unused_2579_; 
v_unused_2577_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2577_);
v_unused_2578_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2578_);
v_unused_2579_ = lean_ctor_get(v_r_1944_, 0);
lean_dec(v_unused_2579_);
v___x_2567_ = v_r_1944_;
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_v_2565_);
lean_inc(v_k_2564_);
lean_dec(v_r_1944_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_unsigned_to_nat(3u);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 4, v_l_2515_);
lean_ctor_set(v___x_2567_, 2, v_v_1942_);
lean_ctor_set(v___x_2567_, 1, v_k_1941_);
lean_ctor_set(v___x_2567_, 0, v___x_2426_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_l_2515_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_l_2515_);
v___x_2571_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2573_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v_r_2563_);
lean_ctor_set(v___x_1946_, 3, v___x_2571_);
lean_ctor_set(v___x_1946_, 2, v_v_2565_);
lean_ctor_set(v___x_1946_, 1, v_k_2564_);
lean_ctor_set(v___x_1946_, 0, v___x_2569_);
v___x_2573_ = v___x_1946_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2569_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_k_2564_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v_v_2565_);
lean_ctor_set(v_reuseFailAlloc_2574_, 3, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2574_, 4, v_r_2563_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_object* v_size_2580_; lean_object* v_k_2581_; lean_object* v_v_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2593_; 
v_size_2580_ = lean_ctor_get(v_r_1944_, 0);
v_k_2581_ = lean_ctor_get(v_r_1944_, 1);
v_v_2582_ = lean_ctor_get(v_r_1944_, 2);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_r_1944_);
if (v_isSharedCheck_2593_ == 0)
{
lean_object* v_unused_2594_; lean_object* v_unused_2595_; 
v_unused_2594_ = lean_ctor_get(v_r_1944_, 4);
lean_dec(v_unused_2594_);
v_unused_2595_ = lean_ctor_get(v_r_1944_, 3);
lean_dec(v_unused_2595_);
v___x_2584_ = v_r_1944_;
v_isShared_2585_ = v_isSharedCheck_2593_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_v_2582_);
lean_inc(v_k_2581_);
lean_inc(v_size_2580_);
lean_dec(v_r_1944_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2593_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 3, v_r_2563_);
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_size_2580_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_k_2581_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v_v_2582_);
lean_ctor_set(v_reuseFailAlloc_2592_, 3, v_r_2563_);
lean_ctor_set(v_reuseFailAlloc_2592_, 4, v_r_2563_);
v___x_2587_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2588_ = lean_unsigned_to_nat(2u);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_2587_);
lean_ctor_set(v___x_1946_, 3, v_r_2563_);
lean_ctor_set(v___x_1946_, 0, v___x_2588_);
v___x_2590_ = v___x_1946_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_r_2563_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v___x_2587_);
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
lean_object* v___x_2597_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 3, v_r_1944_);
lean_ctor_set(v___x_1946_, 0, v___x_2426_);
v___x_2597_ = v___x_1946_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_1941_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_1942_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_r_1944_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_r_1944_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
else
{
return v_t_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2601_, lean_object* v_t_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2601_, v_t_2602_);
lean_dec(v_k_2601_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object* v_id_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v_receivers_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_st_ref_get(v___y_2610_);
v_receivers_2613_ = lean_ctor_get(v___x_2612_, 7);
lean_inc(v_receivers_2613_);
v___x_2614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2613_, v_id_2609_);
lean_dec(v_receivers_2613_);
if (lean_obj_tag(v___x_2614_) == 1)
{
lean_object* v_val_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_val_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_val_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2612_);
lean_ctor_set(v___x_2616_, 1, v_val_2615_);
v___x_2617_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2616_, v___y_2610_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2647_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2647_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2647_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v_fst_2622_; lean_object* v_producers_2623_; lean_object* v_waiters_2624_; lean_object* v_capacity_2625_; lean_object* v_size_2626_; lean_object* v_buffer_2627_; lean_object* v_write_2628_; lean_object* v_read_2629_; lean_object* v_receivers_2630_; lean_object* v_nextId_2631_; uint8_t v_closed_2632_; lean_object* v_pos_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2646_; 
v_fst_2622_ = lean_ctor_get(v_a_2618_, 0);
lean_inc(v_fst_2622_);
lean_dec(v_a_2618_);
v_producers_2623_ = lean_ctor_get(v_fst_2622_, 0);
v_waiters_2624_ = lean_ctor_get(v_fst_2622_, 1);
v_capacity_2625_ = lean_ctor_get(v_fst_2622_, 2);
v_size_2626_ = lean_ctor_get(v_fst_2622_, 3);
v_buffer_2627_ = lean_ctor_get(v_fst_2622_, 4);
v_write_2628_ = lean_ctor_get(v_fst_2622_, 5);
v_read_2629_ = lean_ctor_get(v_fst_2622_, 6);
v_receivers_2630_ = lean_ctor_get(v_fst_2622_, 7);
v_nextId_2631_ = lean_ctor_get(v_fst_2622_, 8);
v_closed_2632_ = lean_ctor_get_uint8(v_fst_2622_, sizeof(void*)*10);
v_pos_2633_ = lean_ctor_get(v_fst_2622_, 9);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_fst_2622_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2635_ = v_fst_2622_;
v_isShared_2636_ = v_isSharedCheck_2646_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_pos_2633_);
lean_inc(v_nextId_2631_);
lean_inc(v_receivers_2630_);
lean_inc(v_read_2629_);
lean_inc(v_write_2628_);
lean_inc(v_buffer_2627_);
lean_inc(v_size_2626_);
lean_inc(v_capacity_2625_);
lean_inc(v_waiters_2624_);
lean_inc(v_producers_2623_);
lean_dec(v_fst_2622_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2646_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2639_; 
v___x_2637_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_id_2609_, v_receivers_2630_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 7, v___x_2637_);
v___x_2639_ = v___x_2635_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_producers_2623_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_waiters_2624_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v_capacity_2625_);
lean_ctor_set(v_reuseFailAlloc_2645_, 3, v_size_2626_);
lean_ctor_set(v_reuseFailAlloc_2645_, 4, v_buffer_2627_);
lean_ctor_set(v_reuseFailAlloc_2645_, 5, v_write_2628_);
lean_ctor_set(v_reuseFailAlloc_2645_, 6, v_read_2629_);
lean_ctor_set(v_reuseFailAlloc_2645_, 7, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2645_, 8, v_nextId_2631_);
lean_ctor_set(v_reuseFailAlloc_2645_, 9, v_pos_2633_);
lean_ctor_set_uint8(v_reuseFailAlloc_2645_, sizeof(void*)*10, v_closed_2632_);
v___x_2639_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2640_ = lean_st_ref_set(v___y_2610_, v___x_2639_);
v___x_2641_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0));
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2641_);
v___x_2643_ = v___x_2620_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
v_a_2648_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2617_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2617_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec(v___x_2614_);
lean_dec(v___x_2612_);
v___x_2656_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1));
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
return v___x_2657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object* v_id_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec(v_id_2658_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object* v_bd_2662_){
_start:
{
lean_object* v_state_2664_; lean_object* v_id_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; 
v_state_2664_ = lean_ctor_get(v_bd_2662_, 0);
lean_inc_ref(v_state_2664_);
v_id_2665_ = lean_ctor_get(v_bd_2662_, 1);
lean_inc(v_id_2665_);
lean_dec_ref(v_bd_2662_);
v___f_2666_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2666_, 0, v_id_2665_);
v___x_2667_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_2664_, v___f_2666_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2692_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2692_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2692_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___y_2673_; 
if (lean_obj_tag(v_a_2668_) == 0)
{
lean_object* v_a_2678_; uint8_t v___x_2679_; 
v_a_2678_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v_a_2668_, 1);
v___x_2679_ = lean_unbox(v_a_2678_);
lean_dec(v_a_2678_);
switch(v___x_2679_)
{
case 0:
{
lean_object* v___x_2680_; 
v___x_2680_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_2673_ = v___x_2680_;
goto v___jp_2672_;
}
case 1:
{
lean_object* v___x_2681_; 
v___x_2681_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_2673_ = v___x_2681_;
goto v___jp_2672_;
}
default: 
{
lean_object* v___x_2682_; 
v___x_2682_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_2673_ = v___x_2682_;
goto v___jp_2672_;
}
}
}
else
{
lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2690_; 
lean_del_object(v___x_2670_);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_a_2668_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; 
v_unused_2691_ = lean_ctor_get(v_a_2668_, 0);
lean_dec(v_unused_2691_);
v___x_2684_ = v_a_2668_;
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
else
{
lean_dec(v_a_2668_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2686_ = lean_box(0);
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2686_);
v___x_2688_ = v___x_2684_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
v___jp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_inc_ref(v___y_2673_);
v___x_2674_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___y_2673_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 1);
lean_ctor_set(v___x_2670_, 0, v___x_2674_);
v___x_2676_ = v___x_2670_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
v_a_2693_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2667_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2667_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object* v_bd_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2701_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object* v_00_u03b1_2704_, lean_object* v_bd_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_2708_, lean_object* v_bd_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(v_00_u03b1_2708_, v_bd_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object* v_00_u03b1_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2716_, lean_object* v_a_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(v_00_u03b1_2716_, v_a_2717_);
lean_dec(v_a_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object* v_00_u03b1_2720_, lean_object* v_place_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2721_, v_a_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2725_, lean_object* v_place_2726_, lean_object* v_a_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(v_00_u03b1_2725_, v_place_2726_, v_a_2727_);
lean_dec(v_a_2727_);
lean_dec(v_place_2726_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object* v_00_u03b1_2730_, lean_object* v_slot_2731_, lean_object* v_next_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2731_, v_next_2732_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2736_, lean_object* v_slot_2737_, lean_object* v_next_2738_, lean_object* v_a_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(v_00_u03b1_2736_, v_slot_2737_, v_next_2738_, v_a_2739_);
lean_dec(v_a_2739_);
lean_dec(v_next_2738_);
lean_dec(v_slot_2737_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object* v_00_u03b1_2742_, lean_object* v_next_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2743_, v_a_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object* v_00_u03b1_2747_, lean_object* v_next_2748_, lean_object* v_a_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(v_00_u03b1_2747_, v_next_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec(v_next_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object* v_00_u03b4_2752_, lean_object* v_t_2753_, lean_object* v_k_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2753_, v_k_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object* v_00_u03b4_2756_, lean_object* v_t_2757_, lean_object* v_k_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(v_00_u03b4_2756_, v_t_2757_, v_k_2758_);
lean_dec(v_k_2758_);
lean_dec(v_t_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2760_, lean_object* v_inst_2761_, lean_object* v_a_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_2762_, v___y_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2766_, lean_object* v_inst_2767_, lean_object* v_a_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2766_, v_inst_2767_, v_a_2768_, v___y_2769_);
lean_dec(v___y_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2772_, lean_object* v_k_2773_, lean_object* v_t_2774_, lean_object* v_h_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2773_, v_t_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2777_, lean_object* v_k_2778_, lean_object* v_t_2779_, lean_object* v_h_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2777_, v_k_2778_, v_t_2779_, v_h_2780_);
lean_dec(v_k_2778_);
return v_res_2781_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2782_, lean_object* v_y_2783_){
_start:
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_nat_dec_lt(v_x_2782_, v_y_2783_);
if (v___x_2784_ == 0)
{
uint8_t v___x_2785_; 
v___x_2785_ = lean_nat_dec_eq(v_x_2782_, v_y_2783_);
if (v___x_2785_ == 0)
{
uint8_t v___x_2786_; 
v___x_2786_ = 2;
return v___x_2786_;
}
else
{
uint8_t v___x_2787_; 
v___x_2787_ = 1;
return v___x_2787_;
}
}
else
{
uint8_t v___x_2788_; 
v___x_2788_ = 0;
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2789_, lean_object* v_y_2790_){
_start:
{
uint8_t v_res_2791_; lean_object* v_r_2792_; 
v_res_2791_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2789_, v_y_2790_);
lean_dec(v_y_2790_);
lean_dec(v_x_2789_);
v_r_2792_ = lean_box(v_res_2791_);
return v_r_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_nat_add(v_x_2793_, v___x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2796_);
lean_dec(v_x_2796_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2798_, lean_object* v_receiverId_2799_, lean_object* v___f_2800_, lean_object* v_receivers_2801_, lean_object* v_s_2802_){
_start:
{
lean_object* v_producers_2803_; lean_object* v_waiters_2804_; lean_object* v_capacity_2805_; lean_object* v_size_2806_; lean_object* v_buffer_2807_; lean_object* v_write_2808_; lean_object* v_read_2809_; lean_object* v_nextId_2810_; uint8_t v_closed_2811_; lean_object* v_pos_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2822_; 
v_producers_2803_ = lean_ctor_get(v_s_2802_, 0);
v_waiters_2804_ = lean_ctor_get(v_s_2802_, 1);
v_capacity_2805_ = lean_ctor_get(v_s_2802_, 2);
v_size_2806_ = lean_ctor_get(v_s_2802_, 3);
v_buffer_2807_ = lean_ctor_get(v_s_2802_, 4);
v_write_2808_ = lean_ctor_get(v_s_2802_, 5);
v_read_2809_ = lean_ctor_get(v_s_2802_, 6);
v_nextId_2810_ = lean_ctor_get(v_s_2802_, 8);
v_closed_2811_ = lean_ctor_get_uint8(v_s_2802_, sizeof(void*)*10);
v_pos_2812_ = lean_ctor_get(v_s_2802_, 9);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_s_2802_);
if (v_isSharedCheck_2822_ == 0)
{
lean_object* v_unused_2823_; 
v_unused_2823_ = lean_ctor_get(v_s_2802_, 7);
lean_dec(v_unused_2823_);
v___x_2814_ = v_s_2802_;
v_isShared_2815_ = v_isSharedCheck_2822_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_pos_2812_);
lean_inc(v_nextId_2810_);
lean_inc(v_read_2809_);
lean_inc(v_write_2808_);
lean_inc(v_buffer_2807_);
lean_inc(v_size_2806_);
lean_inc(v_capacity_2805_);
lean_inc(v_waiters_2804_);
lean_inc(v_producers_2803_);
lean_dec(v_s_2802_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2822_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2816_ = lean_box(0);
v___x_2817_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2798_, v_receiverId_2799_, v___f_2800_, v_receivers_2801_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 7, v___x_2817_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_producers_2803_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_waiters_2804_);
lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_capacity_2805_);
lean_ctor_set(v_reuseFailAlloc_2821_, 3, v_size_2806_);
lean_ctor_set(v_reuseFailAlloc_2821_, 4, v_buffer_2807_);
lean_ctor_set(v_reuseFailAlloc_2821_, 5, v_write_2808_);
lean_ctor_set(v_reuseFailAlloc_2821_, 6, v_read_2809_);
lean_ctor_set(v_reuseFailAlloc_2821_, 7, v___x_2817_);
lean_ctor_set(v_reuseFailAlloc_2821_, 8, v_nextId_2810_);
lean_ctor_set(v_reuseFailAlloc_2821_, 9, v_pos_2812_);
lean_ctor_set_uint8(v_reuseFailAlloc_2821_, sizeof(void*)*10, v_closed_2811_);
v___x_2819_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; 
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2816_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
return v___x_2820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v_toPure_2827_; lean_object* v___x_2828_; 
v_toPure_2827_ = lean_ctor_get(v_toApplicative_2824_, 1);
lean_inc(v_toPure_2827_);
lean_dec_ref(v_toApplicative_2824_);
v___x_2828_ = lean_apply_2(v_toPure_2827_, lean_box(0), v_a_2825_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2829_, lean_object* v_a_2830_, lean_object* v___f_2831_, lean_object* v_inst_2832_, lean_object* v_toBind_2833_, lean_object* v_a_2834_){
_start:
{
if (lean_obj_tag(v_a_2834_) == 1)
{
lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___f_2835_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2835_, 0, v_toApplicative_2829_);
lean_closure_set(v___f_2835_, 1, v_a_2834_);
lean_inc(v_a_2830_);
v___x_2836_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2836_, 0, lean_box(0));
lean_closure_set(v___x_2836_, 1, lean_box(0));
lean_closure_set(v___x_2836_, 2, lean_box(0));
lean_closure_set(v___x_2836_, 3, v_a_2830_);
lean_closure_set(v___x_2836_, 4, v___f_2831_);
v___x_2837_ = lean_apply_2(v_inst_2832_, lean_box(0), v___x_2836_);
v___x_2838_ = lean_apply_4(v_toBind_2833_, lean_box(0), lean_box(0), v___x_2837_, v___f_2835_);
return v___x_2838_;
}
else
{
lean_object* v_toPure_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_dec(v_a_2834_);
lean_dec(v_toBind_2833_);
lean_dec(v_inst_2832_);
lean_dec_ref(v___f_2831_);
v_toPure_2839_ = lean_ctor_get(v_toApplicative_2829_, 1);
lean_inc(v_toPure_2839_);
lean_dec_ref(v_toApplicative_2829_);
v___x_2840_ = lean_box(0);
v___x_2841_ = lean_apply_2(v_toPure_2839_, lean_box(0), v___x_2840_);
return v___x_2841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_2842_, lean_object* v_a_2843_, lean_object* v___f_2844_, lean_object* v_inst_2845_, lean_object* v_toBind_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(v_toApplicative_2842_, v_a_2843_, v___f_2844_, v_inst_2845_, v_toBind_2846_, v_a_2847_);
lean_dec(v_a_2843_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2849_, lean_object* v_receiverId_2850_, lean_object* v___f_2851_, lean_object* v___f_2852_, lean_object* v_toApplicative_2853_, lean_object* v_a_2854_, lean_object* v_inst_2855_, lean_object* v_toBind_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v_receivers_2860_; lean_object* v___x_2861_; 
v_receivers_2860_ = lean_ctor_get(v_a_2859_, 7);
lean_inc_n(v_receivers_2860_, 2);
lean_dec_ref(v_a_2859_);
lean_inc(v_receiverId_2850_);
v___x_2861_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2849_, v_receivers_2860_, v_receiverId_2850_);
if (lean_obj_tag(v___x_2861_) == 1)
{
lean_object* v_val_2862_; lean_object* v___f_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_val_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_val_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___f_2863_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2863_, 0, v___f_2851_);
lean_closure_set(v___f_2863_, 1, v_receiverId_2850_);
lean_closure_set(v___f_2863_, 2, v___f_2852_);
lean_closure_set(v___f_2863_, 3, v_receivers_2860_);
lean_inc(v_toBind_2856_);
lean_inc(v_inst_2855_);
lean_inc(v_a_2854_);
v___f_2864_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2864_, 0, v_toApplicative_2853_);
lean_closure_set(v___f_2864_, 1, v_a_2854_);
lean_closure_set(v___f_2864_, 2, v___f_2863_);
lean_closure_set(v___f_2864_, 3, v_inst_2855_);
lean_closure_set(v___f_2864_, 4, v_toBind_2856_);
v___x_2865_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2857_, v_inst_2855_, v_inst_2858_, v_val_2862_, v_a_2854_);
v___x_2866_ = lean_apply_4(v_toBind_2856_, lean_box(0), lean_box(0), v___x_2865_, v___f_2864_);
return v___x_2866_;
}
else
{
lean_object* v_toPure_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec(v___x_2861_);
lean_dec(v_receivers_2860_);
lean_dec(v_inst_2858_);
lean_dec_ref(v_inst_2857_);
lean_dec(v_toBind_2856_);
lean_dec(v_inst_2855_);
lean_dec_ref(v___f_2852_);
lean_dec_ref(v___f_2851_);
lean_dec(v_receiverId_2850_);
v_toPure_2867_ = lean_ctor_get(v_toApplicative_2853_, 1);
lean_inc(v_toPure_2867_);
lean_dec_ref(v_toApplicative_2853_);
v___x_2868_ = lean_box(0);
v___x_2869_ = lean_apply_2(v_toPure_2867_, lean_box(0), v___x_2868_);
return v___x_2869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object* v___f_2870_, lean_object* v_receiverId_2871_, lean_object* v___f_2872_, lean_object* v___f_2873_, lean_object* v_toApplicative_2874_, lean_object* v_a_2875_, lean_object* v_inst_2876_, lean_object* v_toBind_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(v___f_2870_, v_receiverId_2871_, v___f_2872_, v___f_2873_, v_toApplicative_2874_, v_a_2875_, v_inst_2876_, v_toBind_2877_, v_inst_2878_, v_inst_2879_, v_a_2880_);
lean_dec(v_a_2875_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_receiverId_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_toApplicative_2889_; lean_object* v_toBind_2890_; lean_object* v___f_2891_; lean_object* v___f_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_toApplicative_2889_ = lean_ctor_get(v_inst_2884_, 0);
lean_inc_ref(v_toApplicative_2889_);
v_toBind_2890_ = lean_ctor_get(v_inst_2884_, 1);
lean_inc_n(v_toBind_2890_, 2);
v___f_2891_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_2892_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_inst_2885_);
lean_inc_n(v_a_2888_, 2);
v___f_2893_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_2893_, 0, v___f_2891_);
lean_closure_set(v___f_2893_, 1, v_receiverId_2887_);
lean_closure_set(v___f_2893_, 2, v___f_2891_);
lean_closure_set(v___f_2893_, 3, v___f_2892_);
lean_closure_set(v___f_2893_, 4, v_toApplicative_2889_);
lean_closure_set(v___f_2893_, 5, v_a_2888_);
lean_closure_set(v___f_2893_, 6, v_inst_2885_);
lean_closure_set(v___f_2893_, 7, v_toBind_2890_);
lean_closure_set(v___f_2893_, 8, v_inst_2884_);
lean_closure_set(v___f_2893_, 9, v_inst_2886_);
v___x_2894_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2894_, 0, lean_box(0));
lean_closure_set(v___x_2894_, 1, lean_box(0));
lean_closure_set(v___x_2894_, 2, v_a_2888_);
v___x_2895_ = lean_apply_2(v_inst_2885_, lean_box(0), v___x_2894_);
v___x_2896_ = lean_apply_4(v_toBind_2890_, lean_box(0), lean_box(0), v___x_2895_, v___f_2893_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object* v_inst_2897_, lean_object* v_inst_2898_, lean_object* v_inst_2899_, lean_object* v_receiverId_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2897_, v_inst_2898_, v_inst_2899_, v_receiverId_2900_, v_a_2901_);
lean_dec(v_a_2901_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_2903_, lean_object* v_00_u03b1_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_receiverId_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2905_, v_inst_2906_, v_inst_2907_, v_receiverId_2908_, v_a_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object* v_m_2911_, lean_object* v_00_u03b1_2912_, lean_object* v_inst_2913_, lean_object* v_inst_2914_, lean_object* v_inst_2915_, lean_object* v_receiverId_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(v_m_2911_, v_00_u03b1_2912_, v_inst_2913_, v_inst_2914_, v_inst_2915_, v_receiverId_2916_, v_a_2917_);
lean_dec(v_a_2917_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_2919_, lean_object* v_t_2920_){
_start:
{
if (lean_obj_tag(v_t_2920_) == 0)
{
lean_object* v_size_2921_; lean_object* v_k_2922_; lean_object* v_v_2923_; lean_object* v_l_2924_; lean_object* v_r_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2944_; 
v_size_2921_ = lean_ctor_get(v_t_2920_, 0);
v_k_2922_ = lean_ctor_get(v_t_2920_, 1);
v_v_2923_ = lean_ctor_get(v_t_2920_, 2);
v_l_2924_ = lean_ctor_get(v_t_2920_, 3);
v_r_2925_ = lean_ctor_get(v_t_2920_, 4);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_t_2920_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2927_ = v_t_2920_;
v_isShared_2928_ = v_isSharedCheck_2944_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_r_2925_);
lean_inc(v_l_2924_);
lean_inc(v_v_2923_);
lean_inc(v_k_2922_);
lean_inc(v_size_2921_);
lean_dec(v_t_2920_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2944_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
uint8_t v___x_2929_; 
v___x_2929_ = lean_nat_dec_lt(v_k_2919_, v_k_2922_);
if (v___x_2929_ == 0)
{
uint8_t v___x_2930_; 
v___x_2930_ = lean_nat_dec_eq(v_k_2919_, v_k_2922_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2919_, v_r_2925_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 4, v___x_2931_);
v___x_2933_ = v___x_2927_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_size_2921_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_k_2922_);
lean_ctor_set(v_reuseFailAlloc_2934_, 2, v_v_2923_);
lean_ctor_set(v_reuseFailAlloc_2934_, 3, v_l_2924_);
lean_ctor_set(v_reuseFailAlloc_2934_, 4, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
lean_dec(v_k_2922_);
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = lean_nat_add(v_v_2923_, v___x_2935_);
lean_dec(v_v_2923_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 2, v___x_2936_);
lean_ctor_set(v___x_2927_, 1, v_k_2919_);
v___x_2938_ = v___x_2927_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_size_2921_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_k_2919_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v___x_2936_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_l_2924_);
lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_r_2925_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2919_, v_l_2924_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 3, v___x_2940_);
v___x_2942_ = v___x_2927_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_size_2921_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_k_2922_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_v_2923_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_r_2925_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_dec(v_k_2919_);
return v_t_2920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_2945_, lean_object* v_next_2946_){
_start:
{
lean_object* v___x_2948_; lean_object* v_fst_2950_; lean_object* v_snd_2951_; lean_object* v_value_2953_; lean_object* v_pos_2954_; lean_object* v_remaining_2955_; uint8_t v___x_2956_; uint8_t v___x_2957_; 
v___x_2948_ = lean_st_ref_take(v_slot_2945_);
v_value_2953_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_value_2953_);
v_pos_2954_ = lean_ctor_get(v___x_2948_, 1);
lean_inc(v_pos_2954_);
v_remaining_2955_ = lean_ctor_get(v___x_2948_, 2);
lean_inc(v_remaining_2955_);
v___x_2956_ = lean_nat_dec_eq(v_next_2946_, v_pos_2954_);
v___x_2957_ = lean_bool_not(v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2976_; 
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; lean_object* v_unused_2978_; lean_object* v_unused_2979_; 
v_unused_2977_ = lean_ctor_get(v___x_2948_, 2);
lean_dec(v_unused_2977_);
v_unused_2978_ = lean_ctor_get(v___x_2948_, 1);
lean_dec(v_unused_2978_);
v_unused_2979_ = lean_ctor_get(v___x_2948_, 0);
lean_dec(v_unused_2979_);
v___x_2959_ = v___x_2948_;
v_isShared_2960_ = v_isSharedCheck_2976_;
goto v_resetjp_2958_;
}
else
{
lean_dec(v___x_2948_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2976_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2961_ = lean_unsigned_to_nat(1u);
v___x_2962_ = lean_nat_dec_eq(v_remaining_2955_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2963_ = lean_box(v___x_2962_);
lean_inc(v_value_2953_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v_value_2953_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_nat_sub(v_remaining_2955_, v___x_2961_);
lean_dec(v_remaining_2955_);
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
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_value_2953_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_pos_2954_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
v_fst_2950_ = v___x_2964_;
v_snd_2951_ = v___x_2967_;
goto v___jp_2949_;
}
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_remaining_2955_);
v___x_2969_ = lean_box(v___x_2962_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_value_2953_);
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
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_pos_2954_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
v_fst_2950_ = v___x_2970_;
v_snd_2951_ = v___x_2974_;
goto v___jp_2949_;
}
}
}
}
else
{
lean_object* v___x_2980_; 
lean_dec(v_remaining_2955_);
lean_dec(v_pos_2954_);
lean_dec(v_value_2953_);
v___x_2980_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___closed__0));
v_fst_2950_ = v___x_2980_;
v_snd_2951_ = v___x_2948_;
goto v___jp_2949_;
}
v___jp_2949_:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_st_ref_set(v_slot_2945_, v_snd_2951_);
return v_fst_2950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_2981_, lean_object* v_next_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_2981_, v_next_2982_);
lean_dec(v_next_2982_);
lean_dec(v_slot_2981_);
return v_res_2984_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v_size_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2987_ = lean_st_ref_get(v_a_2985_);
v_size_2988_ = lean_ctor_get(v___x_2987_, 3);
lean_inc(v_size_2988_);
lean_dec(v___x_2987_);
v___x_2989_ = lean_unsigned_to_nat(0u);
v___x_2990_ = lean_nat_dec_eq(v_size_2988_, v___x_2989_);
lean_dec(v_size_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_2991_, lean_object* v___y_2992_){
_start:
{
uint8_t v_res_2993_; lean_object* v_r_2994_; 
v_res_2993_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_2991_);
lean_dec(v_a_2991_);
v_r_2994_ = lean_box(v_res_2993_);
return v_r_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v_capacity_2999_; lean_object* v_buffer_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2998_ = lean_st_ref_get(v_a_2996_);
v_capacity_2999_ = lean_ctor_get(v___x_2998_, 2);
lean_inc(v_capacity_2999_);
v_buffer_3000_ = lean_ctor_get(v___x_2998_, 4);
lean_inc_ref(v_buffer_3000_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_nat_mod(v_place_2995_, v_capacity_2999_);
lean_dec(v_capacity_2999_);
v___x_3002_ = lean_array_fget(v_buffer_3000_, v___x_3001_);
lean_dec(v___x_3001_);
lean_dec_ref(v_buffer_3000_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_3003_, lean_object* v_a_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3003_, v_a_3004_);
lean_dec(v_a_3004_);
lean_dec(v_place_3003_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = lean_st_ref_get(v_a_3008_);
v___x_3011_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3008_);
if (v___x_3011_ == 0)
{
lean_object* v_capacity_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v_fst_3016_; lean_object* v_snd_3017_; lean_object* v_st_3019_; lean_object* v___y_3020_; 
v_capacity_3012_ = lean_ctor_get(v___x_3010_, 2);
lean_inc(v_capacity_3012_);
v___x_3013_ = lean_nat_mod(v_next_3007_, v_capacity_3012_);
lean_dec(v_capacity_3012_);
v___x_3014_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_3013_, v_a_3008_);
lean_dec(v___x_3013_);
v___x_3015_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_3014_, v_next_3007_);
lean_dec(v___x_3014_);
v_fst_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_fst_3016_);
v_snd_3017_ = lean_ctor_get(v___x_3015_, 1);
lean_inc(v_snd_3017_);
lean_dec_ref(v___x_3015_);
if (lean_obj_tag(v_fst_3016_) == 1)
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_unbox(v_snd_3017_);
if (v___x_3022_ == 0)
{
lean_dec(v_snd_3017_);
v_st_3019_ = v___x_3010_;
v___y_3020_ = v_a_3008_;
goto v___jp_3018_;
}
else
{
lean_object* v___x_3023_; lean_object* v_producers_3024_; lean_object* v_waiters_3025_; lean_object* v_capacity_3026_; lean_object* v_size_3027_; lean_object* v_buffer_3028_; lean_object* v_write_3029_; lean_object* v_read_3030_; lean_object* v_receivers_3031_; lean_object* v_nextId_3032_; uint8_t v_closed_3033_; lean_object* v_pos_3034_; lean_object* v___x_3035_; 
v___x_3023_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_3010_);
v_producers_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc_ref(v_producers_3024_);
v_waiters_3025_ = lean_ctor_get(v___x_3023_, 1);
lean_inc_ref(v_waiters_3025_);
v_capacity_3026_ = lean_ctor_get(v___x_3023_, 2);
lean_inc(v_capacity_3026_);
v_size_3027_ = lean_ctor_get(v___x_3023_, 3);
lean_inc(v_size_3027_);
v_buffer_3028_ = lean_ctor_get(v___x_3023_, 4);
lean_inc_ref(v_buffer_3028_);
v_write_3029_ = lean_ctor_get(v___x_3023_, 5);
lean_inc(v_write_3029_);
v_read_3030_ = lean_ctor_get(v___x_3023_, 6);
lean_inc(v_read_3030_);
v_receivers_3031_ = lean_ctor_get(v___x_3023_, 7);
lean_inc(v_receivers_3031_);
v_nextId_3032_ = lean_ctor_get(v___x_3023_, 8);
lean_inc(v_nextId_3032_);
v_closed_3033_ = lean_ctor_get_uint8(v___x_3023_, sizeof(void*)*10);
v_pos_3034_ = lean_ctor_get(v___x_3023_, 9);
lean_inc(v_pos_3034_);
v___x_3035_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3024_);
if (lean_obj_tag(v___x_3035_) == 1)
{
lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3046_; 
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; lean_object* v_unused_3048_; lean_object* v_unused_3049_; lean_object* v_unused_3050_; lean_object* v_unused_3051_; lean_object* v_unused_3052_; lean_object* v_unused_3053_; lean_object* v_unused_3054_; lean_object* v_unused_3055_; lean_object* v_unused_3056_; 
v_unused_3047_ = lean_ctor_get(v___x_3023_, 9);
lean_dec(v_unused_3047_);
v_unused_3048_ = lean_ctor_get(v___x_3023_, 8);
lean_dec(v_unused_3048_);
v_unused_3049_ = lean_ctor_get(v___x_3023_, 7);
lean_dec(v_unused_3049_);
v_unused_3050_ = lean_ctor_get(v___x_3023_, 6);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v___x_3023_, 5);
lean_dec(v_unused_3051_);
v_unused_3052_ = lean_ctor_get(v___x_3023_, 4);
lean_dec(v_unused_3052_);
v_unused_3053_ = lean_ctor_get(v___x_3023_, 3);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v___x_3023_, 2);
lean_dec(v_unused_3054_);
v_unused_3055_ = lean_ctor_get(v___x_3023_, 1);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v___x_3023_, 0);
lean_dec(v_unused_3056_);
v___x_3037_ = v___x_3023_;
v_isShared_3038_ = v_isSharedCheck_3046_;
goto v_resetjp_3036_;
}
else
{
lean_dec(v___x_3023_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3046_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v_val_3039_; lean_object* v_fst_3040_; lean_object* v_snd_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
v_val_3039_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_val_3039_);
lean_dec_ref_known(v___x_3035_, 1);
v_fst_3040_ = lean_ctor_get(v_val_3039_, 0);
lean_inc(v_fst_3040_);
v_snd_3041_ = lean_ctor_get(v_val_3039_, 1);
lean_inc(v_snd_3041_);
lean_dec(v_val_3039_);
v___x_3042_ = lean_io_promise_resolve(v_snd_3017_, v_fst_3040_);
lean_dec(v_fst_3040_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v_snd_3041_);
v___x_3044_ = v___x_3037_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_snd_3041_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_waiters_3025_);
lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_capacity_3026_);
lean_ctor_set(v_reuseFailAlloc_3045_, 3, v_size_3027_);
lean_ctor_set(v_reuseFailAlloc_3045_, 4, v_buffer_3028_);
lean_ctor_set(v_reuseFailAlloc_3045_, 5, v_write_3029_);
lean_ctor_set(v_reuseFailAlloc_3045_, 6, v_read_3030_);
lean_ctor_set(v_reuseFailAlloc_3045_, 7, v_receivers_3031_);
lean_ctor_set(v_reuseFailAlloc_3045_, 8, v_nextId_3032_);
lean_ctor_set(v_reuseFailAlloc_3045_, 9, v_pos_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3045_, sizeof(void*)*10, v_closed_3033_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
v_st_3019_ = v___x_3044_;
v___y_3020_ = v_a_3008_;
goto v___jp_3018_;
}
}
}
else
{
lean_dec(v___x_3035_);
lean_dec(v_pos_3034_);
lean_dec(v_nextId_3032_);
lean_dec(v_receivers_3031_);
lean_dec(v_read_3030_);
lean_dec(v_write_3029_);
lean_dec_ref(v_buffer_3028_);
lean_dec(v_size_3027_);
lean_dec(v_capacity_3026_);
lean_dec_ref(v_waiters_3025_);
lean_dec(v_snd_3017_);
v_st_3019_ = v___x_3023_;
v___y_3020_ = v_a_3008_;
goto v___jp_3018_;
}
}
}
else
{
lean_object* v___x_3057_; 
lean_dec(v_snd_3017_);
lean_dec(v_fst_3016_);
lean_dec(v___x_3010_);
v___x_3057_ = lean_box(0);
return v___x_3057_;
}
v___jp_3018_:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_st_ref_set(v___y_3020_, v_st_3019_);
return v_fst_3016_;
}
}
else
{
lean_object* v___x_3058_; 
lean_dec(v___x_3010_);
v___x_3058_ = lean_box(0);
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_3059_, lean_object* v_a_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3059_, v_a_3060_);
lean_dec(v_a_3060_);
lean_dec(v_next_3059_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v___x_3066_; lean_object* v_receivers_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_st_ref_get(v_a_3064_);
v_receivers_3067_ = lean_ctor_get(v___x_3066_, 7);
lean_inc(v_receivers_3067_);
lean_dec(v___x_3066_);
v___x_3068_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3067_, v_receiverId_3063_);
if (lean_obj_tag(v___x_3068_) == 1)
{
lean_object* v_val_3069_; lean_object* v___x_3070_; 
v_val_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_val_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v___x_3070_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_3069_, v_a_3064_);
lean_dec(v_val_3069_);
if (lean_obj_tag(v___x_3070_) == 1)
{
lean_object* v___x_3071_; lean_object* v_producers_3072_; lean_object* v_waiters_3073_; lean_object* v_capacity_3074_; lean_object* v_size_3075_; lean_object* v_buffer_3076_; lean_object* v_write_3077_; lean_object* v_read_3078_; lean_object* v_nextId_3079_; uint8_t v_closed_3080_; lean_object* v_pos_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3090_; 
v___x_3071_ = lean_st_ref_take(v_a_3064_);
v_producers_3072_ = lean_ctor_get(v___x_3071_, 0);
v_waiters_3073_ = lean_ctor_get(v___x_3071_, 1);
v_capacity_3074_ = lean_ctor_get(v___x_3071_, 2);
v_size_3075_ = lean_ctor_get(v___x_3071_, 3);
v_buffer_3076_ = lean_ctor_get(v___x_3071_, 4);
v_write_3077_ = lean_ctor_get(v___x_3071_, 5);
v_read_3078_ = lean_ctor_get(v___x_3071_, 6);
v_nextId_3079_ = lean_ctor_get(v___x_3071_, 8);
v_closed_3080_ = lean_ctor_get_uint8(v___x_3071_, sizeof(void*)*10);
v_pos_3081_ = lean_ctor_get(v___x_3071_, 9);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3071_, 7);
lean_dec(v_unused_3091_);
v___x_3083_ = v___x_3071_;
v_isShared_3084_ = v_isSharedCheck_3090_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_pos_3081_);
lean_inc(v_nextId_3079_);
lean_inc(v_read_3078_);
lean_inc(v_write_3077_);
lean_inc(v_buffer_3076_);
lean_inc(v_size_3075_);
lean_inc(v_capacity_3074_);
lean_inc(v_waiters_3073_);
lean_inc(v_producers_3072_);
lean_dec(v___x_3071_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3090_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3063_, v_receivers_3067_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 7, v___x_3085_);
v___x_3087_ = v___x_3083_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_producers_3072_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_waiters_3073_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_capacity_3074_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_size_3075_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_buffer_3076_);
lean_ctor_set(v_reuseFailAlloc_3089_, 5, v_write_3077_);
lean_ctor_set(v_reuseFailAlloc_3089_, 6, v_read_3078_);
lean_ctor_set(v_reuseFailAlloc_3089_, 7, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3089_, 8, v_nextId_3079_);
lean_ctor_set(v_reuseFailAlloc_3089_, 9, v_pos_3081_);
lean_ctor_set_uint8(v_reuseFailAlloc_3089_, sizeof(void*)*10, v_closed_3080_);
v___x_3087_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; 
v___x_3088_ = lean_st_ref_set(v_a_3064_, v___x_3087_);
return v___x_3070_;
}
}
}
else
{
lean_object* v___x_3092_; 
lean_dec(v___x_3070_);
lean_dec(v_receivers_3067_);
lean_dec(v_receiverId_3063_);
v___x_3092_ = lean_box(0);
return v___x_3092_;
}
}
else
{
lean_object* v___x_3093_; 
lean_dec(v___x_3068_);
lean_dec(v_receivers_3067_);
lean_dec(v_receiverId_3063_);
v___x_3093_ = lean_box(0);
return v___x_3093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3094_, lean_object* v_a_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3094_, v_a_3095_);
lean_dec(v_a_3095_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3098_, v___y_3099_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3102_, v___y_3103_);
lean_dec(v___y_3103_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3106_){
_start:
{
lean_object* v_state_3108_; lean_object* v_id_3109_; lean_object* v___f_3110_; lean_object* v___x_3111_; 
v_state_3108_ = lean_ctor_get(v_ch_3106_, 0);
lean_inc_ref(v_state_3108_);
v_id_3109_ = lean_ctor_get(v_ch_3106_, 1);
lean_inc(v_id_3109_);
lean_dec_ref(v_ch_3106_);
v___f_3110_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3110_, 0, v_id_3109_);
v___x_3111_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3108_, v___f_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3112_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3115_, lean_object* v_ch_3116_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3116_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3119_, lean_object* v_ch_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3119_, v_ch_3120_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3123_, lean_object* v_receiverId_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3124_, v_a_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3128_, lean_object* v_receiverId_3129_, lean_object* v_a_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3128_, v_receiverId_3129_, v_a_3130_);
lean_dec(v_a_3130_);
return v_res_3132_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3133_, lean_object* v_a_3134_){
_start:
{
uint8_t v___x_3136_; 
v___x_3136_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3134_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3137_, lean_object* v_a_3138_, lean_object* v___y_3139_){
_start:
{
uint8_t v_res_3140_; lean_object* v_r_3141_; 
v_res_3140_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3137_, v_a_3138_);
lean_dec(v_a_3138_);
v_r_3141_ = lean_box(v_res_3140_);
return v_r_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3142_, lean_object* v_place_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3143_, v_a_3144_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3147_, lean_object* v_place_3148_, lean_object* v_a_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3147_, v_place_3148_, v_a_3149_);
lean_dec(v_a_3149_);
lean_dec(v_place_3148_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3152_, lean_object* v_slot_3153_, lean_object* v_next_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3153_, v_next_3154_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3158_, lean_object* v_slot_3159_, lean_object* v_next_3160_, lean_object* v_a_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3158_, v_slot_3159_, v_next_3160_, v_a_3161_);
lean_dec(v_a_3161_);
lean_dec(v_next_3160_);
lean_dec(v_slot_3159_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3164_, lean_object* v_next_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3165_, v_a_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3169_, lean_object* v_next_3170_, lean_object* v_a_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3169_, v_next_3170_, v_a_3171_);
lean_dec(v_a_3171_);
lean_dec(v_next_3170_);
return v_res_3173_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3174_, lean_object* v_t_3175_){
_start:
{
if (lean_obj_tag(v_t_3175_) == 0)
{
lean_object* v_k_3176_; lean_object* v_l_3177_; lean_object* v_r_3178_; uint8_t v___x_3179_; 
v_k_3176_ = lean_ctor_get(v_t_3175_, 1);
v_l_3177_ = lean_ctor_get(v_t_3175_, 3);
v_r_3178_ = lean_ctor_get(v_t_3175_, 4);
v___x_3179_ = lean_nat_dec_lt(v_k_3174_, v_k_3176_);
if (v___x_3179_ == 0)
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_nat_dec_eq(v_k_3174_, v_k_3176_);
if (v___x_3180_ == 0)
{
v_t_3175_ = v_r_3178_;
goto _start;
}
else
{
return v___x_3180_;
}
}
else
{
v_t_3175_ = v_l_3177_;
goto _start;
}
}
else
{
uint8_t v___x_3183_; 
v___x_3183_ = 0;
return v___x_3183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3184_, lean_object* v_t_3185_){
_start:
{
uint8_t v_res_3186_; lean_object* v_r_3187_; 
v_res_3186_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3184_, v_t_3185_);
lean_dec(v_t_3185_);
lean_dec(v_k_3184_);
v_r_3187_ = lean_box(v_res_3186_);
return v_r_3187_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_box(0);
v___x_3189_ = lean_task_pure(v___x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3190_, lean_object* v___f_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; lean_object* v_receivers_3195_; uint8_t v___x_3196_; 
v___x_3194_ = lean_st_ref_get(v___y_3192_);
v_receivers_3195_ = lean_ctor_get(v___x_3194_, 7);
lean_inc(v_receivers_3195_);
lean_dec(v___x_3194_);
v___x_3196_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3190_, v_receivers_3195_);
lean_dec(v_receivers_3195_);
if (v___x_3196_ == 0)
{
lean_object* v___x_3197_; 
lean_dec_ref(v___f_3191_);
lean_dec(v_id_3190_);
v___x_3197_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3197_;
}
else
{
lean_object* v___x_3198_; 
v___x_3198_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3190_, v___y_3192_);
if (lean_obj_tag(v___x_3198_) == 1)
{
lean_object* v___x_3199_; 
lean_dec_ref(v___f_3191_);
v___x_3199_ = lean_task_pure(v___x_3198_);
return v___x_3199_;
}
else
{
lean_object* v___x_3200_; uint8_t v_closed_3201_; 
lean_dec(v___x_3198_);
v___x_3200_ = lean_st_ref_get(v___y_3192_);
v_closed_3201_ = lean_ctor_get_uint8(v___x_3200_, sizeof(void*)*10);
lean_dec(v___x_3200_);
if (v_closed_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v_producers_3204_; lean_object* v_waiters_3205_; lean_object* v_capacity_3206_; lean_object* v_size_3207_; lean_object* v_buffer_3208_; lean_object* v_write_3209_; lean_object* v_read_3210_; lean_object* v_receivers_3211_; lean_object* v_nextId_3212_; uint8_t v_closed_3213_; lean_object* v_pos_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3228_; 
v___x_3202_ = lean_io_promise_new();
v___x_3203_ = lean_st_ref_take(v___y_3192_);
v_producers_3204_ = lean_ctor_get(v___x_3203_, 0);
v_waiters_3205_ = lean_ctor_get(v___x_3203_, 1);
v_capacity_3206_ = lean_ctor_get(v___x_3203_, 2);
v_size_3207_ = lean_ctor_get(v___x_3203_, 3);
v_buffer_3208_ = lean_ctor_get(v___x_3203_, 4);
v_write_3209_ = lean_ctor_get(v___x_3203_, 5);
v_read_3210_ = lean_ctor_get(v___x_3203_, 6);
v_receivers_3211_ = lean_ctor_get(v___x_3203_, 7);
v_nextId_3212_ = lean_ctor_get(v___x_3203_, 8);
v_closed_3213_ = lean_ctor_get_uint8(v___x_3203_, sizeof(void*)*10);
v_pos_3214_ = lean_ctor_get(v___x_3203_, 9);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3216_ = v___x_3203_;
v_isShared_3217_ = v_isSharedCheck_3228_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_pos_3214_);
lean_inc(v_nextId_3212_);
lean_inc(v_receivers_3211_);
lean_inc(v_read_3210_);
lean_inc(v_write_3209_);
lean_inc(v_buffer_3208_);
lean_inc(v_size_3207_);
lean_inc(v_capacity_3206_);
lean_inc(v_waiters_3205_);
lean_inc(v_producers_3204_);
lean_dec(v___x_3203_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3228_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3218_ = lean_box(0);
lean_inc(v___x_3202_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3202_);
lean_ctor_set(v___x_3219_, 1, v___x_3218_);
v___x_3220_ = l_Std_Queue_enqueue___redArg(v___x_3219_, v_waiters_3205_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v___x_3220_);
v___x_3222_ = v___x_3216_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_producers_3204_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_capacity_3206_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_size_3207_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v_buffer_3208_);
lean_ctor_set(v_reuseFailAlloc_3227_, 5, v_write_3209_);
lean_ctor_set(v_reuseFailAlloc_3227_, 6, v_read_3210_);
lean_ctor_set(v_reuseFailAlloc_3227_, 7, v_receivers_3211_);
lean_ctor_set(v_reuseFailAlloc_3227_, 8, v_nextId_3212_);
lean_ctor_set(v_reuseFailAlloc_3227_, 9, v_pos_3214_);
lean_ctor_set_uint8(v_reuseFailAlloc_3227_, sizeof(void*)*10, v_closed_3213_);
v___x_3222_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3223_ = lean_st_ref_set(v___y_3192_, v___x_3222_);
v___x_3224_ = lean_io_promise_result_opt(v___x_3202_);
lean_dec(v___x_3202_);
v___x_3225_ = lean_unsigned_to_nat(0u);
v___x_3226_ = lean_io_bind_task(v___x_3224_, v___f_3191_, v___x_3225_, v_closed_3201_);
return v___x_3226_;
}
}
}
else
{
lean_object* v___x_3229_; 
lean_dec_ref(v___f_3191_);
v___x_3229_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3230_, lean_object* v___f_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3230_, v___f_3231_, v___y_3232_);
lean_dec(v___y_3232_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3235_, lean_object* v_res_3236_){
_start:
{
if (lean_obj_tag(v_res_3236_) == 0)
{
lean_dec_ref(v_ch_3235_);
goto v___jp_3238_;
}
else
{
lean_object* v_val_3240_; uint8_t v___x_3241_; 
v_val_3240_ = lean_ctor_get(v_res_3236_, 0);
v___x_3241_ = lean_unbox(v_val_3240_);
if (v___x_3241_ == 0)
{
lean_dec_ref(v_ch_3235_);
goto v___jp_3238_;
}
else
{
lean_object* v___x_3242_; 
v___x_3242_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3235_);
return v___x_3242_;
}
}
v___jp_3238_:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3243_, lean_object* v_res_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3243_, v_res_3244_);
lean_dec(v_res_3244_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3247_){
_start:
{
lean_object* v_state_3249_; lean_object* v_id_3250_; lean_object* v___f_3251_; lean_object* v___f_3252_; lean_object* v___x_3253_; 
v_state_3249_ = lean_ctor_get(v_ch_3247_, 0);
lean_inc_ref(v_state_3249_);
v_id_3250_ = lean_ctor_get(v_ch_3247_, 1);
lean_inc(v_id_3250_);
v___f_3251_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3251_, 0, v_ch_3247_);
v___f_3252_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3252_, 0, v_id_3250_);
lean_closure_set(v___f_3252_, 1, v___f_3251_);
v___x_3253_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3249_, v___f_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3254_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3257_, lean_object* v_ch_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3261_, lean_object* v_ch_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3261_, v_ch_3262_);
return v_res_3264_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3265_, lean_object* v_k_3266_, lean_object* v_t_3267_){
_start:
{
uint8_t v___x_3268_; 
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3266_, v_t_3267_);
return v___x_3268_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3269_, lean_object* v_k_3270_, lean_object* v_t_3271_){
_start:
{
uint8_t v_res_3272_; lean_object* v_r_3273_; 
v_res_3272_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3269_, v_k_3270_, v_t_3271_);
lean_dec(v_t_3271_);
lean_dec(v_k_3270_);
v_r_3273_ = lean_box(v_res_3272_);
return v_r_3273_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_task_pure(v___x_3274_);
return v___x_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3276_, lean_object* v_ch_3277_, lean_object* v_prio_3278_, lean_object* v_x_3279_){
_start:
{
if (lean_obj_tag(v_x_3279_) == 0)
{
lean_object* v___x_3281_; 
lean_dec(v_prio_3278_);
lean_dec_ref(v_ch_3277_);
lean_dec_ref(v_f_3276_);
v___x_3281_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3281_;
}
else
{
lean_object* v_val_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v_val_3282_ = lean_ctor_get(v_x_3279_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v_x_3279_, 1);
lean_inc_ref(v_f_3276_);
v___x_3283_ = lean_apply_2(v_f_3276_, v_val_3282_, lean_box(0));
v___x_3284_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3276_, v_ch_3277_, v_prio_3278_);
return v___x_3284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3285_, lean_object* v_ch_3286_, lean_object* v_prio_3287_, lean_object* v_x_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3285_, v_ch_3286_, v_prio_3287_, v_x_3288_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3291_, lean_object* v_ch_3292_, lean_object* v_prio_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v___f_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; 
lean_inc_ref(v_ch_3292_);
v___x_3295_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3292_);
lean_inc(v_prio_3293_);
v___f_3296_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3296_, 0, v_f_3291_);
lean_closure_set(v___f_3296_, 1, v_ch_3292_);
lean_closure_set(v___f_3296_, 2, v_prio_3293_);
v___x_3297_ = 0;
v___x_3298_ = lean_io_bind_task(v___x_3295_, v___f_3296_, v_prio_3293_, v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3299_, lean_object* v_ch_3300_, lean_object* v_prio_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3299_, v_ch_3300_, v_prio_3301_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3304_, lean_object* v_f_3305_, lean_object* v_ch_3306_, lean_object* v_prio_3307_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3305_, v_ch_3306_, v_prio_3307_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3310_, lean_object* v_f_3311_, lean_object* v_ch_3312_, lean_object* v_prio_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3310_, v_f_3311_, v_ch_3312_, v_prio_3313_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3316_, lean_object* v_val_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_pos_3319_; lean_object* v_toPure_3320_; uint8_t v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_pos_3319_ = lean_ctor_get(v_a_3318_, 1);
v_toPure_3320_ = lean_ctor_get(v_toApplicative_3316_, 1);
lean_inc(v_toPure_3320_);
lean_dec_ref(v_toApplicative_3316_);
v___x_3321_ = lean_nat_dec_eq(v_pos_3319_, v_val_3317_);
v___x_3322_ = lean_box(v___x_3321_);
v___x_3323_ = lean_apply_2(v_toPure_3320_, lean_box(0), v___x_3322_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3324_, lean_object* v_val_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3324_, v_val_3325_, v_a_3326_);
lean_dec_ref(v_a_3326_);
lean_dec(v_val_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3328_, lean_object* v_toBind_3329_, lean_object* v___f_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3332_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3332_, 0, lean_box(0));
lean_closure_set(v___x_3332_, 1, lean_box(0));
lean_closure_set(v___x_3332_, 2, v_a_3331_);
v___x_3333_ = lean_apply_2(v_inst_3328_, lean_box(0), v___x_3332_);
v___x_3334_ = lean_apply_4(v_toBind_3329_, lean_box(0), lean_box(0), v___x_3333_, v___f_3330_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3335_, lean_object* v_receiverId_3336_, lean_object* v_toApplicative_3337_, lean_object* v_inst_3338_, lean_object* v_toBind_3339_, lean_object* v_inst_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
uint8_t v_closed_3343_; 
v_closed_3343_ = lean_ctor_get_uint8(v_a_3342_, sizeof(void*)*10);
if (v_closed_3343_ == 0)
{
lean_object* v_capacity_3344_; lean_object* v_size_3345_; lean_object* v_receivers_3346_; lean_object* v___x_3347_; 
v_capacity_3344_ = lean_ctor_get(v_a_3342_, 2);
lean_inc(v_capacity_3344_);
v_size_3345_ = lean_ctor_get(v_a_3342_, 3);
lean_inc(v_size_3345_);
v_receivers_3346_ = lean_ctor_get(v_a_3342_, 7);
lean_inc(v_receivers_3346_);
lean_dec_ref(v_a_3342_);
v___x_3347_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3335_, v_receivers_3346_, v_receiverId_3336_);
if (lean_obj_tag(v___x_3347_) == 1)
{
lean_object* v_val_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; 
v_val_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_val_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v___x_3349_ = lean_unsigned_to_nat(0u);
v___x_3350_ = lean_nat_dec_eq(v_size_3345_, v___x_3349_);
lean_dec(v_size_3345_);
if (v___x_3350_ == 0)
{
lean_object* v___f_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_inc(v_val_3348_);
v___f_3351_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3351_, 0, v_toApplicative_3337_);
lean_closure_set(v___f_3351_, 1, v_val_3348_);
lean_inc(v_toBind_3339_);
lean_inc(v_inst_3338_);
v___f_3352_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3352_, 0, v_inst_3338_);
lean_closure_set(v___f_3352_, 1, v_toBind_3339_);
lean_closure_set(v___f_3352_, 2, v___f_3351_);
v___x_3353_ = lean_nat_mod(v_val_3348_, v_capacity_3344_);
lean_dec(v_capacity_3344_);
lean_dec(v_val_3348_);
v___x_3354_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3340_, v_inst_3338_, v___x_3353_, v_a_3341_);
v___x_3355_ = lean_apply_4(v_toBind_3339_, lean_box(0), lean_box(0), v___x_3354_, v___f_3352_);
return v___x_3355_;
}
else
{
lean_object* v_toPure_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec(v_val_3348_);
lean_dec(v_capacity_3344_);
lean_dec_ref(v_inst_3340_);
lean_dec(v_toBind_3339_);
lean_dec(v_inst_3338_);
v_toPure_3356_ = lean_ctor_get(v_toApplicative_3337_, 1);
lean_inc(v_toPure_3356_);
lean_dec_ref(v_toApplicative_3337_);
v___x_3357_ = lean_box(v_closed_3343_);
v___x_3358_ = lean_apply_2(v_toPure_3356_, lean_box(0), v___x_3357_);
return v___x_3358_;
}
}
else
{
lean_object* v_toPure_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec(v___x_3347_);
lean_dec(v_size_3345_);
lean_dec(v_capacity_3344_);
lean_dec_ref(v_inst_3340_);
lean_dec(v_toBind_3339_);
lean_dec(v_inst_3338_);
v_toPure_3359_ = lean_ctor_get(v_toApplicative_3337_, 1);
lean_inc(v_toPure_3359_);
lean_dec_ref(v_toApplicative_3337_);
v___x_3360_ = lean_box(v_closed_3343_);
v___x_3361_ = lean_apply_2(v_toPure_3359_, lean_box(0), v___x_3360_);
return v___x_3361_;
}
}
else
{
lean_object* v_toPure_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec_ref(v_a_3342_);
lean_dec_ref(v_inst_3340_);
lean_dec(v_toBind_3339_);
lean_dec(v_inst_3338_);
lean_dec(v_receiverId_3336_);
lean_dec_ref(v___f_3335_);
v_toPure_3362_ = lean_ctor_get(v_toApplicative_3337_, 1);
lean_inc(v_toPure_3362_);
lean_dec_ref(v_toApplicative_3337_);
v___x_3363_ = lean_box(v_closed_3343_);
v___x_3364_ = lean_apply_2(v_toPure_3362_, lean_box(0), v___x_3363_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object* v___f_3365_, lean_object* v_receiverId_3366_, lean_object* v_toApplicative_3367_, lean_object* v_inst_3368_, lean_object* v_toBind_3369_, lean_object* v_inst_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(v___f_3365_, v_receiverId_3366_, v_toApplicative_3367_, v_inst_3368_, v_toBind_3369_, v_inst_3370_, v_a_3371_, v_a_3372_);
lean_dec(v_a_3371_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3374_, lean_object* v_inst_3375_, lean_object* v_receiverId_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v_toApplicative_3378_; lean_object* v_toBind_3379_; lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_toApplicative_3378_ = lean_ctor_get(v_inst_3374_, 0);
lean_inc_ref(v_toApplicative_3378_);
v_toBind_3379_ = lean_ctor_get(v_inst_3374_, 1);
lean_inc_n(v_toBind_3379_, 2);
v___f_3380_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3377_, 2);
lean_inc(v_inst_3375_);
v___f_3381_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3381_, 0, v___f_3380_);
lean_closure_set(v___f_3381_, 1, v_receiverId_3376_);
lean_closure_set(v___f_3381_, 2, v_toApplicative_3378_);
lean_closure_set(v___f_3381_, 3, v_inst_3375_);
lean_closure_set(v___f_3381_, 4, v_toBind_3379_);
lean_closure_set(v___f_3381_, 5, v_inst_3374_);
lean_closure_set(v___f_3381_, 6, v_a_3377_);
v___x_3382_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3382_, 0, lean_box(0));
lean_closure_set(v___x_3382_, 1, lean_box(0));
lean_closure_set(v___x_3382_, 2, v_a_3377_);
v___x_3383_ = lean_apply_2(v_inst_3375_, lean_box(0), v___x_3382_);
v___x_3384_ = lean_apply_4(v_toBind_3379_, lean_box(0), lean_box(0), v___x_3383_, v___f_3381_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_receiverId_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(v_inst_3385_, v_inst_3386_, v_receiverId_3387_, v_a_3388_);
lean_dec(v_a_3388_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3390_, lean_object* v_00_u03b1_3391_, lean_object* v_inst_3392_, lean_object* v_inst_3393_, lean_object* v_inst_3394_, lean_object* v_inst_3395_, lean_object* v_receiverId_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_toApplicative_3398_; lean_object* v_toBind_3399_; lean_object* v___f_3400_; lean_object* v___f_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_toApplicative_3398_ = lean_ctor_get(v_inst_3392_, 0);
lean_inc_ref(v_toApplicative_3398_);
v_toBind_3399_ = lean_ctor_get(v_inst_3392_, 1);
lean_inc_n(v_toBind_3399_, 2);
v___f_3400_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3397_, 2);
lean_inc(v_inst_3393_);
v___f_3401_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3401_, 0, v___f_3400_);
lean_closure_set(v___f_3401_, 1, v_receiverId_3396_);
lean_closure_set(v___f_3401_, 2, v_toApplicative_3398_);
lean_closure_set(v___f_3401_, 3, v_inst_3393_);
lean_closure_set(v___f_3401_, 4, v_toBind_3399_);
lean_closure_set(v___f_3401_, 5, v_inst_3392_);
lean_closure_set(v___f_3401_, 6, v_a_3397_);
v___x_3402_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3402_, 0, lean_box(0));
lean_closure_set(v___x_3402_, 1, lean_box(0));
lean_closure_set(v___x_3402_, 2, v_a_3397_);
v___x_3403_ = lean_apply_2(v_inst_3393_, lean_box(0), v___x_3402_);
v___x_3404_ = lean_apply_4(v_toBind_3399_, lean_box(0), lean_box(0), v___x_3403_, v___f_3401_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3405_, lean_object* v_00_u03b1_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_inst_3409_, lean_object* v_inst_3410_, lean_object* v_receiverId_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3405_, v_00_u03b1_3406_, v_inst_3407_, v_inst_3408_, v_inst_3409_, v_inst_3410_, v_receiverId_3411_, v_a_3412_);
lean_dec(v_a_3412_);
lean_dec(v_inst_3410_);
lean_dec(v_inst_3409_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3416_, lean_object* v_lose_3417_){
_start:
{
lean_object* v_finished_3419_; lean_object* v_promise_3420_; lean_object* v___x_3421_; uint8_t v___y_3423_; uint8_t v___x_3431_; 
v_finished_3419_ = lean_ctor_get(v_w_3416_, 0);
v_promise_3420_ = lean_ctor_get(v_w_3416_, 1);
v___x_3421_ = lean_st_ref_take(v_finished_3419_);
v___x_3431_ = lean_unbox(v___x_3421_);
lean_dec(v___x_3421_);
if (v___x_3431_ == 0)
{
uint8_t v___x_3432_; 
v___x_3432_ = 1;
v___y_3423_ = v___x_3432_;
goto v___jp_3422_;
}
else
{
uint8_t v___x_3433_; 
v___x_3433_ = 0;
v___y_3423_ = v___x_3433_;
goto v___jp_3422_;
}
v___jp_3422_:
{
uint8_t v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3424_ = 1;
v___x_3425_ = lean_box(v___x_3424_);
v___x_3426_ = lean_st_ref_set(v_finished_3419_, v___x_3425_);
if (v___y_3423_ == 0)
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_apply_1(v_lose_3417_, lean_box(0));
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_dec_ref(v_lose_3417_);
v___x_3428_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3429_ = lean_io_promise_resolve(v___x_3428_, v_promise_3420_);
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
return v___x_3430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3434_, lean_object* v_lose_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3434_, v_lose_3435_);
lean_dec_ref(v_w_3434_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3438_, lean_object* v_w_3439_, lean_object* v_lose_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3439_, v_lose_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3443_, lean_object* v_w_3444_, lean_object* v_lose_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3443_, v_w_3444_, v_lose_3445_);
lean_dec_ref(v_w_3444_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___x_3451_; lean_object* v_receivers_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_st_ref_get(v_a_3449_);
v_receivers_3452_ = lean_ctor_get(v___x_3451_, 7);
lean_inc(v_receivers_3452_);
lean_dec(v___x_3451_);
v___x_3453_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3452_, v_receiverId_3448_);
if (lean_obj_tag(v___x_3453_) == 1)
{
lean_object* v_val_3454_; lean_object* v___x_3455_; 
v_val_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3454_, v_a_3449_);
lean_dec(v_val_3454_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3488_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3488_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3488_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
if (lean_obj_tag(v_a_3456_) == 1)
{
lean_object* v___x_3460_; lean_object* v_producers_3461_; lean_object* v_waiters_3462_; lean_object* v_capacity_3463_; lean_object* v_size_3464_; lean_object* v_buffer_3465_; lean_object* v_write_3466_; lean_object* v_read_3467_; lean_object* v_nextId_3468_; uint8_t v_closed_3469_; lean_object* v_pos_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3482_; 
v___x_3460_ = lean_st_ref_take(v_a_3449_);
v_producers_3461_ = lean_ctor_get(v___x_3460_, 0);
v_waiters_3462_ = lean_ctor_get(v___x_3460_, 1);
v_capacity_3463_ = lean_ctor_get(v___x_3460_, 2);
v_size_3464_ = lean_ctor_get(v___x_3460_, 3);
v_buffer_3465_ = lean_ctor_get(v___x_3460_, 4);
v_write_3466_ = lean_ctor_get(v___x_3460_, 5);
v_read_3467_ = lean_ctor_get(v___x_3460_, 6);
v_nextId_3468_ = lean_ctor_get(v___x_3460_, 8);
v_closed_3469_ = lean_ctor_get_uint8(v___x_3460_, sizeof(void*)*10);
v_pos_3470_ = lean_ctor_get(v___x_3460_, 9);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3482_ == 0)
{
lean_object* v_unused_3483_; 
v_unused_3483_ = lean_ctor_get(v___x_3460_, 7);
lean_dec(v_unused_3483_);
v___x_3472_ = v___x_3460_;
v_isShared_3473_ = v_isSharedCheck_3482_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_pos_3470_);
lean_inc(v_nextId_3468_);
lean_inc(v_read_3467_);
lean_inc(v_write_3466_);
lean_inc(v_buffer_3465_);
lean_inc(v_size_3464_);
lean_inc(v_capacity_3463_);
lean_inc(v_waiters_3462_);
lean_inc(v_producers_3461_);
lean_dec(v___x_3460_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3482_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3474_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3448_, v_receivers_3452_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 7, v___x_3474_);
v___x_3476_ = v___x_3472_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_producers_3461_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_waiters_3462_);
lean_ctor_set(v_reuseFailAlloc_3481_, 2, v_capacity_3463_);
lean_ctor_set(v_reuseFailAlloc_3481_, 3, v_size_3464_);
lean_ctor_set(v_reuseFailAlloc_3481_, 4, v_buffer_3465_);
lean_ctor_set(v_reuseFailAlloc_3481_, 5, v_write_3466_);
lean_ctor_set(v_reuseFailAlloc_3481_, 6, v_read_3467_);
lean_ctor_set(v_reuseFailAlloc_3481_, 7, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3481_, 8, v_nextId_3468_);
lean_ctor_set(v_reuseFailAlloc_3481_, 9, v_pos_3470_);
lean_ctor_set_uint8(v_reuseFailAlloc_3481_, sizeof(void*)*10, v_closed_3469_);
v___x_3476_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3477_ = lean_st_ref_set(v_a_3449_, v___x_3476_);
if (v_isShared_3459_ == 0)
{
v___x_3479_ = v___x_3458_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3456_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
lean_dec(v_a_3456_);
lean_dec(v_receivers_3452_);
lean_dec(v_receiverId_3448_);
v___x_3484_ = lean_box(0);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3484_);
v___x_3486_ = v___x_3458_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_dec(v_receivers_3452_);
lean_dec(v_receiverId_3448_);
return v___x_3455_;
}
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec(v___x_3453_);
lean_dec(v_receivers_3452_);
lean_dec(v_receiverId_3448_);
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
return v___x_3490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3491_, lean_object* v_a_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3491_, v_a_3492_);
lean_dec(v_a_3492_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3495_, lean_object* v_w_3496_, lean_object* v_lose_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_finished_3500_; lean_object* v_promise_3501_; lean_object* v___x_3502_; uint8_t v___y_3504_; uint8_t v___x_3528_; 
v_finished_3500_ = lean_ctor_get(v_w_3496_, 0);
v_promise_3501_ = lean_ctor_get(v_w_3496_, 1);
v___x_3502_ = lean_st_ref_take(v_finished_3500_);
v___x_3528_ = lean_unbox(v___x_3502_);
lean_dec(v___x_3502_);
if (v___x_3528_ == 0)
{
uint8_t v___x_3529_; 
v___x_3529_ = 1;
v___y_3504_ = v___x_3529_;
goto v___jp_3503_;
}
else
{
uint8_t v___x_3530_; 
v___x_3530_ = 0;
v___y_3504_ = v___x_3530_;
goto v___jp_3503_;
}
v___jp_3503_:
{
uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = 1;
v___x_3506_ = lean_box(v___x_3505_);
v___x_3507_ = lean_st_ref_set(v_finished_3500_, v___x_3506_);
if (v___y_3504_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v___x_3495_);
lean_inc(v___y_3498_);
v___x_3508_ = lean_apply_2(v_lose_3497_, v___y_3498_, lean_box(0));
return v___x_3508_;
}
else
{
lean_object* v___x_3509_; 
lean_dec_ref(v_lose_3497_);
v___x_3509_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3495_, v___y_3498_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3519_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3519_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3519_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3514_, 0, v_a_3510_);
v___x_3515_ = lean_io_promise_resolve(v___x_3514_, v_promise_3501_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3515_);
v___x_3517_ = v___x_3512_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
v_a_3520_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3509_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3509_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3531_, lean_object* v_w_3532_, lean_object* v_lose_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3531_, v_w_3532_, v_lose_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v_w_3532_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3537_, lean_object* v___x_3538_, lean_object* v_w_3539_, lean_object* v_lose_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3538_, v_w_3539_, v_lose_3540_, v___y_3541_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3544_, lean_object* v___x_3545_, lean_object* v_w_3546_, lean_object* v_lose_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3544_, v___x_3545_, v_w_3546_, v_lose_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v_w_3546_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3551_){
_start:
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3554_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3557_, lean_object* v___f_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v___x_3561_; uint8_t v_closed_3562_; 
v___x_3561_ = lean_st_ref_get(v___y_3559_);
v_closed_3562_ = lean_ctor_get_uint8(v___x_3561_, sizeof(void*)*10);
if (v_closed_3562_ == 0)
{
lean_object* v_capacity_3563_; lean_object* v_size_3564_; lean_object* v_receivers_3565_; lean_object* v___x_3566_; 
v_capacity_3563_ = lean_ctor_get(v___x_3561_, 2);
lean_inc(v_capacity_3563_);
v_size_3564_ = lean_ctor_get(v___x_3561_, 3);
lean_inc(v_size_3564_);
v_receivers_3565_ = lean_ctor_get(v___x_3561_, 7);
lean_inc(v_receivers_3565_);
lean_dec(v___x_3561_);
v___x_3566_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3565_, v_id_3557_);
lean_dec(v_receivers_3565_);
if (lean_obj_tag(v___x_3566_) == 1)
{
lean_object* v_val_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; 
v_val_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_val_3567_);
lean_dec_ref_known(v___x_3566_, 1);
v___x_3568_ = lean_unsigned_to_nat(0u);
v___x_3569_ = lean_nat_dec_eq(v_size_3564_, v___x_3568_);
lean_dec(v_size_3564_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_nat_mod(v_val_3567_, v_capacity_3563_);
lean_dec(v_capacity_3563_);
v___x_3571_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3570_, v___y_3559_);
lean_dec(v___x_3570_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3573_; lean_object* v_pos_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_a_3572_);
lean_dec_ref_known(v___x_3571_, 1);
v___x_3573_ = lean_st_ref_get(v_a_3572_);
lean_dec(v_a_3572_);
v_pos_3574_ = lean_ctor_get(v___x_3573_, 1);
lean_inc(v_pos_3574_);
lean_dec(v___x_3573_);
v___x_3575_ = lean_nat_dec_eq(v_pos_3574_, v_val_3567_);
lean_dec(v_val_3567_);
lean_dec(v_pos_3574_);
v___x_3576_ = lean_box(v___x_3575_);
lean_inc(v___y_3559_);
v___x_3577_ = lean_apply_3(v___f_3558_, v___x_3576_, v___y_3559_, lean_box(0));
return v___x_3577_;
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_val_3567_);
lean_dec_ref(v___f_3558_);
v_a_3578_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3571_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3571_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_dec(v_val_3567_);
lean_dec(v_capacity_3563_);
v___x_3586_ = lean_box(v_closed_3562_);
lean_inc(v___y_3559_);
v___x_3587_ = lean_apply_3(v___f_3558_, v___x_3586_, v___y_3559_, lean_box(0));
return v___x_3587_;
}
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_dec(v___x_3566_);
lean_dec(v_size_3564_);
lean_dec(v_capacity_3563_);
v___x_3588_ = lean_box(v_closed_3562_);
lean_inc(v___y_3559_);
v___x_3589_ = lean_apply_3(v___f_3558_, v___x_3588_, v___y_3559_, lean_box(0));
return v___x_3589_;
}
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
lean_dec(v___x_3561_);
v___x_3590_ = lean_box(v_closed_3562_);
lean_inc(v___y_3559_);
v___x_3591_ = lean_apply_3(v___f_3558_, v___x_3590_, v___y_3559_, lean_box(0));
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3592_, lean_object* v___f_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3592_, v___f_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec(v_id_3592_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v___x_3600_; lean_object* v_producers_3601_; lean_object* v_waiters_3602_; lean_object* v_capacity_3603_; lean_object* v_size_3604_; lean_object* v_buffer_3605_; lean_object* v_write_3606_; lean_object* v_read_3607_; lean_object* v_receivers_3608_; lean_object* v_nextId_3609_; uint8_t v_closed_3610_; lean_object* v_pos_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3633_; 
v___x_3600_ = lean_st_ref_get(v___y_3598_);
v_producers_3601_ = lean_ctor_get(v___x_3600_, 0);
v_waiters_3602_ = lean_ctor_get(v___x_3600_, 1);
v_capacity_3603_ = lean_ctor_get(v___x_3600_, 2);
v_size_3604_ = lean_ctor_get(v___x_3600_, 3);
v_buffer_3605_ = lean_ctor_get(v___x_3600_, 4);
v_write_3606_ = lean_ctor_get(v___x_3600_, 5);
v_read_3607_ = lean_ctor_get(v___x_3600_, 6);
v_receivers_3608_ = lean_ctor_get(v___x_3600_, 7);
v_nextId_3609_ = lean_ctor_get(v___x_3600_, 8);
v_closed_3610_ = lean_ctor_get_uint8(v___x_3600_, sizeof(void*)*10);
v_pos_3611_ = lean_ctor_get(v___x_3600_, 9);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3613_ = v___x_3600_;
v_isShared_3614_ = v_isSharedCheck_3633_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_pos_3611_);
lean_inc(v_nextId_3609_);
lean_inc(v_receivers_3608_);
lean_inc(v_read_3607_);
lean_inc(v_write_3606_);
lean_inc(v_buffer_3605_);
lean_inc(v_size_3604_);
lean_inc(v_capacity_3603_);
lean_inc(v_waiters_3602_);
lean_inc(v_producers_3601_);
lean_dec(v___x_3600_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3633_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3602_);
if (lean_obj_tag(v___x_3615_) == 1)
{
lean_object* v_val_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3630_; 
v_val_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3630_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_val_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3630_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v_fst_3620_; lean_object* v_snd_3621_; lean_object* v___x_3622_; lean_object* v___x_3624_; 
v_fst_3620_ = lean_ctor_get(v_val_3616_, 0);
lean_inc(v_fst_3620_);
v_snd_3621_ = lean_ctor_get(v_val_3616_, 1);
lean_inc(v_snd_3621_);
lean_dec(v_val_3616_);
v___x_3622_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3620_, v_____do__lift_3597_);
lean_dec(v_fst_3620_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 1, v_snd_3621_);
v___x_3624_ = v___x_3613_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_producers_3601_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_snd_3621_);
lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_capacity_3603_);
lean_ctor_set(v_reuseFailAlloc_3629_, 3, v_size_3604_);
lean_ctor_set(v_reuseFailAlloc_3629_, 4, v_buffer_3605_);
lean_ctor_set(v_reuseFailAlloc_3629_, 5, v_write_3606_);
lean_ctor_set(v_reuseFailAlloc_3629_, 6, v_read_3607_);
lean_ctor_set(v_reuseFailAlloc_3629_, 7, v_receivers_3608_);
lean_ctor_set(v_reuseFailAlloc_3629_, 8, v_nextId_3609_);
lean_ctor_set(v_reuseFailAlloc_3629_, 9, v_pos_3611_);
lean_ctor_set_uint8(v_reuseFailAlloc_3629_, sizeof(void*)*10, v_closed_3610_);
v___x_3624_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3625_; lean_object* v___x_3627_; 
v___x_3625_ = lean_st_ref_set(v___y_3598_, v___x_3624_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set_tag(v___x_3618_, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3625_);
v___x_3627_ = v___x_3618_;
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
lean_dec(v___x_3615_);
lean_del_object(v___x_3613_);
lean_dec(v_pos_3611_);
lean_dec(v_nextId_3609_);
lean_dec(v_receivers_3608_);
lean_dec(v_read_3607_);
lean_dec(v_write_3606_);
lean_dec_ref(v_buffer_3605_);
lean_dec(v_size_3604_);
lean_dec(v_capacity_3603_);
lean_dec_ref(v_producers_3601_);
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
uint8_t v_____do__lift_4156__boxed_3637_; lean_object* v_res_3638_; 
v_____do__lift_4156__boxed_3637_ = lean_unbox(v_____do__lift_3634_);
v_res_3638_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_4156__boxed_3637_, v___y_3635_);
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
v___x_3666_ = lean_st_ref_set(v___y_3643_, v___x_3665_);
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
uint8_t v_____do__lift_4212__boxed_3681_; lean_object* v_res_3682_; 
v_____do__lift_4212__boxed_3681_ = lean_unbox(v_____do__lift_3678_);
v_res_3682_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3675_, v___f_3676_, v_id_3677_, v_____do__lift_4212__boxed_3681_, v___y_3679_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_3906_, lean_object* v_capacity_3907_, lean_object* v_size_3908_, lean_object* v_buffer_3909_, lean_object* v_write_3910_, lean_object* v_read_3911_, lean_object* v_receivers_3912_, lean_object* v_nextId_3913_, uint8_t v_closed_3914_, lean_object* v_pos_3915_, lean_object* v___y_3916_, lean_object* v_x_3917_){
_start:
{
if (lean_obj_tag(v_x_3917_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3927_; 
lean_dec(v_pos_3915_);
lean_dec(v_nextId_3913_);
lean_dec(v_receivers_3912_);
lean_dec(v_read_3911_);
lean_dec(v_write_3910_);
lean_dec_ref(v_buffer_3909_);
lean_dec(v_size_3908_);
lean_dec(v_capacity_3907_);
lean_dec_ref(v_producers_3906_);
v_a_3919_ = lean_ctor_get(v_x_3917_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_x_3917_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3921_ = v_x_3917_;
v_isShared_3922_ = v_isSharedCheck_3927_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v_x_3917_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3927_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3925_; 
v___x_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3938_; 
v_a_3928_ = lean_ctor_get(v_x_3917_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_x_3917_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3930_ = v_x_3917_;
v_isShared_3931_ = v_isSharedCheck_3938_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v_x_3917_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3938_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3932_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3932_, 0, v_producers_3906_);
lean_ctor_set(v___x_3932_, 1, v_a_3928_);
lean_ctor_set(v___x_3932_, 2, v_capacity_3907_);
lean_ctor_set(v___x_3932_, 3, v_size_3908_);
lean_ctor_set(v___x_3932_, 4, v_buffer_3909_);
lean_ctor_set(v___x_3932_, 5, v_write_3910_);
lean_ctor_set(v___x_3932_, 6, v_read_3911_);
lean_ctor_set(v___x_3932_, 7, v_receivers_3912_);
lean_ctor_set(v___x_3932_, 8, v_nextId_3913_);
lean_ctor_set(v___x_3932_, 9, v_pos_3915_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*10, v_closed_3914_);
v___x_3933_ = lean_st_ref_set(v___y_3916_, v___x_3932_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v___x_3933_);
v___x_3935_ = v___x_3930_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3936_; 
v___x_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
return v___x_3936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_3939_, lean_object* v_capacity_3940_, lean_object* v_size_3941_, lean_object* v_buffer_3942_, lean_object* v_write_3943_, lean_object* v_read_3944_, lean_object* v_receivers_3945_, lean_object* v_nextId_3946_, lean_object* v_closed_3947_, lean_object* v_pos_3948_, lean_object* v___y_3949_, lean_object* v_x_3950_, lean_object* v___y_3951_){
_start:
{
uint8_t v_closed_boxed_3952_; lean_object* v_res_3953_; 
v_closed_boxed_3952_ = lean_unbox(v_closed_3947_);
v_res_3953_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_3939_, v_capacity_3940_, v_size_3941_, v_buffer_3942_, v_write_3943_, v_read_3944_, v_receivers_3945_, v_nextId_3946_, v_closed_boxed_3952_, v_pos_3948_, v___y_3949_, v_x_3950_);
lean_dec(v___y_3949_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_3954_){
_start:
{
if (lean_obj_tag(v_x_3954_) == 0)
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_x_3954_);
return v___x_3956_;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3966_; 
v_a_3957_ = lean_ctor_get(v_x_3954_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v_x_3954_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3959_ = v_x_3954_;
v_isShared_3960_ = v_isSharedCheck_3966_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v_x_3954_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3966_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3961_ = l_List_reverse___redArg(v_a_3957_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v___x_3961_);
v___x_3963_ = v___x_3959_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3961_);
v___x_3963_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3964_; 
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
return v___x_3964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_3967_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_3970_, lean_object* v___x_3971_, lean_object* v_x_3972_){
_start:
{
if (lean_obj_tag(v_x_3972_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v___x_3971_);
lean_dec(v_a_3970_);
v_a_3974_ = lean_ctor_get(v_x_3972_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_x_3972_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3976_ = v_x_3972_;
v_isShared_3977_ = v_isSharedCheck_3982_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v_x_3972_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3982_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
}
}
else
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3999_; 
v_a_3983_ = lean_ctor_get(v_x_3972_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v_x_3972_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3985_ = v_x_3972_;
v_isShared_3986_ = v_isSharedCheck_3999_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v_x_3972_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3999_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
uint8_t v___x_3987_; 
v___x_3987_ = l_List_isEmpty___redArg(v_a_3970_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; lean_object* v___x_3990_; 
lean_dec(v___x_3971_);
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v_a_3983_);
lean_ctor_set(v___x_3988_, 1, v_a_3970_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_3988_);
v___x_3990_ = v___x_3985_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; 
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
return v___x_3991_;
}
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
lean_dec(v_a_3970_);
v___x_3993_ = l_List_reverse___redArg(v_a_3983_);
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3971_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_3994_);
v___x_3996_ = v___x_3985_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
return v___x_3997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_4000_, lean_object* v___x_4001_, lean_object* v_x_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_4000_, v___x_4001_, v_x_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_4005_){
_start:
{
if (lean_obj_tag(v_x_4005_) == 0)
{
lean_object* v___x_4007_; 
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v_x_4005_);
return v___x_4007_;
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4019_; 
v_a_4008_ = lean_ctor_get(v_x_4005_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_x_4005_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4010_ = v_x_4005_;
v_isShared_4011_ = v_isSharedCheck_4019_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v_x_4005_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4019_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
uint8_t v___x_4012_; uint8_t v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4016_; 
v___x_4012_ = lean_unbox(v_a_4008_);
lean_dec(v_a_4008_);
v___x_4013_ = lean_bool_not(v___x_4012_);
v___x_4014_ = lean_box(v___x_4013_);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 0, v___x_4014_);
v___x_4016_ = v___x_4010_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; 
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_4023_, lean_object* v_x_4024_, lean_object* v_head_4025_, lean_object* v_x_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4023_, v_x_4024_, v_head_4025_, v_x_4026_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_4035_, lean_object* v_x_4036_){
_start:
{
if (lean_obj_tag(v_x_4035_) == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4038_, 0, v_x_4036_);
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
return v___x_4039_;
}
else
{
lean_object* v_head_4040_; lean_object* v_tail_4041_; lean_object* v_waiter_4042_; lean_object* v___f_4043_; lean_object* v_val_4045_; 
v_head_4040_ = lean_ctor_get(v_x_4035_, 0);
lean_inc(v_head_4040_);
v_tail_4041_ = lean_ctor_get(v_x_4035_, 1);
lean_inc(v_tail_4041_);
lean_dec_ref_known(v_x_4035_, 2);
v_waiter_4042_ = lean_ctor_get(v_head_4040_, 1);
lean_inc(v_waiter_4042_);
v___f_4043_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4043_, 0, v_tail_4041_);
lean_closure_set(v___f_4043_, 1, v_x_4036_);
lean_closure_set(v___f_4043_, 2, v_head_4040_);
if (lean_obj_tag(v_waiter_4042_) == 0)
{
lean_object* v___x_4049_; 
v___x_4049_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v_val_4045_ = v___x_4049_;
goto v___jp_4044_;
}
else
{
lean_object* v_val_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4064_; 
v_val_4050_ = lean_ctor_get(v_waiter_4042_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_waiter_4042_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4052_ = v_waiter_4042_;
v_isShared_4053_ = v_isSharedCheck_4064_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_val_4050_);
lean_dec(v_waiter_4042_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4064_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v_finished_4054_; lean_object* v___x_4055_; lean_object* v___f_4056_; lean_object* v___x_4058_; 
v_finished_4054_ = lean_ctor_get(v_val_4050_, 0);
lean_inc(v_finished_4054_);
lean_dec(v_val_4050_);
v___x_4055_ = lean_st_ref_get(v_finished_4054_);
lean_dec(v_finished_4054_);
v___f_4056_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4055_);
v___x_4058_ = v___x_4052_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4055_);
v___x_4058_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; lean_object* v___x_4062_; 
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
v___x_4060_ = lean_unsigned_to_nat(0u);
v___x_4061_ = 0;
v___x_4062_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4060_, v___x_4061_, v___x_4059_, v___f_4056_);
v_val_4045_ = v___x_4062_;
goto v___jp_4044_;
}
}
}
v___jp_4044_:
{
lean_object* v___x_4046_; uint8_t v___x_4047_; lean_object* v___x_4048_; 
v___x_4046_ = lean_unsigned_to_nat(0u);
v___x_4047_ = 0;
v___x_4048_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4046_, v___x_4047_, v_val_4045_, v___f_4043_);
return v___x_4048_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_4065_, lean_object* v_x_4066_, lean_object* v_head_4067_, lean_object* v_x_4068_){
_start:
{
if (lean_obj_tag(v_x_4068_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4078_; 
lean_dec_ref(v_head_4067_);
lean_dec(v_x_4066_);
lean_dec(v_tail_4065_);
v_a_4070_ = lean_ctor_get(v_x_4068_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_x_4068_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4072_ = v_x_4068_;
v_isShared_4073_ = v_isSharedCheck_4078_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v_x_4068_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4078_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
lean_object* v___x_4076_; 
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
return v___x_4076_;
}
}
}
else
{
lean_object* v_a_4079_; uint8_t v___x_4080_; 
v_a_4079_ = lean_ctor_get(v_x_4068_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v_x_4068_, 1);
v___x_4080_ = lean_unbox(v_a_4079_);
lean_dec(v_a_4079_);
if (v___x_4080_ == 0)
{
lean_object* v___x_4081_; 
lean_dec_ref(v_head_4067_);
v___x_4081_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4065_, v_x_4066_);
return v___x_4081_;
}
else
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4082_, 0, v_head_4067_);
lean_ctor_set(v___x_4082_, 1, v_x_4066_);
v___x_4083_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4065_, v___x_4082_);
return v___x_4083_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_4084_, lean_object* v_x_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4084_, v_x_4085_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v_eList_4088_, lean_object* v___x_4089_, lean_object* v___f_4090_, lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4091_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4101_; 
lean_dec_ref(v___f_4090_);
lean_dec(v___x_4089_);
lean_dec(v_eList_4088_);
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
lean_object* v_a_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; lean_object* v___x_4106_; lean_object* v___f_4107_; lean_object* v___x_4108_; 
v_a_4102_ = lean_ctor_get(v_x_4091_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v_x_4091_, 1);
lean_inc(v___x_4089_);
v___x_4103_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4088_, v___x_4089_);
v___x_4104_ = lean_unsigned_to_nat(0u);
v___x_4105_ = 0;
v___x_4106_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4104_, v___x_4105_, v___x_4103_, v___f_4090_);
v___f_4107_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4107_, 0, v_a_4102_);
lean_closure_set(v___f_4107_, 1, v___x_4089_);
v___x_4108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4104_, v___x_4105_, v___x_4106_, v___f_4107_);
return v___x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v_eList_4109_, lean_object* v___x_4110_, lean_object* v___f_4111_, lean_object* v_x_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v_eList_4109_, v___x_4110_, v___f_4111_, v_x_4112_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_eList_4119_; lean_object* v_dList_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___f_4123_; lean_object* v___x_4124_; uint8_t v___x_4125_; lean_object* v___x_4126_; lean_object* v___f_4127_; lean_object* v___x_4128_; 
v_eList_4119_ = lean_ctor_get(v_q_4116_, 0);
lean_inc(v_eList_4119_);
v_dList_4120_ = lean_ctor_get(v_q_4116_, 1);
lean_inc(v_dList_4120_);
lean_dec_ref(v_q_4116_);
v___x_4121_ = lean_box(0);
v___x_4122_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4120_, v___x_4121_);
v___f_4123_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4124_ = lean_unsigned_to_nat(0u);
v___x_4125_ = 0;
v___x_4126_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4124_, v___x_4125_, v___x_4122_, v___f_4123_);
v___f_4127_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4127_, 0, v_eList_4119_);
lean_closure_set(v___f_4127_, 1, v___x_4121_);
lean_closure_set(v___f_4127_, 2, v___f_4123_);
v___x_4128_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4124_, v___x_4125_, v___x_4126_, v___f_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4129_, v___y_4130_);
lean_dec(v___y_4130_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4133_, lean_object* v_x_4134_){
_start:
{
if (lean_obj_tag(v_x_4134_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4144_; 
v_a_4136_ = lean_ctor_get(v_x_4134_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_x_4134_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4138_ = v_x_4134_;
v_isShared_4139_ = v_isSharedCheck_4144_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v_x_4134_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4144_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
lean_object* v___x_4142_; 
v___x_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4141_);
return v___x_4142_;
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v_producers_4146_; lean_object* v_waiters_4147_; lean_object* v_capacity_4148_; lean_object* v_size_4149_; lean_object* v_buffer_4150_; lean_object* v_write_4151_; lean_object* v_read_4152_; lean_object* v_receivers_4153_; lean_object* v_nextId_4154_; uint8_t v_closed_4155_; lean_object* v_pos_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___f_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; lean_object* v___x_4162_; 
v_a_4145_ = lean_ctor_get(v_x_4134_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v_x_4134_, 1);
v_producers_4146_ = lean_ctor_get(v_a_4145_, 0);
lean_inc_ref(v_producers_4146_);
v_waiters_4147_ = lean_ctor_get(v_a_4145_, 1);
lean_inc_ref(v_waiters_4147_);
v_capacity_4148_ = lean_ctor_get(v_a_4145_, 2);
lean_inc(v_capacity_4148_);
v_size_4149_ = lean_ctor_get(v_a_4145_, 3);
lean_inc(v_size_4149_);
v_buffer_4150_ = lean_ctor_get(v_a_4145_, 4);
lean_inc_ref(v_buffer_4150_);
v_write_4151_ = lean_ctor_get(v_a_4145_, 5);
lean_inc(v_write_4151_);
v_read_4152_ = lean_ctor_get(v_a_4145_, 6);
lean_inc(v_read_4152_);
v_receivers_4153_ = lean_ctor_get(v_a_4145_, 7);
lean_inc(v_receivers_4153_);
v_nextId_4154_ = lean_ctor_get(v_a_4145_, 8);
lean_inc(v_nextId_4154_);
v_closed_4155_ = lean_ctor_get_uint8(v_a_4145_, sizeof(void*)*10);
v_pos_4156_ = lean_ctor_get(v_a_4145_, 9);
lean_inc(v_pos_4156_);
lean_dec(v_a_4145_);
v___x_4157_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4147_, v___y_4133_);
v___x_4158_ = lean_box(v_closed_4155_);
lean_inc(v___y_4133_);
v___f_4159_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4159_, 0, v_producers_4146_);
lean_closure_set(v___f_4159_, 1, v_capacity_4148_);
lean_closure_set(v___f_4159_, 2, v_size_4149_);
lean_closure_set(v___f_4159_, 3, v_buffer_4150_);
lean_closure_set(v___f_4159_, 4, v_write_4151_);
lean_closure_set(v___f_4159_, 5, v_read_4152_);
lean_closure_set(v___f_4159_, 6, v_receivers_4153_);
lean_closure_set(v___f_4159_, 7, v_nextId_4154_);
lean_closure_set(v___f_4159_, 8, v___x_4158_);
lean_closure_set(v___f_4159_, 9, v_pos_4156_);
lean_closure_set(v___f_4159_, 10, v___y_4133_);
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = 0;
v___x_4162_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4160_, v___x_4161_, v___x_4157_, v___f_4159_);
return v___x_4162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4163_, lean_object* v_x_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4163_, v_x_4164_);
lean_dec(v___y_4163_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; lean_object* v___f_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; uint8_t v___x_4174_; lean_object* v___x_4175_; 
v___x_4169_ = lean_st_ref_get(v___y_4167_);
lean_inc(v___y_4167_);
v___f_4170_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4170_, 0, v___y_4167_);
v___x_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
v___x_4173_ = lean_unsigned_to_nat(0u);
v___x_4174_ = 0;
v___x_4175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4173_, v___x_4174_, v___x_4172_, v___f_4170_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4176_);
lean_dec(v___y_4176_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4179_, lean_object* v_waiter_4180_){
_start:
{
lean_object* v_val_4183_; lean_object* v___x_4185_; 
v___x_4185_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4179_, v_waiter_4180_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set_tag(v___x_4188_, 1);
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
v_val_4183_ = v___x_4191_;
goto v___jp_4182_;
}
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
v_a_4194_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4185_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4185_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
lean_ctor_set_tag(v___x_4196_, 0);
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
v_val_4183_ = v___x_4199_;
goto v___jp_4182_;
}
}
}
v___jp_4182_:
{
lean_object* v___x_4184_; 
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v_val_4183_);
return v___x_4184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4202_, lean_object* v_waiter_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4202_, v_waiter_4203_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4206_){
_start:
{
if (lean_obj_tag(v_x_4206_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4216_; 
v_a_4208_ = lean_ctor_get(v_x_4206_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v_x_4206_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4210_ = v_x_4206_;
v_isShared_4211_ = v_isSharedCheck_4216_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v_x_4206_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4216_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
return v___x_4214_;
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4226_; 
v_a_4217_ = lean_ctor_get(v_x_4206_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v_x_4206_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4219_ = v_x_4206_;
v_isShared_4220_ = v_isSharedCheck_4226_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v_x_4206_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4226_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4221_; lean_object* v___x_4223_; 
v___x_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4221_, 0, v_a_4217_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4221_);
v___x_4223_ = v___x_4219_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
return v___x_4224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4227_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_val_4230_, lean_object* v_x_4231_){
_start:
{
if (lean_obj_tag(v_x_4231_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4241_; 
v_a_4233_ = lean_ctor_get(v_x_4231_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_x_4231_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4235_ = v_x_4231_;
v_isShared_4236_ = v_isSharedCheck_4241_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v_x_4231_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4241_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___x_4238_);
return v___x_4239_;
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4253_; 
v_a_4242_ = lean_ctor_get(v_x_4231_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v_x_4231_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4244_ = v_x_4231_;
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v_x_4231_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4253_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v_pos_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4250_; 
v_pos_4246_ = lean_ctor_get(v_a_4242_, 1);
lean_inc(v_pos_4246_);
lean_dec(v_a_4242_);
v___x_4247_ = lean_nat_dec_eq(v_pos_4246_, v_val_4230_);
lean_dec(v_pos_4246_);
v___x_4248_ = lean_box(v___x_4247_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v___x_4248_);
v___x_4250_ = v___x_4244_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4251_; 
v___x_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
return v___x_4251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_val_4254_, lean_object* v_x_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_val_4254_, v_x_4255_);
lean_dec(v_val_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v___x_4258_, uint8_t v_closed_4259_, lean_object* v___f_4260_, lean_object* v_x_4261_){
_start:
{
if (lean_obj_tag(v_x_4261_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4271_; 
lean_dec_ref(v___f_4260_);
lean_dec(v___x_4258_);
v_a_4263_ = lean_ctor_get(v_x_4261_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_x_4261_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4265_ = v_x_4261_;
v_isShared_4266_ = v_isSharedCheck_4271_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v_x_4261_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4271_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4282_; 
v_a_4272_ = lean_ctor_get(v_x_4261_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v_x_4261_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4274_ = v_x_4261_;
v_isShared_4275_ = v_isSharedCheck_4282_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v_x_4261_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4282_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4276_ = lean_st_ref_get(v_a_4272_);
lean_dec(v_a_4272_);
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v___x_4276_);
v___x_4278_ = v___x_4274_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
v___x_4280_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4258_, v_closed_4259_, v___x_4279_, v___f_4260_);
return v___x_4280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v___x_4283_, lean_object* v_closed_4284_, lean_object* v___f_4285_, lean_object* v_x_4286_, lean_object* v___y_4287_){
_start:
{
uint8_t v_closed_boxed_4288_; lean_object* v_res_4289_; 
v_closed_boxed_4288_ = lean_unbox(v_closed_4284_);
v_res_4289_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v___x_4283_, v_closed_boxed_4288_, v___f_4285_, v_x_4286_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v_id_4290_, lean_object* v___y_4291_, lean_object* v_x_4292_){
_start:
{
if (lean_obj_tag(v_x_4292_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4302_; 
v_a_4294_ = lean_ctor_get(v_x_4292_, 0);
v_isSharedCheck_4302_ = !lean_is_exclusive(v_x_4292_);
if (v_isSharedCheck_4302_ == 0)
{
v___x_4296_ = v_x_4292_;
v_isShared_4297_ = v_isSharedCheck_4302_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v_x_4292_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4302_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
lean_object* v___x_4300_; 
v___x_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4299_);
return v___x_4300_;
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v___x_4305_; uint8_t v_isShared_4306_; uint8_t v_isSharedCheck_4342_; 
v_a_4303_ = lean_ctor_get(v_x_4292_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_x_4292_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4305_ = v_x_4292_;
v_isShared_4306_ = v_isSharedCheck_4342_;
goto v_resetjp_4304_;
}
else
{
lean_inc(v_a_4303_);
lean_dec(v_x_4292_);
v___x_4305_ = lean_box(0);
v_isShared_4306_ = v_isSharedCheck_4342_;
goto v_resetjp_4304_;
}
v_resetjp_4304_:
{
uint8_t v_closed_4307_; 
v_closed_4307_ = lean_ctor_get_uint8(v_a_4303_, sizeof(void*)*10);
if (v_closed_4307_ == 0)
{
lean_object* v_capacity_4308_; lean_object* v_size_4309_; lean_object* v_receivers_4310_; lean_object* v___x_4311_; 
v_capacity_4308_ = lean_ctor_get(v_a_4303_, 2);
lean_inc(v_capacity_4308_);
v_size_4309_ = lean_ctor_get(v_a_4303_, 3);
lean_inc(v_size_4309_);
v_receivers_4310_ = lean_ctor_get(v_a_4303_, 7);
lean_inc(v_receivers_4310_);
lean_dec(v_a_4303_);
v___x_4311_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4310_, v_id_4290_);
lean_dec(v_receivers_4310_);
if (lean_obj_tag(v___x_4311_) == 1)
{
lean_object* v_val_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4331_; 
v_val_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4331_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_val_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4331_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_nat_dec_eq(v_size_4309_, v___x_4316_);
lean_dec(v_size_4309_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___f_4320_; lean_object* v___x_4321_; lean_object* v___f_4322_; lean_object* v___x_4323_; 
lean_del_object(v___x_4314_);
lean_del_object(v___x_4305_);
v___x_4318_ = lean_nat_mod(v_val_4312_, v_capacity_4308_);
lean_dec(v_capacity_4308_);
v___x_4319_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4318_, v___y_4291_);
v___f_4320_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4320_, 0, v_val_4312_);
v___x_4321_ = lean_box(v_closed_4307_);
v___f_4322_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_4322_, 0, v___x_4316_);
lean_closure_set(v___f_4322_, 1, v___x_4321_);
lean_closure_set(v___f_4322_, 2, v___f_4320_);
v___x_4323_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4316_, v_closed_4307_, v___x_4319_, v___f_4322_);
return v___x_4323_;
}
else
{
lean_object* v___x_4324_; lean_object* v___x_4326_; 
lean_dec(v_val_4312_);
lean_dec(v_capacity_4308_);
v___x_4324_ = lean_box(v_closed_4307_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4324_);
v___x_4326_ = v___x_4305_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4324_);
v___x_4326_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
lean_object* v___x_4328_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4326_);
v___x_4328_ = v___x_4314_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4326_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
}
else
{
lean_object* v___x_4332_; lean_object* v___x_4334_; 
lean_dec(v___x_4311_);
lean_dec(v_size_4309_);
lean_dec(v_capacity_4308_);
v___x_4332_ = lean_box(v_closed_4307_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4332_);
v___x_4334_ = v___x_4305_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4332_);
v___x_4334_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4335_; 
v___x_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
return v___x_4335_;
}
}
}
else
{
lean_object* v___x_4337_; lean_object* v___x_4339_; 
lean_dec(v_a_4303_);
v___x_4337_ = lean_box(v_closed_4307_);
if (v_isShared_4306_ == 0)
{
lean_ctor_set(v___x_4305_, 0, v___x_4337_);
v___x_4339_ = v___x_4305_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4337_);
v___x_4339_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
return v___x_4340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v_id_4343_, lean_object* v___y_4344_, lean_object* v_x_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v_id_4343_, v___y_4344_, v_x_4345_);
lean_dec(v___y_4344_);
lean_dec(v_id_4343_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4348_, lean_object* v_x_4349_){
_start:
{
if (lean_obj_tag(v_x_4349_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4359_; 
lean_dec_ref(v_x_4348_);
v_a_4351_ = lean_ctor_get(v_x_4349_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v_x_4349_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4353_ = v_x_4349_;
v_isShared_4354_ = v_isSharedCheck_4359_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v_x_4349_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4359_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
lean_object* v___x_4357_; 
v___x_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
return v___x_4357_;
}
}
}
else
{
lean_object* v___x_4360_; 
lean_dec_ref_known(v_x_4349_, 1);
v___x_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4360_, 0, v_x_4348_);
return v___x_4360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4361_, v_x_4362_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4371_, lean_object* v_receiverId_4372_, lean_object* v_receivers_4373_, lean_object* v_x_4374_){
_start:
{
if (lean_obj_tag(v_x_4374_) == 0)
{
lean_object* v___x_4376_; 
lean_dec(v_receivers_4373_);
lean_dec(v_receiverId_4372_);
v___x_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4376_, 0, v_x_4374_);
return v___x_4376_;
}
else
{
lean_object* v_a_4377_; 
v_a_4377_ = lean_ctor_get(v_x_4374_, 0);
if (lean_obj_tag(v_a_4377_) == 1)
{
lean_object* v___x_4378_; lean_object* v_producers_4379_; lean_object* v_waiters_4380_; lean_object* v_capacity_4381_; lean_object* v_size_4382_; lean_object* v_buffer_4383_; lean_object* v_write_4384_; lean_object* v_read_4385_; lean_object* v_nextId_4386_; uint8_t v_closed_4387_; lean_object* v_pos_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4402_; 
v___x_4378_ = lean_st_ref_take(v_a_4371_);
v_producers_4379_ = lean_ctor_get(v___x_4378_, 0);
v_waiters_4380_ = lean_ctor_get(v___x_4378_, 1);
v_capacity_4381_ = lean_ctor_get(v___x_4378_, 2);
v_size_4382_ = lean_ctor_get(v___x_4378_, 3);
v_buffer_4383_ = lean_ctor_get(v___x_4378_, 4);
v_write_4384_ = lean_ctor_get(v___x_4378_, 5);
v_read_4385_ = lean_ctor_get(v___x_4378_, 6);
v_nextId_4386_ = lean_ctor_get(v___x_4378_, 8);
v_closed_4387_ = lean_ctor_get_uint8(v___x_4378_, sizeof(void*)*10);
v_pos_4388_ = lean_ctor_get(v___x_4378_, 9);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4402_ == 0)
{
lean_object* v_unused_4403_; 
v_unused_4403_ = lean_ctor_get(v___x_4378_, 7);
lean_dec(v_unused_4403_);
v___x_4390_ = v___x_4378_;
v_isShared_4391_ = v_isSharedCheck_4402_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_pos_4388_);
lean_inc(v_nextId_4386_);
lean_inc(v_read_4385_);
lean_inc(v_write_4384_);
lean_inc(v_buffer_4383_);
lean_inc(v_size_4382_);
lean_inc(v_capacity_4381_);
lean_inc(v_waiters_4380_);
lean_inc(v_producers_4379_);
lean_dec(v___x_4378_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4402_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4392_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4372_, v_receivers_4373_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 7, v___x_4392_);
v___x_4394_ = v___x_4390_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_producers_4379_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_waiters_4380_);
lean_ctor_set(v_reuseFailAlloc_4401_, 2, v_capacity_4381_);
lean_ctor_set(v_reuseFailAlloc_4401_, 3, v_size_4382_);
lean_ctor_set(v_reuseFailAlloc_4401_, 4, v_buffer_4383_);
lean_ctor_set(v_reuseFailAlloc_4401_, 5, v_write_4384_);
lean_ctor_set(v_reuseFailAlloc_4401_, 6, v_read_4385_);
lean_ctor_set(v_reuseFailAlloc_4401_, 7, v___x_4392_);
lean_ctor_set(v_reuseFailAlloc_4401_, 8, v_nextId_4386_);
lean_ctor_set(v_reuseFailAlloc_4401_, 9, v_pos_4388_);
lean_ctor_set_uint8(v_reuseFailAlloc_4401_, sizeof(void*)*10, v_closed_4387_);
v___x_4394_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; lean_object* v___f_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; lean_object* v___x_4400_; 
v___x_4395_ = lean_st_ref_set(v_a_4371_, v___x_4394_);
v___f_4396_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4396_, 0, v_x_4374_);
v___x_4397_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
v___x_4398_ = lean_unsigned_to_nat(0u);
v___x_4399_ = 0;
v___x_4400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4398_, v___x_4399_, v___x_4397_, v___f_4396_);
return v___x_4400_;
}
}
}
else
{
lean_object* v___x_4404_; 
lean_dec_ref_known(v_x_4374_, 1);
lean_dec(v_receivers_4373_);
lean_dec(v_receiverId_4372_);
v___x_4404_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4405_, lean_object* v_receiverId_4406_, lean_object* v_receivers_4407_, lean_object* v_x_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4405_, v_receiverId_4406_, v_receivers_4407_, v_x_4408_);
lean_dec(v_a_4405_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4411_){
_start:
{
if (lean_obj_tag(v_x_4411_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4421_; 
v_a_4413_ = lean_ctor_get(v_x_4411_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_x_4411_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4415_ = v_x_4411_;
v_isShared_4416_ = v_isSharedCheck_4421_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v_x_4411_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4421_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; 
v___x_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
return v___x_4419_;
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4434_; 
v_a_4422_ = lean_ctor_get(v_x_4411_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v_x_4411_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4424_ = v_x_4411_;
v_isShared_4425_ = v_isSharedCheck_4434_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v_x_4411_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4434_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v_size_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4431_; 
v_size_4426_ = lean_ctor_get(v_a_4422_, 3);
lean_inc(v_size_4426_);
lean_dec(v_a_4422_);
v___x_4427_ = lean_unsigned_to_nat(0u);
v___x_4428_ = lean_nat_dec_eq(v_size_4426_, v___x_4427_);
lean_dec(v_size_4426_);
v___x_4429_ = lean_box(v___x_4428_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4429_);
v___x_4431_ = v___x_4424_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4432_; 
v___x_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
return v___x_4432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4435_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4439_){
_start:
{
lean_object* v___x_4441_; lean_object* v___f_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; uint8_t v___x_4446_; lean_object* v___x_4447_; 
v___x_4441_ = lean_st_ref_get(v_a_4439_);
v___f_4442_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4441_);
v___x_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
v___x_4445_ = lean_unsigned_to_nat(0u);
v___x_4446_ = 0;
v___x_4447_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4445_, v___x_4446_, v___x_4444_, v___f_4442_);
return v___x_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4448_);
lean_dec(v_a_4448_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4451_, lean_object* v_next_4452_){
_start:
{
lean_object* v___x_4454_; lean_object* v_fst_4456_; lean_object* v_snd_4457_; lean_object* v_value_4461_; lean_object* v_pos_4462_; lean_object* v_remaining_4463_; uint8_t v___x_4464_; uint8_t v___x_4465_; 
v___x_4454_ = lean_st_ref_take(v_slot_4451_);
v_value_4461_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_value_4461_);
v_pos_4462_ = lean_ctor_get(v___x_4454_, 1);
lean_inc(v_pos_4462_);
v_remaining_4463_ = lean_ctor_get(v___x_4454_, 2);
lean_inc(v_remaining_4463_);
v___x_4464_ = lean_nat_dec_eq(v_next_4452_, v_pos_4462_);
v___x_4465_ = lean_bool_not(v___x_4464_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4484_; 
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4484_ == 0)
{
lean_object* v_unused_4485_; lean_object* v_unused_4486_; lean_object* v_unused_4487_; 
v_unused_4485_ = lean_ctor_get(v___x_4454_, 2);
lean_dec(v_unused_4485_);
v_unused_4486_ = lean_ctor_get(v___x_4454_, 1);
lean_dec(v_unused_4486_);
v_unused_4487_ = lean_ctor_get(v___x_4454_, 0);
lean_dec(v_unused_4487_);
v___x_4467_ = v___x_4454_;
v_isShared_4468_ = v_isSharedCheck_4484_;
goto v_resetjp_4466_;
}
else
{
lean_dec(v___x_4454_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4484_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4469_; uint8_t v___x_4470_; 
v___x_4469_ = lean_unsigned_to_nat(1u);
v___x_4470_ = lean_nat_dec_eq(v_remaining_4463_, v___x_4469_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4471_ = lean_box(v___x_4470_);
lean_inc(v_value_4461_);
v___x_4472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4472_, 0, v_value_4461_);
lean_ctor_set(v___x_4472_, 1, v___x_4471_);
v___x_4473_ = lean_nat_sub(v_remaining_4463_, v___x_4469_);
lean_dec(v_remaining_4463_);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 2, v___x_4473_);
v___x_4475_ = v___x_4467_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_value_4461_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v_pos_4462_);
lean_ctor_set(v_reuseFailAlloc_4476_, 2, v___x_4473_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
v_fst_4456_ = v___x_4472_;
v_snd_4457_ = v___x_4475_;
goto v___jp_4455_;
}
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4482_; 
lean_dec(v_remaining_4463_);
v___x_4477_ = lean_box(v___x_4470_);
v___x_4478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4478_, 0, v_value_4461_);
lean_ctor_set(v___x_4478_, 1, v___x_4477_);
v___x_4479_ = lean_box(0);
v___x_4480_ = lean_unsigned_to_nat(0u);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 2, v___x_4480_);
lean_ctor_set(v___x_4467_, 0, v___x_4479_);
v___x_4482_ = v___x_4467_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4479_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v_pos_4462_);
lean_ctor_set(v_reuseFailAlloc_4483_, 2, v___x_4480_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
v_fst_4456_ = v___x_4478_;
v_snd_4457_ = v___x_4482_;
goto v___jp_4455_;
}
}
}
}
else
{
lean_object* v___x_4488_; 
lean_dec(v_remaining_4463_);
lean_dec(v_pos_4462_);
lean_dec(v_value_4461_);
v___x_4488_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___closed__0));
v_fst_4456_ = v___x_4488_;
v_snd_4457_ = v___x_4454_;
goto v___jp_4455_;
}
v___jp_4455_:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4458_ = lean_st_ref_set(v_slot_4451_, v_snd_4457_);
v___x_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4459_, 0, v_fst_4456_);
v___x_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
return v___x_4460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4489_, lean_object* v_next_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4489_, v_next_4490_);
lean_dec(v_next_4490_);
lean_dec(v_slot_4489_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4493_, uint8_t v_a_4494_, lean_object* v___f_4495_, lean_object* v_x_4496_){
_start:
{
if (lean_obj_tag(v_x_4496_) == 0)
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4506_; 
lean_dec_ref(v___f_4495_);
v_a_4498_ = lean_ctor_get(v_x_4496_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v_x_4496_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4500_ = v_x_4496_;
v_isShared_4501_ = v_isSharedCheck_4506_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v_x_4496_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4506_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4504_; 
v___x_4504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4503_);
return v___x_4504_;
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v_a_4507_ = lean_ctor_get(v_x_4496_, 0);
lean_inc(v_a_4507_);
lean_dec_ref_known(v_x_4496_, 1);
v___x_4508_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4507_, v_next_4493_);
lean_dec(v_a_4507_);
v___x_4509_ = lean_unsigned_to_nat(0u);
v___x_4510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4509_, v_a_4494_, v___x_4508_, v___f_4495_);
return v___x_4510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4511_, lean_object* v_a_4512_, lean_object* v___f_4513_, lean_object* v_x_4514_, lean_object* v___y_4515_){
_start:
{
uint8_t v_a_12231__boxed_4516_; lean_object* v_res_4517_; 
v_a_12231__boxed_4516_ = lean_unbox(v_a_4512_);
v_res_4517_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4511_, v_a_12231__boxed_4516_, v___f_4513_, v_x_4514_);
lean_dec(v_next_4511_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4518_, lean_object* v___f_4519_, lean_object* v_____r_4520_, lean_object* v_st_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4524_ = lean_st_ref_set(v___y_4522_, v_st_4521_);
v___x_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
v___x_4527_ = lean_unsigned_to_nat(0u);
v___x_4528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4527_, v_a_4518_, v___x_4526_, v___f_4519_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4529_, lean_object* v___f_4530_, lean_object* v_____r_4531_, lean_object* v_st_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
uint8_t v_a_12269__boxed_4535_; lean_object* v_res_4536_; 
v_a_12269__boxed_4535_ = lean_unbox(v_a_4529_);
v_res_4536_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_12269__boxed_4535_, v___f_4530_, v_____r_4531_, v_st_4532_, v___y_4533_);
lean_dec(v___y_4533_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4537_, lean_object* v_waiters_4538_, lean_object* v_capacity_4539_, lean_object* v_size_4540_, lean_object* v_buffer_4541_, lean_object* v_write_4542_, lean_object* v_read_4543_, lean_object* v_receivers_4544_, lean_object* v_nextId_4545_, uint8_t v_closed_4546_, lean_object* v_pos_4547_, lean_object* v___f_4548_, lean_object* v_a_4549_, lean_object* v_x_4550_){
_start:
{
if (lean_obj_tag(v_x_4550_) == 0)
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4560_; 
lean_dec_ref(v___f_4548_);
lean_dec(v_pos_4547_);
lean_dec(v_nextId_4545_);
lean_dec(v_receivers_4544_);
lean_dec(v_read_4543_);
lean_dec(v_write_4542_);
lean_dec_ref(v_buffer_4541_);
lean_dec(v_size_4540_);
lean_dec(v_capacity_4539_);
lean_dec_ref(v_waiters_4538_);
lean_dec_ref(v_snd_4537_);
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
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
lean_dec_ref_known(v_x_4550_, 1);
v___x_4561_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4561_, 0, v_snd_4537_);
lean_ctor_set(v___x_4561_, 1, v_waiters_4538_);
lean_ctor_set(v___x_4561_, 2, v_capacity_4539_);
lean_ctor_set(v___x_4561_, 3, v_size_4540_);
lean_ctor_set(v___x_4561_, 4, v_buffer_4541_);
lean_ctor_set(v___x_4561_, 5, v_write_4542_);
lean_ctor_set(v___x_4561_, 6, v_read_4543_);
lean_ctor_set(v___x_4561_, 7, v_receivers_4544_);
lean_ctor_set(v___x_4561_, 8, v_nextId_4545_);
lean_ctor_set(v___x_4561_, 9, v_pos_4547_);
lean_ctor_set_uint8(v___x_4561_, sizeof(void*)*10, v_closed_4546_);
v___x_4562_ = lean_box(0);
lean_inc(v_a_4549_);
v___x_4563_ = lean_apply_4(v___f_4548_, v___x_4562_, v___x_4561_, v_a_4549_, lean_box(0));
return v___x_4563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4564_, lean_object* v_waiters_4565_, lean_object* v_capacity_4566_, lean_object* v_size_4567_, lean_object* v_buffer_4568_, lean_object* v_write_4569_, lean_object* v_read_4570_, lean_object* v_receivers_4571_, lean_object* v_nextId_4572_, lean_object* v_closed_4573_, lean_object* v_pos_4574_, lean_object* v___f_4575_, lean_object* v_a_4576_, lean_object* v_x_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v_closed_boxed_4579_; lean_object* v_res_4580_; 
v_closed_boxed_4579_ = lean_unbox(v_closed_4573_);
v_res_4580_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4564_, v_waiters_4565_, v_capacity_4566_, v_size_4567_, v_buffer_4568_, v_write_4569_, v_read_4570_, v_receivers_4571_, v_nextId_4572_, v_closed_boxed_4579_, v_pos_4574_, v___f_4575_, v_a_4576_, v_x_4577_);
lean_dec(v_a_4576_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4581_, lean_object* v_x_4582_){
_start:
{
if (lean_obj_tag(v_x_4582_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4592_; 
lean_dec(v_fst_4581_);
v_a_4584_ = lean_ctor_get(v_x_4582_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_x_4582_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4586_ = v_x_4582_;
v_isShared_4587_ = v_isSharedCheck_4592_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v_x_4582_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4592_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
lean_object* v___x_4590_; 
v___x_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
return v___x_4590_;
}
}
}
else
{
lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4600_; 
v_isSharedCheck_4600_ = !lean_is_exclusive(v_x_4582_);
if (v_isSharedCheck_4600_ == 0)
{
lean_object* v_unused_4601_; 
v_unused_4601_ = lean_ctor_get(v_x_4582_, 0);
lean_dec(v_unused_4601_);
v___x_4594_ = v_x_4582_;
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
else
{
lean_dec(v_x_4582_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4600_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v_fst_4581_);
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_fst_4581_);
v___x_4597_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
lean_object* v___x_4598_; 
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4597_);
return v___x_4598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4602_, lean_object* v_x_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4602_, v_x_4603_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, uint8_t v___x_4609_, lean_object* v_x_4610_){
_start:
{
if (lean_obj_tag(v_x_4610_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4620_; 
lean_dec_ref(v_a_4607_);
v_a_4612_ = lean_ctor_get(v_x_4610_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v_x_4610_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4614_ = v_x_4610_;
v_isShared_4615_ = v_isSharedCheck_4620_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v_x_4610_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4620_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
lean_object* v___x_4618_; 
v___x_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4617_);
return v___x_4618_;
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4668_; 
v_a_4621_ = lean_ctor_get(v_x_4610_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v_x_4610_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4623_ = v_x_4610_;
v_isShared_4624_ = v_isSharedCheck_4668_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v_x_4610_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4668_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v_fst_4625_; 
v_fst_4625_ = lean_ctor_get(v_a_4621_, 0);
lean_inc(v_fst_4625_);
if (lean_obj_tag(v_fst_4625_) == 1)
{
lean_object* v_snd_4626_; lean_object* v___f_4627_; lean_object* v___x_4628_; lean_object* v___f_4629_; uint8_t v___x_4630_; 
v_snd_4626_ = lean_ctor_get(v_a_4621_, 1);
lean_inc(v_snd_4626_);
lean_dec(v_a_4621_);
v___f_4627_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4627_, 0, v_fst_4625_);
v___x_4628_ = lean_box(v_a_4606_);
lean_inc_ref(v___f_4627_);
v___f_4629_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4629_, 0, v___x_4628_);
lean_closure_set(v___f_4629_, 1, v___f_4627_);
v___x_4630_ = lean_unbox(v_snd_4626_);
lean_dec(v_snd_4626_);
if (v___x_4630_ == 0)
{
lean_object* v___x_4631_; lean_object* v___x_4632_; 
lean_dec_ref(v___f_4629_);
lean_del_object(v___x_4623_);
v___x_4631_ = lean_box(0);
v___x_4632_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4606_, v___f_4627_, v___x_4631_, v_a_4607_, v_a_4608_);
return v___x_4632_;
}
else
{
lean_object* v___x_4633_; lean_object* v_producers_4634_; lean_object* v_waiters_4635_; lean_object* v_capacity_4636_; lean_object* v_size_4637_; lean_object* v_buffer_4638_; lean_object* v_write_4639_; lean_object* v_read_4640_; lean_object* v_receivers_4641_; lean_object* v_nextId_4642_; uint8_t v_closed_4643_; lean_object* v_pos_4644_; lean_object* v___x_4645_; 
v___x_4633_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4607_);
v_producers_4634_ = lean_ctor_get(v___x_4633_, 0);
lean_inc_ref(v_producers_4634_);
v_waiters_4635_ = lean_ctor_get(v___x_4633_, 1);
lean_inc_ref(v_waiters_4635_);
v_capacity_4636_ = lean_ctor_get(v___x_4633_, 2);
lean_inc(v_capacity_4636_);
v_size_4637_ = lean_ctor_get(v___x_4633_, 3);
lean_inc(v_size_4637_);
v_buffer_4638_ = lean_ctor_get(v___x_4633_, 4);
lean_inc_ref(v_buffer_4638_);
v_write_4639_ = lean_ctor_get(v___x_4633_, 5);
lean_inc(v_write_4639_);
v_read_4640_ = lean_ctor_get(v___x_4633_, 6);
lean_inc(v_read_4640_);
v_receivers_4641_ = lean_ctor_get(v___x_4633_, 7);
lean_inc(v_receivers_4641_);
v_nextId_4642_ = lean_ctor_get(v___x_4633_, 8);
lean_inc(v_nextId_4642_);
v_closed_4643_ = lean_ctor_get_uint8(v___x_4633_, sizeof(void*)*10);
v_pos_4644_ = lean_ctor_get(v___x_4633_, 9);
lean_inc(v_pos_4644_);
v___x_4645_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4634_);
if (lean_obj_tag(v___x_4645_) == 1)
{
lean_object* v_val_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4664_; 
lean_dec_ref(v___x_4633_);
lean_dec_ref(v___f_4627_);
v_val_4646_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4648_ = v___x_4645_;
v_isShared_4649_ = v_isSharedCheck_4664_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_val_4646_);
lean_dec(v___x_4645_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4664_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v_fst_4650_; lean_object* v_snd_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___f_4655_; lean_object* v___x_4657_; 
v_fst_4650_ = lean_ctor_get(v_val_4646_, 0);
lean_inc(v_fst_4650_);
v_snd_4651_ = lean_ctor_get(v_val_4646_, 1);
lean_inc(v_snd_4651_);
lean_dec(v_val_4646_);
v___x_4652_ = lean_box(v___x_4609_);
v___x_4653_ = lean_io_promise_resolve(v___x_4652_, v_fst_4650_);
lean_dec(v_fst_4650_);
v___x_4654_ = lean_box(v_closed_4643_);
lean_inc(v_a_4608_);
v___f_4655_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4655_, 0, v_snd_4651_);
lean_closure_set(v___f_4655_, 1, v_waiters_4635_);
lean_closure_set(v___f_4655_, 2, v_capacity_4636_);
lean_closure_set(v___f_4655_, 3, v_size_4637_);
lean_closure_set(v___f_4655_, 4, v_buffer_4638_);
lean_closure_set(v___f_4655_, 5, v_write_4639_);
lean_closure_set(v___f_4655_, 6, v_read_4640_);
lean_closure_set(v___f_4655_, 7, v_receivers_4641_);
lean_closure_set(v___f_4655_, 8, v_nextId_4642_);
lean_closure_set(v___f_4655_, 9, v___x_4654_);
lean_closure_set(v___f_4655_, 10, v_pos_4644_);
lean_closure_set(v___f_4655_, 11, v___f_4629_);
lean_closure_set(v___f_4655_, 12, v_a_4608_);
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 0, v___x_4653_);
v___x_4657_ = v___x_4623_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4653_);
v___x_4657_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4659_; 
if (v_isShared_4649_ == 0)
{
lean_ctor_set_tag(v___x_4648_, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4657_);
v___x_4659_ = v___x_4648_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4660_ = lean_unsigned_to_nat(0u);
v___x_4661_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4660_, v_a_4606_, v___x_4659_, v___f_4655_);
return v___x_4661_;
}
}
}
}
else
{
lean_object* v___x_4665_; lean_object* v___x_4666_; 
lean_dec(v___x_4645_);
lean_dec(v_pos_4644_);
lean_dec(v_nextId_4642_);
lean_dec(v_receivers_4641_);
lean_dec(v_read_4640_);
lean_dec(v_write_4639_);
lean_dec_ref(v_buffer_4638_);
lean_dec(v_size_4637_);
lean_dec(v_capacity_4636_);
lean_dec_ref(v_waiters_4635_);
lean_dec_ref(v___f_4629_);
lean_del_object(v___x_4623_);
v___x_4665_ = lean_box(0);
v___x_4666_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4606_, v___f_4627_, v___x_4665_, v___x_4633_, v_a_4608_);
return v___x_4666_;
}
}
}
else
{
lean_object* v___x_4667_; 
lean_dec(v_fst_4625_);
lean_del_object(v___x_4623_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4607_);
v___x_4667_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v___x_4672_, lean_object* v_x_4673_, lean_object* v___y_4674_){
_start:
{
uint8_t v_a_12381__boxed_4675_; uint8_t v___x_12383__boxed_4676_; lean_object* v_res_4677_; 
v_a_12381__boxed_4675_ = lean_unbox(v_a_4669_);
v___x_12383__boxed_4676_ = lean_unbox(v___x_4672_);
v_res_4677_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12381__boxed_4675_, v_a_4670_, v_a_4671_, v___x_12383__boxed_4676_, v_x_4673_);
lean_dec(v_a_4671_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4678_, lean_object* v_next_4679_, lean_object* v_a_4680_, lean_object* v_x_4681_){
_start:
{
if (lean_obj_tag(v_x_4681_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4691_; 
lean_dec(v_next_4679_);
lean_dec_ref(v_a_4678_);
v_a_4683_ = lean_ctor_get(v_x_4681_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v_x_4681_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4685_ = v_x_4681_;
v_isShared_4686_ = v_isSharedCheck_4691_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v_x_4681_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4691_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4689_; 
v___x_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
return v___x_4689_;
}
}
}
else
{
lean_object* v_a_4692_; uint8_t v___x_4693_; 
v_a_4692_ = lean_ctor_get(v_x_4681_, 0);
lean_inc(v_a_4692_);
lean_dec_ref_known(v_x_4681_, 1);
v___x_4693_ = lean_unbox(v_a_4692_);
if (v___x_4693_ == 0)
{
lean_object* v_capacity_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; uint8_t v___x_4697_; lean_object* v___x_4698_; lean_object* v___f_4699_; lean_object* v___f_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___x_4703_; 
v_capacity_4694_ = lean_ctor_get(v_a_4678_, 2);
v___x_4695_ = lean_nat_mod(v_next_4679_, v_capacity_4694_);
v___x_4696_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4695_, v_a_4680_);
v___x_4697_ = 1;
v___x_4698_ = lean_box(v___x_4697_);
lean_inc(v_a_4680_);
lean_inc_n(v_a_4692_, 2);
v___f_4699_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4699_, 0, v_a_4692_);
lean_closure_set(v___f_4699_, 1, v_a_4678_);
lean_closure_set(v___f_4699_, 2, v_a_4680_);
lean_closure_set(v___f_4699_, 3, v___x_4698_);
v___f_4700_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4700_, 0, v_next_4679_);
lean_closure_set(v___f_4700_, 1, v_a_4692_);
lean_closure_set(v___f_4700_, 2, v___f_4699_);
v___x_4701_ = lean_unsigned_to_nat(0u);
v___x_4702_ = lean_unbox(v_a_4692_);
lean_dec(v_a_4692_);
v___x_4703_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4701_, v___x_4702_, v___x_4696_, v___f_4700_);
return v___x_4703_;
}
else
{
lean_object* v___x_4704_; 
lean_dec(v_a_4692_);
lean_dec(v_next_4679_);
lean_dec_ref(v_a_4678_);
v___x_4704_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4704_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4705_, lean_object* v_next_4706_, lean_object* v_a_4707_, lean_object* v_x_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4705_, v_next_4706_, v_a_4707_, v_x_4708_);
lean_dec(v_a_4707_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4711_, lean_object* v_next_4712_, lean_object* v_x_4713_){
_start:
{
if (lean_obj_tag(v_x_4713_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4723_; 
lean_dec(v_next_4712_);
v_a_4715_ = lean_ctor_get(v_x_4713_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v_x_4713_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4717_ = v_x_4713_;
v_isShared_4718_ = v_isSharedCheck_4723_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v_x_4713_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4723_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4720_; 
if (v_isShared_4718_ == 0)
{
v___x_4720_ = v___x_4717_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4715_);
v___x_4720_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4721_; 
v___x_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
return v___x_4721_;
}
}
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4725_; lean_object* v___f_4726_; lean_object* v___x_4727_; uint8_t v___x_4728_; lean_object* v___x_4729_; 
v_a_4724_ = lean_ctor_get(v_x_4713_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v_x_4713_, 1);
v___x_4725_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4711_);
lean_inc(v_a_4711_);
v___f_4726_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4726_, 0, v_a_4724_);
lean_closure_set(v___f_4726_, 1, v_next_4712_);
lean_closure_set(v___f_4726_, 2, v_a_4711_);
v___x_4727_ = lean_unsigned_to_nat(0u);
v___x_4728_ = 0;
v___x_4729_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4727_, v___x_4728_, v___x_4725_, v___f_4726_);
return v___x_4729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4730_, lean_object* v_next_4731_, lean_object* v_x_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4730_, v_next_4731_, v_x_4732_);
lean_dec(v_a_4730_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4735_, lean_object* v_a_4736_){
_start:
{
lean_object* v___x_4738_; lean_object* v___f_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; lean_object* v___x_4744_; 
v___x_4738_ = lean_st_ref_get(v_a_4736_);
lean_inc(v_a_4736_);
v___f_4739_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4739_, 0, v_a_4736_);
lean_closure_set(v___f_4739_, 1, v_next_4735_);
v___x_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4738_);
v___x_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
v___x_4742_ = lean_unsigned_to_nat(0u);
v___x_4743_ = 0;
v___x_4744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4742_, v___x_4743_, v___x_4741_, v___f_4739_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4745_, lean_object* v_a_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v_res_4748_; 
v_res_4748_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4745_, v_a_4746_);
lean_dec(v_a_4746_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4749_, lean_object* v_a_4750_, lean_object* v_x_4751_){
_start:
{
if (lean_obj_tag(v_x_4751_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4761_; 
lean_dec(v_receiverId_4749_);
v_a_4753_ = lean_ctor_get(v_x_4751_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_x_4751_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4755_ = v_x_4751_;
v_isShared_4756_ = v_isSharedCheck_4761_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v_x_4751_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4761_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4759_; 
v___x_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4758_);
return v___x_4759_;
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v_receivers_4763_; lean_object* v___x_4764_; 
v_a_4762_ = lean_ctor_get(v_x_4751_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v_x_4751_, 1);
v_receivers_4763_ = lean_ctor_get(v_a_4762_, 7);
lean_inc(v_receivers_4763_);
lean_dec(v_a_4762_);
v___x_4764_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4763_, v_receiverId_4749_);
if (lean_obj_tag(v___x_4764_) == 1)
{
lean_object* v_val_4765_; lean_object* v___x_4766_; lean_object* v___f_4767_; lean_object* v___x_4768_; uint8_t v___x_4769_; lean_object* v___x_4770_; 
v_val_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_val_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4766_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4765_, v_a_4750_);
lean_inc(v_a_4750_);
v___f_4767_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4767_, 0, v_a_4750_);
lean_closure_set(v___f_4767_, 1, v_receiverId_4749_);
lean_closure_set(v___f_4767_, 2, v_receivers_4763_);
v___x_4768_ = lean_unsigned_to_nat(0u);
v___x_4769_ = 0;
v___x_4770_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4768_, v___x_4769_, v___x_4766_, v___f_4767_);
return v___x_4770_;
}
else
{
lean_object* v___x_4771_; 
lean_dec(v___x_4764_);
lean_dec(v_receivers_4763_);
lean_dec(v_receiverId_4749_);
v___x_4771_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__2));
return v___x_4771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4772_, lean_object* v_a_4773_, lean_object* v_x_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4772_, v_a_4773_, v_x_4774_);
lean_dec(v_a_4773_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4777_, lean_object* v_a_4778_){
_start:
{
lean_object* v___x_4780_; lean_object* v___f_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; uint8_t v___x_4785_; lean_object* v___x_4786_; 
v___x_4780_ = lean_st_ref_get(v_a_4778_);
lean_inc(v_a_4778_);
v___f_4781_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4781_, 0, v_receiverId_4777_);
lean_closure_set(v___f_4781_, 1, v_a_4778_);
v___x_4782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4780_);
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
v___x_4784_ = lean_unsigned_to_nat(0u);
v___x_4785_ = 0;
v___x_4786_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4784_, v___x_4785_, v___x_4783_, v___f_4781_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4787_, lean_object* v_a_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4787_, v_a_4788_);
lean_dec(v_a_4788_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4795_, lean_object* v___y_4796_, lean_object* v___f_4797_, lean_object* v_x_4798_){
_start:
{
if (lean_obj_tag(v_x_4798_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4808_; 
lean_dec_ref(v___f_4797_);
lean_dec(v_id_4795_);
v_a_4800_ = lean_ctor_get(v_x_4798_, 0);
v_isSharedCheck_4808_ = !lean_is_exclusive(v_x_4798_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4802_ = v_x_4798_;
v_isShared_4803_ = v_isSharedCheck_4808_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v_x_4798_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4808_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
lean_object* v___x_4806_; 
v___x_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
return v___x_4806_;
}
}
}
else
{
lean_object* v_a_4809_; uint8_t v___x_4810_; 
v_a_4809_ = lean_ctor_get(v_x_4798_, 0);
lean_inc(v_a_4809_);
lean_dec_ref_known(v_x_4798_, 1);
v___x_4810_ = lean_unbox(v_a_4809_);
lean_dec(v_a_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; 
lean_dec_ref(v___f_4797_);
lean_dec(v_id_4795_);
v___x_4811_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___closed__1));
return v___x_4811_;
}
else
{
lean_object* v___x_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; lean_object* v___x_4815_; 
v___x_4812_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4795_, v___y_4796_);
v___x_4813_ = lean_unsigned_to_nat(0u);
v___x_4814_ = 0;
v___x_4815_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4813_, v___x_4814_, v___x_4812_, v___f_4797_);
return v___x_4815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4816_, lean_object* v___y_4817_, lean_object* v___f_4818_, lean_object* v_x_4819_, lean_object* v___y_4820_){
_start:
{
lean_object* v_res_4821_; 
v_res_4821_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4816_, v___y_4817_, v___f_4818_, v_x_4819_);
lean_dec(v___y_4817_);
return v_res_4821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4822_, lean_object* v___f_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v___x_4826_; lean_object* v___f_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; uint8_t v___x_4831_; lean_object* v___x_4832_; lean_object* v___f_4833_; lean_object* v___x_4834_; 
v___x_4826_ = lean_st_ref_get(v___y_4824_);
lean_inc_n(v___y_4824_, 2);
lean_inc(v_id_4822_);
v___f_4827_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_4827_, 0, v_id_4822_);
lean_closure_set(v___f_4827_, 1, v___y_4824_);
v___x_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = 0;
v___x_4832_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4830_, v___x_4831_, v___x_4829_, v___f_4827_);
v___f_4833_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4833_, 0, v_id_4822_);
lean_closure_set(v___f_4833_, 1, v___y_4824_);
lean_closure_set(v___f_4833_, 2, v___f_4823_);
v___x_4834_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4830_, v___x_4831_, v___x_4832_, v___f_4833_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4835_, lean_object* v___f_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4835_, v___f_4836_, v___y_4837_);
lean_dec(v___y_4837_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4842_){
_start:
{
lean_object* v_state_4843_; lean_object* v_id_4844_; lean_object* v___f_4845_; lean_object* v___f_4846_; lean_object* v___f_4847_; lean_object* v___f_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; 
v_state_4843_ = lean_ctor_get(v_ch_4842_, 0);
lean_inc_ref_n(v_state_4843_, 2);
v_id_4844_ = lean_ctor_get(v_ch_4842_, 1);
lean_inc(v_id_4844_);
v___f_4845_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4846_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4846_, 0, v_ch_4842_);
v___f_4847_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4848_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4848_, 0, v_id_4844_);
lean_closure_set(v___f_4848_, 1, v___f_4847_);
v___x_4849_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4849_, 0, lean_box(0));
lean_closure_set(v___x_4849_, 1, lean_box(0));
lean_closure_set(v___x_4849_, 2, v_state_4843_);
lean_closure_set(v___x_4849_, 3, v___f_4848_);
v___x_4850_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4850_, 0, lean_box(0));
lean_closure_set(v___x_4850_, 1, lean_box(0));
lean_closure_set(v___x_4850_, 2, v_state_4843_);
lean_closure_set(v___x_4850_, 3, v___f_4845_);
v___x_4851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4849_);
lean_ctor_set(v___x_4851_, 1, v___f_4846_);
lean_ctor_set(v___x_4851_, 2, v___x_4850_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4852_, lean_object* v_ch_4853_){
_start:
{
lean_object* v___x_4854_; 
v___x_4854_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4853_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4855_, lean_object* v_receiverId_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4856_, v_a_4857_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4860_, lean_object* v_receiverId_4861_, lean_object* v_a_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4860_, v_receiverId_4861_, v_a_4862_);
lean_dec(v_a_4862_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4865_, lean_object* v_q_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4866_, v___y_4867_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4870_, lean_object* v_q_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4870_, v_q_4871_, v___y_4872_);
lean_dec(v___y_4872_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4875_, lean_object* v_slot_4876_, lean_object* v_next_4877_, lean_object* v_a_4878_){
_start:
{
lean_object* v___x_4880_; 
v___x_4880_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4876_, v_next_4877_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4881_, lean_object* v_slot_4882_, lean_object* v_next_4883_, lean_object* v_a_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4881_, v_slot_4882_, v_next_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec(v_next_4883_);
lean_dec(v_slot_4882_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4887_, lean_object* v_a_4888_){
_start:
{
lean_object* v___x_4890_; 
v___x_4890_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4888_);
return v___x_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4891_, lean_object* v_a_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4891_, v_a_4892_);
lean_dec(v_a_4892_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4895_, lean_object* v_next_4896_, lean_object* v_a_4897_){
_start:
{
lean_object* v___x_4899_; 
v___x_4899_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4896_, v_a_4897_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4900_, lean_object* v_next_4901_, lean_object* v_a_4902_, lean_object* v___y_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4900_, v_next_4901_, v_a_4902_);
lean_dec(v_a_4902_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4905_, lean_object* v_x_4906_, lean_object* v_x_4907_, lean_object* v___y_4908_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4906_, v_x_4907_);
return v___x_4910_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4911_, lean_object* v_x_4912_, lean_object* v_x_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4911_, v_x_4912_, v_x_4913_, v___y_4914_);
lean_dec(v___y_4914_);
return v_res_4916_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4918_){
_start:
{
lean_object* v___x_4920_; 
v___x_4920_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4918_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4921_, lean_object* v_a_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l_Std_Broadcast_new___redArg(v_capacity_4921_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4924_, lean_object* v_capacity_4925_, lean_object* v_h_4926_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4925_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4929_, lean_object* v_capacity_4930_, lean_object* v_h_4931_, lean_object* v_a_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Std_Broadcast_new(v_00_u03b1_4929_, v_capacity_4930_, v_h_4931_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4934_, lean_object* v_v_4935_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4934_, v_v_4935_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4938_, lean_object* v_v_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Std_Broadcast_trySend___redArg(v_ch_4938_, v_v_4939_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4942_, lean_object* v_ch_4943_, lean_object* v_v_4944_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4943_, v_v_4944_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4947_, lean_object* v_ch_4948_, lean_object* v_v_4949_, lean_object* v_a_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l_Std_Broadcast_trySend(v_00_u03b1_4947_, v_ch_4948_, v_v_4949_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4952_){
_start:
{
lean_object* v___x_4954_; 
v___x_4954_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4952_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4962_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4962_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4962_ == 0)
{
v___x_4957_ = v___x_4954_;
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v___x_4954_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4962_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___x_4960_; 
if (v_isShared_4958_ == 0)
{
v___x_4960_ = v___x_4957_;
goto v_reusejp_4959_;
}
else
{
lean_object* v_reuseFailAlloc_4961_; 
v_reuseFailAlloc_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_a_4955_);
v___x_4960_ = v_reuseFailAlloc_4961_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
return v___x_4960_;
}
}
}
else
{
lean_object* v_a_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4970_; 
v_a_4963_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4970_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4965_ = v___x_4954_;
v_isShared_4966_ = v_isSharedCheck_4970_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_a_4963_);
lean_dec(v___x_4954_);
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
v_reuseFailAlloc_4969_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_4971_, lean_object* v_a_4972_){
_start:
{
lean_object* v_res_4973_; 
v_res_4973_ = l_Std_Broadcast_subscribe___redArg(v_ch_4971_);
return v_res_4973_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_4974_, lean_object* v_ch_4975_){
_start:
{
lean_object* v___x_4977_; 
v___x_4977_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4975_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4977_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4977_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
else
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4993_; 
v_a_4986_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4988_ = v___x_4977_;
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4977_);
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
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_4994_, lean_object* v_ch_4995_, lean_object* v_a_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_Std_Broadcast_subscribe(v_00_u03b1_4994_, v_ch_4995_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_4998_){
_start:
{
lean_object* v___x_5000_; 
v___x_5000_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_4998_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v___x_5000_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___x_5000_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5026_; 
v_a_5009_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5011_ = v___x_5000_;
v_isShared_5012_ = v_isSharedCheck_5026_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_5000_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5026_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
uint8_t v___x_5013_; 
v___x_5013_ = lean_unbox(v_a_5009_);
lean_dec(v_a_5009_);
switch(v___x_5013_)
{
case 0:
{
lean_object* v___x_5014_; lean_object* v___x_5016_; 
v___x_5014_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 0, v___x_5014_);
v___x_5016_ = v___x_5011_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_5014_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
case 1:
{
lean_object* v___x_5018_; lean_object* v___x_5020_; 
v___x_5018_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 0, v___x_5018_);
v___x_5020_ = v___x_5011_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
default: 
{
lean_object* v___x_5022_; lean_object* v___x_5024_; 
v___x_5022_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 0, v___x_5022_);
v___x_5024_ = v___x_5011_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5027_, lean_object* v_a_5028_){
_start:
{
lean_object* v_res_5029_; 
v_res_5029_ = l_Std_Broadcast_close___redArg(v_ch_5027_);
return v_res_5029_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5030_, lean_object* v_ch_5031_){
_start:
{
lean_object* v___x_5033_; 
v___x_5033_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5031_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_5033_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_5033_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
else
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5059_; 
v_a_5042_ = lean_ctor_get(v___x_5033_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5033_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5044_ = v___x_5033_;
v_isShared_5045_ = v_isSharedCheck_5059_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5033_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5059_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
uint8_t v___x_5046_; 
v___x_5046_ = lean_unbox(v_a_5042_);
lean_dec(v_a_5042_);
switch(v___x_5046_)
{
case 0:
{
lean_object* v___x_5047_; lean_object* v___x_5049_; 
v___x_5047_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5045_ == 0)
{
lean_ctor_set(v___x_5044_, 0, v___x_5047_);
v___x_5049_ = v___x_5044_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5047_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
case 1:
{
lean_object* v___x_5051_; lean_object* v___x_5053_; 
v___x_5051_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5045_ == 0)
{
lean_ctor_set(v___x_5044_, 0, v___x_5051_);
v___x_5053_ = v___x_5044_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5051_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
default: 
{
lean_object* v___x_5055_; lean_object* v___x_5057_; 
v___x_5055_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5045_ == 0)
{
lean_ctor_set(v___x_5044_, 0, v___x_5055_);
v___x_5057_ = v___x_5044_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5055_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5060_, lean_object* v_ch_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l_Std_Broadcast_close(v_00_u03b1_5060_, v_ch_5061_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5064_){
_start:
{
lean_object* v___y_5067_; 
if (lean_obj_tag(v_x_5064_) == 0)
{
lean_object* v_a_5071_; uint8_t v___x_5072_; 
v_a_5071_ = lean_ctor_get(v_x_5064_, 0);
lean_inc(v_a_5071_);
lean_dec_ref_known(v_x_5064_, 1);
v___x_5072_ = lean_unbox(v_a_5071_);
lean_dec(v_a_5071_);
switch(v___x_5072_)
{
case 0:
{
lean_object* v___x_5073_; 
v___x_5073_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5067_ = v___x_5073_;
goto v___jp_5066_;
}
case 1:
{
lean_object* v___x_5074_; 
v___x_5074_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5067_ = v___x_5074_;
goto v___jp_5066_;
}
default: 
{
lean_object* v___x_5075_; 
v___x_5075_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5067_ = v___x_5075_;
goto v___jp_5066_;
}
}
}
else
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5084_; 
v_a_5076_ = lean_ctor_get(v_x_5064_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v_x_5064_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5078_ = v_x_5064_;
v_isShared_5079_ = v_isSharedCheck_5084_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v_x_5064_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5084_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
lean_object* v___x_5082_; 
v___x_5082_ = lean_task_pure(v___x_5081_);
return v___x_5082_;
}
}
}
v___jp_5066_:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
lean_inc_ref(v___y_5067_);
v___x_5068_ = lean_mk_io_user_error(v___y_5067_);
v___x_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5068_);
v___x_5070_ = lean_task_pure(v___x_5069_);
return v___x_5070_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5085_, lean_object* v___y_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5085_);
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5089_, lean_object* v_v_5090_){
_start:
{
lean_object* v___x_5092_; lean_object* v___f_5093_; lean_object* v___x_5094_; uint8_t v___x_5095_; lean_object* v___x_5096_; 
v___x_5092_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5089_, v_v_5090_);
v___f_5093_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5094_ = lean_unsigned_to_nat(0u);
v___x_5095_ = 1;
v___x_5096_ = lean_io_bind_task(v___x_5092_, v___f_5093_, v___x_5094_, v___x_5095_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5097_, lean_object* v_v_5098_, lean_object* v_a_5099_){
_start:
{
lean_object* v_res_5100_; 
v_res_5100_ = l_Std_Broadcast_send___redArg(v_ch_5097_, v_v_5098_);
return v_res_5100_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5101_, lean_object* v_ch_5102_, lean_object* v_v_5103_){
_start:
{
lean_object* v___x_5105_; lean_object* v___f_5106_; lean_object* v___x_5107_; uint8_t v___x_5108_; lean_object* v___x_5109_; 
v___x_5105_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5102_, v_v_5103_);
v___f_5106_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5107_ = lean_unsigned_to_nat(0u);
v___x_5108_ = 1;
v___x_5109_ = lean_io_bind_task(v___x_5105_, v___f_5106_, v___x_5107_, v___x_5108_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5110_, lean_object* v_ch_5111_, lean_object* v_v_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Std_Broadcast_send(v_00_u03b1_5110_, v_ch_5111_, v_v_5112_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5115_){
_start:
{
lean_object* v___x_5117_; 
v___x_5117_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5115_);
return v___x_5117_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5118_, lean_object* v_a_5119_){
_start:
{
lean_object* v_res_5120_; 
v_res_5120_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5118_);
return v_res_5120_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5121_, lean_object* v_ch_5122_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5122_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5125_, lean_object* v_ch_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5125_, v_ch_5126_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5129_){
_start:
{
lean_object* v___x_5131_; 
v___x_5131_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5129_);
return v___x_5131_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5132_, lean_object* v_a_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5132_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5135_, lean_object* v_inst_5136_, lean_object* v_ch_5137_){
_start:
{
lean_object* v___x_5139_; 
v___x_5139_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5137_);
return v___x_5139_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5140_, lean_object* v_inst_5141_, lean_object* v_ch_5142_, lean_object* v_a_5143_){
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5140_, v_inst_5141_, v_ch_5142_);
lean_dec(v_inst_5141_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5145_){
_start:
{
lean_object* v___x_5146_; 
v___x_5146_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5145_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5147_, lean_object* v_inst_5148_, lean_object* v_ch_5149_){
_start:
{
lean_object* v___x_5150_; 
v___x_5150_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5149_);
return v___x_5150_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5151_, lean_object* v_inst_5152_, lean_object* v_ch_5153_){
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5151_, v_inst_5152_, v_ch_5153_);
lean_dec(v_inst_5152_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5155_){
_start:
{
lean_object* v___x_5157_; 
v___x_5157_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5155_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5158_, lean_object* v_a_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5158_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5161_, lean_object* v_ch_5162_){
_start:
{
lean_object* v___x_5164_; 
v___x_5164_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5162_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5165_, lean_object* v_ch_5166_, lean_object* v_a_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5165_, v_ch_5166_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5169_, lean_object* v_ch_5170_, lean_object* v_prio_5171_){
_start:
{
lean_object* v___x_5173_; 
v___x_5173_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5169_, v_ch_5170_, v_prio_5171_);
return v___x_5173_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5174_, lean_object* v_ch_5175_, lean_object* v_prio_5176_, lean_object* v_a_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5174_, v_ch_5175_, v_prio_5176_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5179_, lean_object* v_f_5180_, lean_object* v_ch_5181_, lean_object* v_prio_5182_){
_start:
{
lean_object* v___x_5184_; 
v___x_5184_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5180_, v_ch_5181_, v_prio_5182_);
return v___x_5184_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5185_, lean_object* v_f_5186_, lean_object* v_ch_5187_, lean_object* v_prio_5188_, lean_object* v_a_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5185_, v_f_5186_, v_ch_5187_, v_prio_5188_);
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5196_, lean_object* v_inst_5197_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__2));
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5199_, lean_object* v_inst_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5199_, v_inst_5200_);
lean_dec(v_inst_5200_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__0(lean_object* v_a_5202_){
_start:
{
lean_object* v___x_5203_; 
v___x_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5203_, 0, v_a_5202_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(lean_object* v___f_5204_, lean_object* v_x_5205_){
_start:
{
if (lean_obj_tag(v_x_5205_) == 0)
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5215_; 
lean_dec_ref(v___f_5204_);
v_a_5207_ = lean_ctor_get(v_x_5205_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v_x_5205_);
if (v_isSharedCheck_5215_ == 0)
{
v___x_5209_ = v_x_5205_;
v_isShared_5210_ = v_isSharedCheck_5215_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v_x_5205_);
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
lean_object* v_a_5216_; 
v_a_5216_ = lean_ctor_get(v_x_5205_, 0);
lean_inc(v_a_5216_);
lean_dec_ref_known(v_x_5205_, 1);
if (lean_obj_tag(v_a_5216_) == 0)
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5225_; 
lean_dec_ref(v___f_5204_);
v_a_5217_ = lean_ctor_get(v_a_5216_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v_a_5216_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5219_ = v_a_5216_;
v_isShared_5220_ = v_isSharedCheck_5225_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v_a_5216_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5225_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5222_; 
if (v_isShared_5220_ == 0)
{
v___x_5222_ = v___x_5219_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5217_);
v___x_5222_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5223_; 
v___x_5223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5223_, 0, v___x_5222_);
return v___x_5223_;
}
}
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5227_; uint8_t v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; 
v_a_5226_ = lean_ctor_get(v_a_5216_, 0);
lean_inc(v_a_5226_);
lean_dec_ref_known(v_a_5216_, 1);
v___x_5227_ = lean_unsigned_to_nat(0u);
v___x_5228_ = 0;
v___x_5229_ = lean_task_map(v___f_5204_, v_a_5226_, v___x_5227_, v___x_5228_);
v___x_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5229_);
return v___x_5230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1___boxed(lean_object* v___f_5231_, lean_object* v_x_5232_, lean_object* v___y_5233_){
_start:
{
lean_object* v_res_5234_; 
v_res_5234_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__1(v___f_5231_, v_x_5232_);
return v_res_5234_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(lean_object* v___f_5235_, lean_object* v_receiver_5236_){
_start:
{
lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; uint8_t v___x_5243_; lean_object* v___x_5244_; 
v___x_5238_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5236_);
v___x_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5238_);
v___x_5240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5240_, 0, v___x_5239_);
v___x_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5240_);
v___x_5242_ = lean_unsigned_to_nat(0u);
v___x_5243_ = 0;
v___x_5244_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5242_, v___x_5243_, v___x_5241_, v___f_5235_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2___boxed(lean_object* v___f_5245_, lean_object* v_receiver_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v_res_5248_; 
v_res_5248_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___lam__2(v___f_5245_, v_receiver_5246_);
return v_res_5248_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5254_, lean_object* v_inst_5255_){
_start:
{
lean_object* v___f_5256_; 
v___f_5256_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__2));
return v___f_5256_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5257_, lean_object* v_inst_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5257_, v_inst_5258_);
lean_dec(v_inst_5258_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__1(lean_object* v_a_5260_){
_start:
{
lean_object* v___x_5261_; 
v___x_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5261_, 0, v_a_5260_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(lean_object* v___f_5266_, lean_object* v_x_5267_){
_start:
{
if (lean_obj_tag(v_x_5267_) == 0)
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5277_; 
lean_dec_ref(v___f_5266_);
v_a_5269_ = lean_ctor_get(v_x_5267_, 0);
v_isSharedCheck_5277_ = !lean_is_exclusive(v_x_5267_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5271_ = v_x_5267_;
v_isShared_5272_ = v_isSharedCheck_5277_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v_x_5267_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5277_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
lean_object* v___x_5275_; 
v___x_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5274_);
return v___x_5275_;
}
}
}
else
{
lean_object* v_a_5278_; lean_object* v___x_5279_; uint8_t v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v_a_5278_ = lean_ctor_get(v_x_5267_, 0);
lean_inc(v_a_5278_);
lean_dec_ref_known(v_x_5267_, 1);
v___x_5279_ = lean_unsigned_to_nat(0u);
v___x_5280_ = 0;
v___x_5281_ = lean_task_map(v___f_5266_, v_a_5278_, v___x_5279_, v___x_5280_);
v___x_5282_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___closed__1));
v___x_5283_ = lean_task_map(v___x_5282_, v___x_5281_, v___x_5279_, v___x_5280_);
v___x_5284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5284_, 0, v___x_5283_);
return v___x_5284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0___boxed(lean_object* v___f_5285_, lean_object* v_x_5286_, lean_object* v___y_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__0(v___f_5285_, v_x_5286_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(lean_object* v___f_5289_, lean_object* v___f_5290_, lean_object* v_receiver_5291_, lean_object* v_x_5292_){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; uint8_t v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; uint8_t v___x_5300_; lean_object* v___x_5301_; 
v___x_5294_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5291_, v_x_5292_);
v___x_5295_ = lean_unsigned_to_nat(0u);
v___x_5296_ = 1;
v___x_5297_ = lean_io_bind_task(v___x_5294_, v___f_5289_, v___x_5295_, v___x_5296_);
v___x_5298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5297_);
v___x_5299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5299_, 0, v___x_5298_);
v___x_5300_ = 0;
v___x_5301_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5295_, v___x_5300_, v___x_5299_, v___f_5290_);
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2___boxed(lean_object* v___f_5302_, lean_object* v___f_5303_, lean_object* v_receiver_5304_, lean_object* v_x_5305_, lean_object* v___y_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__2(v___f_5302_, v___f_5303_, v_receiver_5304_, v_x_5305_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(lean_object* v_x_5308_){
_start:
{
lean_object* v___x_5310_; 
v___x_5310_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3___boxed(lean_object* v_x_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v_res_5313_; 
v_res_5313_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__3(v_x_5311_);
lean_dec_ref(v_x_5311_);
return v_res_5313_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(lean_object* v___f_5314_, lean_object* v_socket_5315_, lean_object* v_x_5316_, lean_object* v___y_5317_){
_start:
{
lean_object* v___x_5319_; 
v___x_5319_ = lean_apply_3(v___f_5314_, v_socket_5315_, v___y_5317_, lean_box(0));
return v___x_5319_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed(lean_object* v___f_5320_, lean_object* v_socket_5321_, lean_object* v_x_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4(v___f_5320_, v_socket_5321_, v_x_5322_, v___y_5323_);
return v_res_5325_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(lean_object* v___f_5326_, lean_object* v___x_5327_, lean_object* v_socket_5328_, lean_object* v_data_5329_){
_start:
{
lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; uint8_t v___x_5334_; 
v___x_5331_ = lean_unsigned_to_nat(0u);
v___x_5332_ = lean_array_get_size(v_data_5329_);
v___x_5333_ = lean_box(0);
v___x_5334_ = lean_nat_dec_lt(v___x_5331_, v___x_5332_);
if (v___x_5334_ == 0)
{
lean_object* v___x_5335_; 
lean_dec_ref(v_data_5329_);
lean_dec_ref(v_socket_5328_);
lean_dec_ref(v___x_5327_);
lean_dec_ref(v___f_5326_);
v___x_5335_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5335_;
}
else
{
lean_object* v___f_5336_; uint8_t v___x_5337_; 
v___f_5336_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5336_, 0, v___f_5326_);
lean_closure_set(v___f_5336_, 1, v_socket_5328_);
v___x_5337_ = lean_nat_dec_le(v___x_5332_, v___x_5332_);
if (v___x_5337_ == 0)
{
if (v___x_5334_ == 0)
{
lean_object* v___x_5338_; 
lean_dec_ref(v___f_5336_);
lean_dec_ref(v_data_5329_);
lean_dec_ref(v___x_5327_);
v___x_5338_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__1));
return v___x_5338_;
}
else
{
size_t v___x_5339_; size_t v___x_5340_; lean_object* v___x_899__overap_5341_; lean_object* v___x_5342_; 
v___x_5339_ = ((size_t)0ULL);
v___x_5340_ = lean_usize_of_nat(v___x_5332_);
v___x_899__overap_5341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5327_, v___f_5336_, v_data_5329_, v___x_5339_, v___x_5340_, v___x_5333_);
v___x_5342_ = lean_apply_1(v___x_899__overap_5341_, lean_box(0));
return v___x_5342_;
}
}
else
{
size_t v___x_5343_; size_t v___x_5344_; lean_object* v___x_902__overap_5345_; lean_object* v___x_5346_; 
v___x_5343_ = ((size_t)0ULL);
v___x_5344_ = lean_usize_of_nat(v___x_5332_);
v___x_902__overap_5345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5327_, v___f_5336_, v_data_5329_, v___x_5343_, v___x_5344_, v___x_5333_);
v___x_5346_ = lean_apply_1(v___x_902__overap_5345_, lean_box(0));
return v___x_5346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed(lean_object* v___f_5347_, lean_object* v___x_5348_, lean_object* v_socket_5349_, lean_object* v_data_5350_, lean_object* v___y_5351_){
_start:
{
lean_object* v_res_5352_; 
v_res_5352_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5(v___f_5347_, v___x_5348_, v_socket_5349_, v_data_5350_);
return v_res_5352_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4(void){
_start:
{
lean_object* v___x_5360_; 
v___x_5360_ = l_Std_Async_EAsync_instMonad(lean_box(0));
return v___x_5360_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5(void){
_start:
{
lean_object* v___x_5361_; lean_object* v___f_5362_; lean_object* v___f_5363_; 
v___x_5361_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__4);
v___f_5362_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___f_5363_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___lam__5___boxed), 5, 2);
lean_closure_set(v___f_5363_, 0, v___f_5362_);
lean_closure_set(v___f_5363_, 1, v___x_5361_);
return v___f_5363_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6(void){
_start:
{
lean_object* v___f_5364_; lean_object* v___f_5365_; lean_object* v___f_5366_; lean_object* v___x_5367_; 
v___f_5364_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__3));
v___f_5365_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__5);
v___f_5366_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__2));
v___x_5367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5367_, 0, v___f_5366_);
lean_ctor_set(v___x_5367_, 1, v___f_5365_);
lean_ctor_set(v___x_5367_, 2, v___f_5364_);
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5368_, lean_object* v_inst_5369_){
_start:
{
lean_object* v___x_5370_; 
v___x_5370_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__6);
return v___x_5370_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5371_, lean_object* v_inst_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5371_, v_inst_5372_);
lean_dec(v_inst_5372_);
return v_res_5373_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5374_; 
v___x_5374_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5374_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5375_){
_start:
{
lean_object* v___x_5377_; 
v___x_5377_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5375_);
return v___x_5377_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5378_, lean_object* v_a_5379_){
_start:
{
lean_object* v_res_5380_; 
v_res_5380_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5378_);
return v_res_5380_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5381_, lean_object* v_capacity_5382_, lean_object* v_h_5383_){
_start:
{
lean_object* v___x_5385_; 
v___x_5385_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5382_);
return v___x_5385_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5386_, lean_object* v_capacity_5387_, lean_object* v_h_5388_, lean_object* v_a_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5386_, v_capacity_5387_, v_h_5388_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5391_, lean_object* v_v_5392_){
_start:
{
lean_object* v___x_5394_; 
v___x_5394_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5391_, v_v_5392_);
return v___x_5394_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5395_, lean_object* v_v_5396_, lean_object* v_a_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5395_, v_v_5396_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5399_, lean_object* v_ch_5400_, lean_object* v_v_5401_){
_start:
{
lean_object* v___x_5403_; 
v___x_5403_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5400_, v_v_5401_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5404_, lean_object* v_ch_5405_, lean_object* v_v_5406_, lean_object* v_a_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5404_, v_ch_5405_, v_v_5406_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5410_, lean_object* v_v_5411_){
_start:
{
lean_object* v___x_5413_; lean_object* v___f_5414_; lean_object* v___x_5415_; uint8_t v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5413_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5410_, v_v_5411_);
v___f_5414_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5415_ = lean_unsigned_to_nat(0u);
v___x_5416_ = 1;
v___x_5417_ = lean_io_bind_task(v___x_5413_, v___f_5414_, v___x_5415_, v___x_5416_);
v___x_5418_ = lean_io_wait(v___x_5417_);
v___x_5419_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5420_ = l_IO_ofExcept___redArg(v___x_5419_, v___x_5418_);
return v___x_5420_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5421_, lean_object* v_v_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5421_, v_v_5422_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5425_, lean_object* v_ch_5426_, lean_object* v_v_5427_){
_start:
{
lean_object* v___x_5429_; lean_object* v___f_5430_; lean_object* v___x_5431_; uint8_t v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; 
v___x_5429_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5426_, v_v_5427_);
v___f_5430_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5431_ = lean_unsigned_to_nat(0u);
v___x_5432_ = 1;
v___x_5433_ = lean_io_bind_task(v___x_5429_, v___f_5430_, v___x_5431_, v___x_5432_);
v___x_5434_ = lean_io_wait(v___x_5433_);
v___x_5435_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5436_ = l_IO_ofExcept___redArg(v___x_5435_, v___x_5434_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5437_, lean_object* v_ch_5438_, lean_object* v_v_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5437_, v_ch_5438_, v_v_5439_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5442_){
_start:
{
lean_object* v___x_5444_; 
v___x_5444_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5442_);
return v___x_5444_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5445_, lean_object* v_a_5446_){
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5445_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5448_, lean_object* v_ch_5449_){
_start:
{
lean_object* v___x_5451_; 
v___x_5451_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5449_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5452_, lean_object* v_ch_5453_, lean_object* v_a_5454_){
_start:
{
lean_object* v_res_5455_; 
v_res_5455_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5452_, v_ch_5453_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5456_){
_start:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5458_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5456_);
v___x_5459_ = lean_io_wait(v___x_5458_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5460_, lean_object* v_a_5461_){
_start:
{
lean_object* v_res_5462_; 
v_res_5462_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5460_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5463_, lean_object* v_inst_5464_, lean_object* v_ch_5465_){
_start:
{
lean_object* v___x_5467_; 
v___x_5467_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5465_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5468_, lean_object* v_inst_5469_, lean_object* v_ch_5470_, lean_object* v_a_5471_){
_start:
{
lean_object* v_res_5472_; 
v_res_5472_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5468_, v_inst_5469_, v_ch_5470_);
lean_dec(v_inst_5469_);
return v_res_5472_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5473_, lean_object* v_b_5474_, lean_object* v_f_5475_, lean_object* v_toBind_5476_, lean_object* v___f_5477_, lean_object* v_a_5478_){
_start:
{
if (lean_obj_tag(v_a_5478_) == 0)
{
lean_object* v___x_5479_; 
lean_dec(v___f_5477_);
lean_dec(v_toBind_5476_);
lean_dec(v_f_5475_);
v___x_5479_ = lean_apply_2(v_toPure_5473_, lean_box(0), v_b_5474_);
return v___x_5479_;
}
else
{
lean_object* v_val_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; 
lean_dec(v_toPure_5473_);
v_val_5480_ = lean_ctor_get(v_a_5478_, 0);
lean_inc(v_val_5480_);
lean_dec_ref_known(v_a_5478_, 1);
v___x_5481_ = lean_apply_2(v_f_5475_, v_val_5480_, v_b_5474_);
v___x_5482_ = lean_apply_4(v_toBind_5476_, lean_box(0), lean_box(0), v___x_5481_, v___f_5477_);
return v___x_5482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5483_, lean_object* v_inst_5484_, lean_object* v_inst_5485_, lean_object* v_ch_5486_, lean_object* v_f_5487_, lean_object* v_b_5488_){
_start:
{
lean_object* v_toApplicative_5489_; lean_object* v_toBind_5490_; lean_object* v_toPure_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___f_5494_; lean_object* v___f_5495_; lean_object* v___x_5496_; 
v_toApplicative_5489_ = lean_ctor_get(v_inst_5484_, 0);
v_toBind_5490_ = lean_ctor_get(v_inst_5484_, 1);
lean_inc_n(v_toBind_5490_, 2);
v_toPure_5491_ = lean_ctor_get(v_toApplicative_5489_, 1);
lean_inc_n(v_toPure_5491_, 2);
lean_inc_ref(v_ch_5486_);
lean_inc(v_inst_5483_);
v___x_5492_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5492_, 0, lean_box(0));
lean_closure_set(v___x_5492_, 1, v_inst_5483_);
lean_closure_set(v___x_5492_, 2, v_ch_5486_);
lean_inc(v_inst_5485_);
v___x_5493_ = lean_apply_2(v_inst_5485_, lean_box(0), v___x_5492_);
lean_inc(v_f_5487_);
v___f_5494_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5494_, 0, v_toPure_5491_);
lean_closure_set(v___f_5494_, 1, v_inst_5483_);
lean_closure_set(v___f_5494_, 2, v_inst_5484_);
lean_closure_set(v___f_5494_, 3, v_inst_5485_);
lean_closure_set(v___f_5494_, 4, v_ch_5486_);
lean_closure_set(v___f_5494_, 5, v_f_5487_);
v___f_5495_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5495_, 0, v_toPure_5491_);
lean_closure_set(v___f_5495_, 1, v_b_5488_);
lean_closure_set(v___f_5495_, 2, v_f_5487_);
lean_closure_set(v___f_5495_, 3, v_toBind_5490_);
lean_closure_set(v___f_5495_, 4, v___f_5494_);
v___x_5496_ = lean_apply_4(v_toBind_5490_, lean_box(0), lean_box(0), v___x_5493_, v___f_5495_);
return v___x_5496_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5497_, lean_object* v_inst_5498_, lean_object* v_inst_5499_, lean_object* v_inst_5500_, lean_object* v_ch_5501_, lean_object* v_f_5502_, lean_object* v_____do__lift_5503_){
_start:
{
if (lean_obj_tag(v_____do__lift_5503_) == 0)
{
lean_object* v_a_5504_; lean_object* v___x_5505_; 
lean_dec(v_f_5502_);
lean_dec_ref(v_ch_5501_);
lean_dec(v_inst_5500_);
lean_dec_ref(v_inst_5499_);
lean_dec(v_inst_5498_);
v_a_5504_ = lean_ctor_get(v_____do__lift_5503_, 0);
lean_inc(v_a_5504_);
lean_dec_ref_known(v_____do__lift_5503_, 1);
v___x_5505_ = lean_apply_2(v_toPure_5497_, lean_box(0), v_a_5504_);
return v___x_5505_;
}
else
{
lean_object* v_a_5506_; lean_object* v___x_5507_; 
lean_dec(v_toPure_5497_);
v_a_5506_ = lean_ctor_get(v_____do__lift_5503_, 0);
lean_inc(v_a_5506_);
lean_dec_ref_known(v_____do__lift_5503_, 1);
v___x_5507_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5498_, v_inst_5499_, v_inst_5500_, v_ch_5501_, v_f_5502_, v_a_5506_);
return v___x_5507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5508_, lean_object* v_m_5509_, lean_object* v_00_u03b2_5510_, lean_object* v_inst_5511_, lean_object* v_inst_5512_, lean_object* v_inst_5513_, lean_object* v_ch_5514_, lean_object* v_f_5515_, lean_object* v_b_5516_){
_start:
{
lean_object* v___x_5517_; 
v___x_5517_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5511_, v_inst_5512_, v_inst_5513_, v_ch_5514_, v_f_5515_, v_b_5516_);
return v___x_5517_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5518_, lean_object* v_inst_5519_, lean_object* v_inst_5520_, lean_object* v_00_u03b2_5521_, lean_object* v_ch_5522_, lean_object* v_b_5523_, lean_object* v_f_5524_){
_start:
{
lean_object* v___x_5525_; 
v___x_5525_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5518_, v_inst_5519_, v_inst_5520_, v_ch_5522_, v_f_5524_, v_b_5523_);
return v___x_5525_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5526_, lean_object* v_inst_5527_, lean_object* v_inst_5528_){
_start:
{
lean_object* v___f_5529_; 
v___f_5529_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5529_, 0, v_inst_5526_);
lean_closure_set(v___f_5529_, 1, v_inst_5527_);
lean_closure_set(v___f_5529_, 2, v_inst_5528_);
return v___f_5529_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5530_, lean_object* v_m_5531_, lean_object* v_inst_5532_, lean_object* v_inst_5533_, lean_object* v_inst_5534_){
_start:
{
lean_object* v___f_5535_; 
v___f_5535_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5535_, 0, v_inst_5532_);
lean_closure_set(v___f_5535_, 1, v_inst_5533_);
lean_closure_set(v___f_5535_, 2, v_inst_5534_);
return v___f_5535_;
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

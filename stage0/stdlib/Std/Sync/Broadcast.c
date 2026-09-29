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
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Queue_empty___redArg();
lean_object* l_Std_Queue_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_wait(lean_object*);
lean_object* l_IO_ofExcept___redArg(lean_object*, lean_object*);
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
lean_object* l_EIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_instInhabitedSlot_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_instInhabitedSlot_default___redArg___closed__0 = (const lean_object*)&l_Std_instInhabitedSlot_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default___redArg();
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_instInhabitedSlot_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_instInhabitedSlot_default___closed__0;
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg();
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__0_value;
static const lean_ctor_object l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__0_value)}};
static const lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__1_value;
static const lean_ctor_object l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__0_value),((lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__1_value)}};
static const lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__2 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__0_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__1_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__1_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__2 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_const___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__0_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Broadcast_send___redArg___closed__0_value),((lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__0_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2_value;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0;
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
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default___redArg(){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = ((lean_object*)(l_Std_instInhabitedSlot_default___redArg___closed__0));
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default___redArg___boxed(lean_object* v___dummy_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_instInhabitedSlot_default___redArg();
return v_res_230_;
}
}
static lean_object* _init_l_Std_instInhabitedSlot_default___closed__0(void){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Std_instInhabitedSlot_default___redArg();
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default(lean_object* v_00_u03b1_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg(){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg___boxed(lean_object* v___dummy_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg();
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot(lean_object* v_a_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_239_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(9u);
v___x_254_ = lean_nat_to_int(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(7u);
v___x_262_ = lean_nat_to_int(v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(13u);
v___x_267_ = lean_nat_to_int(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0));
v___x_270_ = lean_string_length(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17);
v___x_272_ = lean_nat_to_int(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(lean_object* v_inst_277_, lean_object* v_x_278_){
_start:
{
lean_object* v_value_279_; lean_object* v_pos_280_; lean_object* v_remaining_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_value_279_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_value_279_);
v_pos_280_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_pos_280_);
v_remaining_281_ = lean_ctor_get(v_x_278_, 2);
lean_inc(v_remaining_281_);
lean_dec_ref(v_x_278_);
v___x_282_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5));
v___x_283_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__6));
v___x_284_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_Option_repr___redArg(v_inst_277_, v_value_279_, v___x_285_);
v___x_287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_284_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = 0;
v___x_289_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*1, v___x_288_);
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_283_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__9));
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_box(1);
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__11));
v___x_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_282_);
v___x_298_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12);
v___x_299_ = l_Nat_reprFast(v_pos_280_);
v___x_300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___x_301_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_298_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set_uint8(v___x_302_, sizeof(void*)*1, v___x_288_);
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_297_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_291_);
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_293_);
v___x_306_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__14));
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v___x_282_);
v___x_309_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15);
v___x_310_ = l_Nat_reprFast(v_remaining_281_);
v___x_311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
v___x_312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_309_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_288_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_308_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18);
v___x_316_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__19));
v___x_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_314_);
v___x_318_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__20));
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_315_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*1, v___x_288_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(lean_object* v_00_u03b1_322_, lean_object* v_inst_323_, lean_object* v_x_324_, lean_object* v_prec_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(v_inst_323_, v_x_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed(lean_object* v_00_u03b1_327_, lean_object* v_inst_328_, lean_object* v_x_329_, lean_object* v_prec_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(v_00_u03b1_327_, v_inst_328_, v_x_329_, v_prec_330_);
lean_dec(v_prec_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot___redArg(lean_object* v_inst_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_333_, 0, lean_box(0));
lean_closure_set(v___x_333_, 1, v_inst_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot(lean_object* v_00_u03b1_334_, lean_object* v_inst_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_336_, 0, lean_box(0));
lean_closure_set(v___x_336_, 1, v_inst_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10));
v___x_364_ = l_Lean_mkAtom(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12);
v___x_366_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_367_ = lean_array_push(v___x_366_, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__16));
v___x_379_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_380_ = lean_array_push(v___x_379_, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_381_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17);
v___x_382_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15));
v___x_383_ = lean_box(2);
v___x_384_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___x_381_);
return v___x_384_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18);
v___x_386_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13);
v___x_387_ = lean_array_push(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_388_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19);
v___x_389_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11));
v___x_390_ = lean_box(2);
v___x_391_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_ctor_set(v___x_391_, 2, v___x_388_);
return v___x_391_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20);
v___x_393_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_394_ = lean_array_push(v___x_393_, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21);
v___x_396_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9));
v___x_397_ = lean_box(2);
v___x_398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_395_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22);
v___x_400_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_401_ = lean_array_push(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23);
v___x_403_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7));
v___x_404_ = lean_box(2);
v___x_405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
return v___x_405_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24);
v___x_407_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_408_ = lean_array_push(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25);
v___x_410_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4));
v___x_411_ = lean_box(2);
v___x_412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
return v___x_412_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1(void){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(lean_object* v_x_414_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_Std_instInhabitedSlot_default___redArg___closed__0));
v___x_417_ = lean_st_mk_ref(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(v_x_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(lean_object* v_n_421_, lean_object* v_f_422_, lean_object* v_xs_423_, lean_object* v_k_424_, lean_object* v_acc_425_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = lean_nat_dec_lt(v_k_424_, v_n_421_);
if (v___x_427_ == 0)
{
lean_dec(v_k_424_);
lean_dec_ref(v_f_422_);
return v_acc_425_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_428_ = lean_array_fget_borrowed(v_xs_423_, v_k_424_);
lean_inc_ref(v_f_422_);
lean_inc(v___x_428_);
v___x_429_ = lean_apply_2(v_f_422_, v___x_428_, lean_box(0));
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_k_424_, v___x_430_);
lean_dec(v_k_424_);
v___x_432_ = lean_array_push(v_acc_425_, v___x_429_);
v_k_424_ = v___x_431_;
v_acc_425_ = v___x_432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_434_, lean_object* v_f_435_, lean_object* v_xs_436_, lean_object* v_k_437_, lean_object* v_acc_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_434_, v_f_435_, v_xs_436_, v_k_437_, v_acc_438_);
lean_dec_ref(v_xs_436_);
lean_dec(v_n_434_);
return v_res_440_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_Queue_empty___redArg();
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(lean_object* v_capacity_445_){
_start:
{
lean_object* v___f_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___f_447_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__0));
v___x_448_ = lean_box(0);
lean_inc(v_capacity_445_);
v___x_449_ = lean_mk_array(v_capacity_445_, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__1));
v___x_452_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_capacity_445_, v___f_447_, v___x_449_, v___x_450_, v___x_451_);
lean_dec_ref(v___x_449_);
v___x_453_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_454_ = lean_box(1);
v___x_455_ = 0;
v___x_456_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_456_, 0, v___x_453_);
lean_ctor_set(v___x_456_, 1, v___x_453_);
lean_ctor_set(v___x_456_, 2, v_capacity_445_);
lean_ctor_set(v___x_456_, 3, v___x_450_);
lean_ctor_set(v___x_456_, 4, v___x_452_);
lean_ctor_set(v___x_456_, 5, v___x_450_);
lean_ctor_set(v___x_456_, 6, v___x_450_);
lean_ctor_set(v___x_456_, 7, v___x_454_);
lean_ctor_set(v___x_456_, 8, v___x_450_);
lean_ctor_set(v___x_456_, 9, v___x_450_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*10, v___x_455_);
v___x_457_ = l_Std_Mutex_new___redArg(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___boxed(lean_object* v_capacity_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new(lean_object* v_00_u03b1_461_, lean_object* v_capacity_462_, lean_object* v_h_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_462_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___boxed(lean_object* v_00_u03b1_466_, lean_object* v_capacity_467_, lean_object* v_h_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new(v_00_u03b1_466_, v_capacity_467_, v_h_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(lean_object* v_00_u03b1_471_, lean_object* v_00_u03b2_472_, lean_object* v_n_473_, lean_object* v_f_474_, lean_object* v_xs_475_, lean_object* v_k_476_, lean_object* v_h_477_, lean_object* v_acc_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_473_, v_f_474_, v_xs_475_, v_k_476_, v_acc_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_481_, lean_object* v_00_u03b2_482_, lean_object* v_n_483_, lean_object* v_f_484_, lean_object* v_xs_485_, lean_object* v_k_486_, lean_object* v_h_487_, lean_object* v_acc_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(v_00_u03b1_481_, v_00_u03b2_482_, v_n_483_, v_f_484_, v_xs_485_, v_k_486_, v_h_487_, v_acc_488_);
lean_dec_ref(v_xs_485_);
lean_dec(v_n_483_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(lean_object* v_mutex_491_, lean_object* v_k_492_){
_start:
{
lean_object* v_ref_494_; lean_object* v_mutex_495_; lean_object* v___x_496_; lean_object* v_r_497_; 
v_ref_494_ = lean_ctor_get(v_mutex_491_, 0);
lean_inc(v_ref_494_);
v_mutex_495_ = lean_ctor_get(v_mutex_491_, 1);
lean_inc(v_mutex_495_);
lean_dec_ref(v_mutex_491_);
v___x_496_ = lean_io_basemutex_lock(v_mutex_495_);
v_r_497_ = lean_apply_2(v_k_492_, v_ref_494_, lean_box(0));
if (lean_obj_tag(v_r_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_506_; 
v_a_498_ = lean_ctor_get(v_r_497_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_r_497_);
if (v_isSharedCheck_506_ == 0)
{
v___x_500_ = v_r_497_;
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v_r_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_506_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_io_basemutex_unlock(v_mutex_495_);
lean_dec(v_mutex_495_);
if (v_isShared_501_ == 0)
{
v___x_504_ = v___x_500_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_498_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_a_507_ = lean_ctor_get(v_r_497_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_r_497_);
if (v_isSharedCheck_515_ == 0)
{
v___x_509_ = v_r_497_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v_r_497_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_io_basemutex_unlock(v_mutex_495_);
lean_dec(v_mutex_495_);
if (v_isShared_510_ == 0)
{
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_507_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg___boxed(lean_object* v_mutex_516_, lean_object* v_k_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_516_, v_k_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_mutex_522_, lean_object* v_k_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_522_, v_k_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___boxed(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_mutex_528_, lean_object* v_k_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(v_00_u03b1_526_, v_00_u03b2_527_, v_mutex_528_, v_k_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(lean_object* v_k_532_, lean_object* v_v_533_, lean_object* v_t_534_){
_start:
{
if (lean_obj_tag(v_t_534_) == 0)
{
lean_object* v_size_535_; lean_object* v_k_536_; lean_object* v_v_537_; lean_object* v_l_538_; lean_object* v_r_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_820_; 
v_size_535_ = lean_ctor_get(v_t_534_, 0);
v_k_536_ = lean_ctor_get(v_t_534_, 1);
v_v_537_ = lean_ctor_get(v_t_534_, 2);
v_l_538_ = lean_ctor_get(v_t_534_, 3);
v_r_539_ = lean_ctor_get(v_t_534_, 4);
v_isSharedCheck_820_ = !lean_is_exclusive(v_t_534_);
if (v_isSharedCheck_820_ == 0)
{
v___x_541_ = v_t_534_;
v_isShared_542_ = v_isSharedCheck_820_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_r_539_);
lean_inc(v_l_538_);
lean_inc(v_v_537_);
lean_inc(v_k_536_);
lean_inc(v_size_535_);
lean_dec(v_t_534_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_820_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
uint8_t v___x_543_; 
v___x_543_ = lean_nat_dec_lt(v_k_532_, v_k_536_);
if (v___x_543_ == 0)
{
uint8_t v___x_544_; 
v___x_544_ = lean_nat_dec_eq(v_k_532_, v_k_536_);
if (v___x_544_ == 0)
{
lean_object* v_impl_545_; lean_object* v___x_546_; 
lean_dec(v_size_535_);
v_impl_545_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_532_, v_v_533_, v_r_539_);
v___x_546_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_538_) == 0)
{
lean_object* v_size_547_; lean_object* v_size_548_; lean_object* v_k_549_; lean_object* v_v_550_; lean_object* v_l_551_; lean_object* v_r_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_size_547_ = lean_ctor_get(v_l_538_, 0);
v_size_548_ = lean_ctor_get(v_impl_545_, 0);
lean_inc(v_size_548_);
v_k_549_ = lean_ctor_get(v_impl_545_, 1);
lean_inc(v_k_549_);
v_v_550_ = lean_ctor_get(v_impl_545_, 2);
lean_inc(v_v_550_);
v_l_551_ = lean_ctor_get(v_impl_545_, 3);
lean_inc(v_l_551_);
v_r_552_ = lean_ctor_get(v_impl_545_, 4);
lean_inc(v_r_552_);
v___x_553_ = lean_unsigned_to_nat(3u);
v___x_554_ = lean_nat_mul(v___x_553_, v_size_547_);
v___x_555_ = lean_nat_dec_lt(v___x_554_, v_size_548_);
lean_dec(v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_r_552_);
lean_dec(v_l_551_);
lean_dec(v_v_550_);
lean_dec(v_k_549_);
v___x_556_ = lean_nat_add(v___x_546_, v_size_547_);
v___x_557_ = lean_nat_add(v___x_556_, v_size_548_);
lean_dec(v_size_548_);
lean_dec(v___x_556_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v_impl_545_);
lean_ctor_set(v___x_541_, 0, v___x_557_);
v___x_559_ = v___x_541_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_l_538_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v_impl_545_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_624_; 
v_isSharedCheck_624_ = !lean_is_exclusive(v_impl_545_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; lean_object* v_unused_626_; lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; 
v_unused_625_ = lean_ctor_get(v_impl_545_, 4);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v_impl_545_, 3);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v_impl_545_, 2);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_impl_545_, 1);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_impl_545_, 0);
lean_dec(v_unused_629_);
v___x_562_ = v_impl_545_;
v_isShared_563_ = v_isSharedCheck_624_;
goto v_resetjp_561_;
}
else
{
lean_dec(v_impl_545_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_624_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v_size_564_; lean_object* v_k_565_; lean_object* v_v_566_; lean_object* v_l_567_; lean_object* v_r_568_; lean_object* v_size_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_size_564_ = lean_ctor_get(v_l_551_, 0);
v_k_565_ = lean_ctor_get(v_l_551_, 1);
v_v_566_ = lean_ctor_get(v_l_551_, 2);
v_l_567_ = lean_ctor_get(v_l_551_, 3);
v_r_568_ = lean_ctor_get(v_l_551_, 4);
v_size_569_ = lean_ctor_get(v_r_552_, 0);
v___x_570_ = lean_unsigned_to_nat(2u);
v___x_571_ = lean_nat_mul(v___x_570_, v_size_569_);
v___x_572_ = lean_nat_dec_lt(v_size_564_, v___x_571_);
lean_dec(v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_600_; 
lean_inc(v_r_568_);
lean_inc(v_l_567_);
lean_inc(v_v_566_);
lean_inc(v_k_565_);
v_isSharedCheck_600_ = !lean_is_exclusive(v_l_551_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; lean_object* v_unused_602_; lean_object* v_unused_603_; lean_object* v_unused_604_; lean_object* v_unused_605_; 
v_unused_601_ = lean_ctor_get(v_l_551_, 4);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_l_551_, 3);
lean_dec(v_unused_602_);
v_unused_603_ = lean_ctor_get(v_l_551_, 2);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_l_551_, 1);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_l_551_, 0);
lean_dec(v_unused_605_);
v___x_574_ = v_l_551_;
v_isShared_575_ = v_isSharedCheck_600_;
goto v_resetjp_573_;
}
else
{
lean_dec(v_l_551_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_600_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_590_; 
v___x_576_ = lean_nat_add(v___x_546_, v_size_547_);
v___x_577_ = lean_nat_add(v___x_576_, v_size_548_);
lean_dec(v_size_548_);
if (lean_obj_tag(v_l_567_) == 0)
{
lean_object* v_size_598_; 
v_size_598_ = lean_ctor_get(v_l_567_, 0);
lean_inc(v_size_598_);
v___y_590_ = v_size_598_;
goto v___jp_589_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___y_590_ = v___x_599_;
goto v___jp_589_;
}
v___jp_578_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_nat_add(v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 4, v_r_552_);
lean_ctor_set(v___x_574_, 3, v_r_568_);
lean_ctor_set(v___x_574_, 2, v_v_550_);
lean_ctor_set(v___x_574_, 1, v_k_549_);
lean_ctor_set(v___x_574_, 0, v___x_582_);
v___x_584_ = v___x_574_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_k_549_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_v_550_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_r_568_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v_r_552_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 4, v___x_584_);
lean_ctor_set(v___x_562_, 3, v___y_579_);
lean_ctor_set(v___x_562_, 2, v_v_566_);
lean_ctor_set(v___x_562_, 1, v_k_565_);
lean_ctor_set(v___x_562_, 0, v___x_577_);
v___x_586_ = v___x_562_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_k_565_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v_v_566_);
lean_ctor_set(v_reuseFailAlloc_587_, 3, v___y_579_);
lean_ctor_set(v_reuseFailAlloc_587_, 4, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = lean_nat_add(v___x_576_, v___y_590_);
lean_dec(v___y_590_);
lean_dec(v___x_576_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v_l_567_);
lean_ctor_set(v___x_541_, 0, v___x_591_);
v___x_593_ = v___x_541_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_l_538_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_l_567_);
v___x_593_ = v_reuseFailAlloc_597_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = lean_nat_add(v___x_546_, v_size_569_);
if (lean_obj_tag(v_r_568_) == 0)
{
lean_object* v_size_595_; 
v_size_595_ = lean_ctor_get(v_r_568_, 0);
lean_inc(v_size_595_);
v___y_579_ = v___x_593_;
v___y_580_ = v___x_594_;
v___y_581_ = v_size_595_;
goto v___jp_578_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___y_579_ = v___x_593_;
v___y_580_ = v___x_594_;
v___y_581_ = v___x_596_;
goto v___jp_578_;
}
}
}
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
lean_del_object(v___x_541_);
v___x_606_ = lean_nat_add(v___x_546_, v_size_547_);
v___x_607_ = lean_nat_add(v___x_606_, v_size_548_);
lean_dec(v_size_548_);
v___x_608_ = lean_nat_add(v___x_606_, v_size_564_);
lean_dec(v___x_606_);
lean_inc_ref(v_l_538_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 4, v_l_551_);
lean_ctor_set(v___x_562_, 3, v_l_538_);
lean_ctor_set(v___x_562_, 2, v_v_537_);
lean_ctor_set(v___x_562_, 1, v_k_536_);
lean_ctor_set(v___x_562_, 0, v___x_608_);
v___x_610_ = v___x_562_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_l_538_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_l_551_);
v___x_610_ = v_reuseFailAlloc_623_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_isSharedCheck_617_ = !lean_is_exclusive(v_l_538_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; lean_object* v_unused_622_; 
v_unused_618_ = lean_ctor_get(v_l_538_, 4);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_l_538_, 3);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_l_538_, 2);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_l_538_, 1);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_l_538_, 0);
lean_dec(v_unused_622_);
v___x_612_ = v_l_538_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_dec(v_l_538_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 4, v_r_552_);
lean_ctor_set(v___x_612_, 3, v___x_610_);
lean_ctor_set(v___x_612_, 2, v_v_550_);
lean_ctor_set(v___x_612_, 1, v_k_549_);
lean_ctor_set(v___x_612_, 0, v___x_607_);
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_k_549_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_v_550_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_r_552_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_630_; 
v_l_630_ = lean_ctor_get(v_impl_545_, 3);
lean_inc(v_l_630_);
if (lean_obj_tag(v_l_630_) == 0)
{
lean_object* v_r_631_; lean_object* v_k_632_; lean_object* v_v_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_656_; 
v_r_631_ = lean_ctor_get(v_impl_545_, 4);
v_k_632_ = lean_ctor_get(v_impl_545_, 1);
v_v_633_ = lean_ctor_get(v_impl_545_, 2);
v_isSharedCheck_656_ = !lean_is_exclusive(v_impl_545_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; lean_object* v_unused_658_; 
v_unused_657_ = lean_ctor_get(v_impl_545_, 3);
lean_dec(v_unused_657_);
v_unused_658_ = lean_ctor_get(v_impl_545_, 0);
lean_dec(v_unused_658_);
v___x_635_ = v_impl_545_;
v_isShared_636_ = v_isSharedCheck_656_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_r_631_);
lean_inc(v_v_633_);
lean_inc(v_k_632_);
lean_dec(v_impl_545_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_656_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_k_637_; lean_object* v_v_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_652_; 
v_k_637_ = lean_ctor_get(v_l_630_, 1);
v_v_638_ = lean_ctor_get(v_l_630_, 2);
v_isSharedCheck_652_ = !lean_is_exclusive(v_l_630_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; 
v_unused_653_ = lean_ctor_get(v_l_630_, 4);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_l_630_, 3);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_l_630_, 0);
lean_dec(v_unused_655_);
v___x_640_ = v_l_630_;
v_isShared_641_ = v_isSharedCheck_652_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_v_638_);
lean_inc(v_k_637_);
lean_dec(v_l_630_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_652_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_631_, 2);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 4, v_r_631_);
lean_ctor_set(v___x_640_, 3, v_r_631_);
lean_ctor_set(v___x_640_, 2, v_v_537_);
lean_ctor_set(v___x_640_, 1, v_k_536_);
lean_ctor_set(v___x_640_, 0, v___x_546_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_r_631_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v_r_631_);
v___x_644_ = v_reuseFailAlloc_651_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
lean_inc(v_r_631_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 3, v_r_631_);
lean_ctor_set(v___x_635_, 0, v___x_546_);
v___x_646_ = v___x_635_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_k_632_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_v_633_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_r_631_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_r_631_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v___x_646_);
lean_ctor_set(v___x_541_, 3, v___x_644_);
lean_ctor_set(v___x_541_, 2, v_v_638_);
lean_ctor_set(v___x_541_, 1, v_k_637_);
lean_ctor_set(v___x_541_, 0, v___x_642_);
v___x_648_ = v___x_541_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_k_637_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_v_638_);
lean_ctor_set(v_reuseFailAlloc_649_, 3, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_649_, 4, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
else
{
lean_object* v_r_659_; 
v_r_659_ = lean_ctor_get(v_impl_545_, 4);
lean_inc(v_r_659_);
if (lean_obj_tag(v_r_659_) == 0)
{
lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_672_; 
v_k_660_ = lean_ctor_get(v_impl_545_, 1);
v_v_661_ = lean_ctor_get(v_impl_545_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v_impl_545_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; lean_object* v_unused_674_; lean_object* v_unused_675_; 
v_unused_673_ = lean_ctor_get(v_impl_545_, 4);
lean_dec(v_unused_673_);
v_unused_674_ = lean_ctor_get(v_impl_545_, 3);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_impl_545_, 0);
lean_dec(v_unused_675_);
v___x_663_ = v_impl_545_;
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_v_661_);
lean_inc(v_k_660_);
lean_dec(v_impl_545_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_672_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = lean_unsigned_to_nat(3u);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 4, v_l_630_);
lean_ctor_set(v___x_663_, 2, v_v_537_);
lean_ctor_set(v___x_663_, 1, v_k_536_);
lean_ctor_set(v___x_663_, 0, v___x_546_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_l_630_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_l_630_);
v___x_667_ = v_reuseFailAlloc_671_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v_r_659_);
lean_ctor_set(v___x_541_, 3, v___x_667_);
lean_ctor_set(v___x_541_, 2, v_v_661_);
lean_ctor_set(v___x_541_, 1, v_k_660_);
lean_ctor_set(v___x_541_, 0, v___x_665_);
v___x_669_ = v___x_541_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_k_660_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_v_661_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_r_659_);
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
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_unsigned_to_nat(2u);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v_impl_545_);
lean_ctor_set(v___x_541_, 3, v_r_659_);
lean_ctor_set(v___x_541_, 0, v___x_676_);
v___x_678_ = v___x_541_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_r_659_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v_impl_545_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
else
{
lean_object* v___x_681_; 
lean_dec(v_v_537_);
lean_dec(v_k_536_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 2, v_v_533_);
lean_ctor_set(v___x_541_, 1, v_k_532_);
v___x_681_ = v___x_541_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_size_535_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_532_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_533_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_l_538_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_r_539_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
else
{
lean_object* v_impl_683_; lean_object* v___x_684_; 
lean_dec(v_size_535_);
v_impl_683_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_532_, v_v_533_, v_l_538_);
v___x_684_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_539_) == 0)
{
lean_object* v_size_685_; lean_object* v_size_686_; lean_object* v_k_687_; lean_object* v_v_688_; lean_object* v_l_689_; lean_object* v_r_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_size_685_ = lean_ctor_get(v_r_539_, 0);
v_size_686_ = lean_ctor_get(v_impl_683_, 0);
lean_inc(v_size_686_);
v_k_687_ = lean_ctor_get(v_impl_683_, 1);
lean_inc(v_k_687_);
v_v_688_ = lean_ctor_get(v_impl_683_, 2);
lean_inc(v_v_688_);
v_l_689_ = lean_ctor_get(v_impl_683_, 3);
lean_inc(v_l_689_);
v_r_690_ = lean_ctor_get(v_impl_683_, 4);
lean_inc(v_r_690_);
v___x_691_ = lean_unsigned_to_nat(3u);
v___x_692_ = lean_nat_mul(v___x_691_, v_size_685_);
v___x_693_ = lean_nat_dec_lt(v___x_692_, v_size_686_);
lean_dec(v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec(v_r_690_);
lean_dec(v_l_689_);
lean_dec(v_v_688_);
lean_dec(v_k_687_);
v___x_694_ = lean_nat_add(v___x_684_, v_size_686_);
lean_dec(v_size_686_);
v___x_695_ = lean_nat_add(v___x_694_, v_size_685_);
lean_dec(v___x_694_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 3, v_impl_683_);
lean_ctor_set(v___x_541_, 0, v___x_695_);
v___x_697_ = v___x_541_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_impl_683_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_r_539_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
else
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_764_; 
v_isSharedCheck_764_ = !lean_is_exclusive(v_impl_683_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; 
v_unused_765_ = lean_ctor_get(v_impl_683_, 4);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_impl_683_, 3);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_impl_683_, 2);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_impl_683_, 1);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_impl_683_, 0);
lean_dec(v_unused_769_);
v___x_700_ = v_impl_683_;
v_isShared_701_ = v_isSharedCheck_764_;
goto v_resetjp_699_;
}
else
{
lean_dec(v_impl_683_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_764_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_size_702_; lean_object* v_size_703_; lean_object* v_k_704_; lean_object* v_v_705_; lean_object* v_l_706_; lean_object* v_r_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_size_702_ = lean_ctor_get(v_l_689_, 0);
v_size_703_ = lean_ctor_get(v_r_690_, 0);
v_k_704_ = lean_ctor_get(v_r_690_, 1);
v_v_705_ = lean_ctor_get(v_r_690_, 2);
v_l_706_ = lean_ctor_get(v_r_690_, 3);
v_r_707_ = lean_ctor_get(v_r_690_, 4);
v___x_708_ = lean_unsigned_to_nat(2u);
v___x_709_ = lean_nat_mul(v___x_708_, v_size_702_);
v___x_710_ = lean_nat_dec_lt(v_size_703_, v___x_709_);
lean_dec(v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_739_; 
lean_inc(v_r_707_);
lean_inc(v_l_706_);
lean_inc(v_v_705_);
lean_inc(v_k_704_);
v_isSharedCheck_739_ = !lean_is_exclusive(v_r_690_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; lean_object* v_unused_741_; lean_object* v_unused_742_; lean_object* v_unused_743_; lean_object* v_unused_744_; 
v_unused_740_ = lean_ctor_get(v_r_690_, 4);
lean_dec(v_unused_740_);
v_unused_741_ = lean_ctor_get(v_r_690_, 3);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_r_690_, 2);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_r_690_, 1);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v_r_690_, 0);
lean_dec(v_unused_744_);
v___x_712_ = v_r_690_;
v_isShared_713_ = v_isSharedCheck_739_;
goto v_resetjp_711_;
}
else
{
lean_dec(v_r_690_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_739_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___x_727_; lean_object* v___y_729_; 
v___x_714_ = lean_nat_add(v___x_684_, v_size_686_);
lean_dec(v_size_686_);
v___x_715_ = lean_nat_add(v___x_714_, v_size_685_);
lean_dec(v___x_714_);
v___x_727_ = lean_nat_add(v___x_684_, v_size_702_);
if (lean_obj_tag(v_l_706_) == 0)
{
lean_object* v_size_737_; 
v_size_737_ = lean_ctor_get(v_l_706_, 0);
lean_inc(v_size_737_);
v___y_729_ = v_size_737_;
goto v___jp_728_;
}
else
{
lean_object* v___x_738_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___y_729_ = v___x_738_;
goto v___jp_728_;
}
v___jp_716_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_nat_add(v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec(v___y_718_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 4, v_r_539_);
lean_ctor_set(v___x_712_, 3, v_r_707_);
lean_ctor_set(v___x_712_, 2, v_v_537_);
lean_ctor_set(v___x_712_, 1, v_k_536_);
lean_ctor_set(v___x_712_, 0, v___x_720_);
v___x_722_ = v___x_712_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v_r_707_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v_r_539_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_724_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 4, v___x_722_);
lean_ctor_set(v___x_700_, 3, v___y_717_);
lean_ctor_set(v___x_700_, 2, v_v_705_);
lean_ctor_set(v___x_700_, 1, v_k_704_);
lean_ctor_set(v___x_700_, 0, v___x_715_);
v___x_724_ = v___x_700_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_k_704_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_v_705_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v___y_717_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_nat_add(v___x_727_, v___y_729_);
lean_dec(v___y_729_);
lean_dec(v___x_727_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v_l_706_);
lean_ctor_set(v___x_541_, 3, v_l_689_);
lean_ctor_set(v___x_541_, 2, v_v_688_);
lean_ctor_set(v___x_541_, 1, v_k_687_);
lean_ctor_set(v___x_541_, 0, v___x_730_);
v___x_732_ = v___x_541_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_k_687_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_v_688_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v_l_689_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_l_706_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_nat_add(v___x_684_, v_size_685_);
if (lean_obj_tag(v_r_707_) == 0)
{
lean_object* v_size_734_; 
v_size_734_ = lean_ctor_get(v_r_707_, 0);
lean_inc(v_size_734_);
v___y_717_ = v___x_732_;
v___y_718_ = v___x_733_;
v___y_719_ = v_size_734_;
goto v___jp_716_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = lean_unsigned_to_nat(0u);
v___y_717_ = v___x_732_;
v___y_718_ = v___x_733_;
v___y_719_ = v___x_735_;
goto v___jp_716_;
}
}
}
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
lean_del_object(v___x_541_);
v___x_745_ = lean_nat_add(v___x_684_, v_size_686_);
lean_dec(v_size_686_);
v___x_746_ = lean_nat_add(v___x_745_, v_size_685_);
lean_dec(v___x_745_);
v___x_747_ = lean_nat_add(v___x_684_, v_size_685_);
v___x_748_ = lean_nat_add(v___x_747_, v_size_703_);
lean_dec(v___x_747_);
lean_inc_ref(v_r_539_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 4, v_r_539_);
lean_ctor_set(v___x_700_, 3, v_r_690_);
lean_ctor_set(v___x_700_, 2, v_v_537_);
lean_ctor_set(v___x_700_, 1, v_k_536_);
lean_ctor_set(v___x_700_, 0, v___x_748_);
v___x_750_ = v___x_700_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_r_690_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_r_539_);
v___x_750_ = v_reuseFailAlloc_763_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_isSharedCheck_757_ = !lean_is_exclusive(v_r_539_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; 
v_unused_758_ = lean_ctor_get(v_r_539_, 4);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_r_539_, 3);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_r_539_, 2);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_r_539_, 1);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_r_539_, 0);
lean_dec(v_unused_762_);
v___x_752_ = v_r_539_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_dec(v_r_539_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 4, v___x_750_);
lean_ctor_set(v___x_752_, 3, v_l_689_);
lean_ctor_set(v___x_752_, 2, v_v_688_);
lean_ctor_set(v___x_752_, 1, v_k_687_);
lean_ctor_set(v___x_752_, 0, v___x_746_);
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_k_687_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_v_688_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_l_689_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v___x_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_770_; 
v_l_770_ = lean_ctor_get(v_impl_683_, 3);
lean_inc(v_l_770_);
if (lean_obj_tag(v_l_770_) == 0)
{
lean_object* v_r_771_; lean_object* v_k_772_; lean_object* v_v_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_784_; 
v_r_771_ = lean_ctor_get(v_impl_683_, 4);
v_k_772_ = lean_ctor_get(v_impl_683_, 1);
v_v_773_ = lean_ctor_get(v_impl_683_, 2);
v_isSharedCheck_784_ = !lean_is_exclusive(v_impl_683_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; lean_object* v_unused_786_; 
v_unused_785_ = lean_ctor_get(v_impl_683_, 3);
lean_dec(v_unused_785_);
v_unused_786_ = lean_ctor_get(v_impl_683_, 0);
lean_dec(v_unused_786_);
v___x_775_ = v_impl_683_;
v_isShared_776_ = v_isSharedCheck_784_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_r_771_);
lean_inc(v_v_773_);
lean_inc(v_k_772_);
lean_dec(v_impl_683_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_784_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_771_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 3, v_r_771_);
lean_ctor_set(v___x_775_, 2, v_v_537_);
lean_ctor_set(v___x_775_, 1, v_k_536_);
lean_ctor_set(v___x_775_, 0, v___x_684_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_r_771_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_r_771_);
v___x_779_ = v_reuseFailAlloc_783_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v___x_779_);
lean_ctor_set(v___x_541_, 3, v_l_770_);
lean_ctor_set(v___x_541_, 2, v_v_773_);
lean_ctor_set(v___x_541_, 1, v_k_772_);
lean_ctor_set(v___x_541_, 0, v___x_777_);
v___x_781_ = v___x_541_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_k_772_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_v_773_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_l_770_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_r_787_; 
v_r_787_ = lean_ctor_get(v_impl_683_, 4);
lean_inc(v_r_787_);
if (lean_obj_tag(v_r_787_) == 0)
{
lean_object* v_k_788_; lean_object* v_v_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_812_; 
v_k_788_ = lean_ctor_get(v_impl_683_, 1);
v_v_789_ = lean_ctor_get(v_impl_683_, 2);
v_isSharedCheck_812_ = !lean_is_exclusive(v_impl_683_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; lean_object* v_unused_814_; lean_object* v_unused_815_; 
v_unused_813_ = lean_ctor_get(v_impl_683_, 4);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_impl_683_, 3);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_impl_683_, 0);
lean_dec(v_unused_815_);
v___x_791_ = v_impl_683_;
v_isShared_792_ = v_isSharedCheck_812_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_v_789_);
lean_inc(v_k_788_);
lean_dec(v_impl_683_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_812_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_k_793_; lean_object* v_v_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_808_; 
v_k_793_ = lean_ctor_get(v_r_787_, 1);
v_v_794_ = lean_ctor_get(v_r_787_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_r_787_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; lean_object* v_unused_811_; 
v_unused_809_ = lean_ctor_get(v_r_787_, 4);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_r_787_, 3);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_r_787_, 0);
lean_dec(v_unused_811_);
v___x_796_ = v_r_787_;
v_isShared_797_ = v_isSharedCheck_808_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_v_794_);
lean_inc(v_k_793_);
lean_dec(v_r_787_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_808_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_unsigned_to_nat(3u);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 4, v_l_770_);
lean_ctor_set(v___x_796_, 3, v_l_770_);
lean_ctor_set(v___x_796_, 2, v_v_789_);
lean_ctor_set(v___x_796_, 1, v_k_788_);
lean_ctor_set(v___x_796_, 0, v___x_684_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_l_770_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_l_770_);
v___x_800_ = v_reuseFailAlloc_807_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v_l_770_);
lean_ctor_set(v___x_791_, 2, v_v_537_);
lean_ctor_set(v___x_791_, 1, v_k_536_);
lean_ctor_set(v___x_791_, 0, v___x_684_);
v___x_802_ = v___x_791_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_l_770_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_l_770_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v___x_802_);
lean_ctor_set(v___x_541_, 3, v___x_800_);
lean_ctor_set(v___x_541_, 2, v_v_794_);
lean_ctor_set(v___x_541_, 1, v_k_793_);
lean_ctor_set(v___x_541_, 0, v___x_798_);
v___x_804_ = v___x_541_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_793_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_794_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
else
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_unsigned_to_nat(2u);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 4, v_r_787_);
lean_ctor_set(v___x_541_, 3, v_impl_683_);
lean_ctor_set(v___x_541_, 0, v___x_816_);
v___x_818_ = v___x_541_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_k_536_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_v_537_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_impl_683_);
lean_ctor_set(v_reuseFailAlloc_819_, 4, v_r_787_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v_k_532_);
lean_ctor_set(v___x_822_, 2, v_v_533_);
lean_ctor_set(v___x_822_, 3, v_t_534_);
lean_ctor_set(v___x_822_, 4, v_t_534_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; lean_object* v_producers_826_; lean_object* v_waiters_827_; lean_object* v_capacity_828_; lean_object* v_size_829_; lean_object* v_buffer_830_; lean_object* v_write_831_; lean_object* v_read_832_; lean_object* v_receivers_833_; lean_object* v_nextId_834_; uint8_t v_closed_835_; lean_object* v_pos_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_848_; 
v___x_825_ = lean_st_ref_take(v___y_823_);
v_producers_826_ = lean_ctor_get(v___x_825_, 0);
v_waiters_827_ = lean_ctor_get(v___x_825_, 1);
v_capacity_828_ = lean_ctor_get(v___x_825_, 2);
v_size_829_ = lean_ctor_get(v___x_825_, 3);
v_buffer_830_ = lean_ctor_get(v___x_825_, 4);
v_write_831_ = lean_ctor_get(v___x_825_, 5);
v_read_832_ = lean_ctor_get(v___x_825_, 6);
v_receivers_833_ = lean_ctor_get(v___x_825_, 7);
v_nextId_834_ = lean_ctor_get(v___x_825_, 8);
v_closed_835_ = lean_ctor_get_uint8(v___x_825_, sizeof(void*)*10);
v_pos_836_ = lean_ctor_get(v___x_825_, 9);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_848_ == 0)
{
v___x_838_ = v___x_825_;
v_isShared_839_ = v_isSharedCheck_848_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_pos_836_);
lean_inc(v_nextId_834_);
lean_inc(v_receivers_833_);
lean_inc(v_read_832_);
lean_inc(v_write_831_);
lean_inc(v_buffer_830_);
lean_inc(v_size_829_);
lean_inc(v_capacity_828_);
lean_inc(v_waiters_827_);
lean_inc(v_producers_826_);
lean_dec(v___x_825_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_848_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
lean_inc(v_pos_836_);
lean_inc(v_nextId_834_);
v___x_840_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_nextId_834_, v_pos_836_, v_receivers_833_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_add(v_nextId_834_, v___x_841_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 8, v___x_842_);
lean_ctor_set(v___x_838_, 7, v___x_840_);
v___x_844_ = v___x_838_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_producers_826_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_waiters_827_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_capacity_828_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v_size_829_);
lean_ctor_set(v_reuseFailAlloc_847_, 4, v_buffer_830_);
lean_ctor_set(v_reuseFailAlloc_847_, 5, v_write_831_);
lean_ctor_set(v_reuseFailAlloc_847_, 6, v_read_832_);
lean_ctor_set(v_reuseFailAlloc_847_, 7, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_847_, 8, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_847_, 9, v_pos_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_847_, sizeof(void*)*10, v_closed_835_);
v___x_844_ = v_reuseFailAlloc_847_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_st_ref_put(v___y_823_, v___x_844_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_nextId_834_);
return v___x_846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0___boxed(lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(v___y_849_);
lean_dec(v___y_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(lean_object* v_bd_853_){
_start:
{
lean_object* v___f_855_; lean_object* v___x_856_; 
v___f_855_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___closed__0));
lean_inc_ref(v_bd_853_);
v___x_856_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_bd_853_, v___f_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_865_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_865_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v_bd_853_);
lean_ctor_set(v___x_861_, 1, v_a_857_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v_bd_853_);
v_a_866_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_856_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_856_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___boxed(lean_object* v_bd_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(lean_object* v_00_u03b1_877_, lean_object* v_bd_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_878_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___boxed(lean_object* v_00_u03b1_881_, lean_object* v_bd_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(v_00_u03b1_881_, v_bd_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0(lean_object* v_00_u03b2_885_, lean_object* v_k_886_, lean_object* v_v_887_, lean_object* v_t_888_, lean_object* v_hl_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_886_, v_v_887_, v_t_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(lean_object* v_toApplicative_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_size_893_; lean_object* v_toPure_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_size_893_ = lean_ctor_get(v_a_892_, 3);
v_toPure_894_ = lean_ctor_get(v_toApplicative_891_, 1);
lean_inc(v_toPure_894_);
lean_dec_ref(v_toApplicative_891_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_eq(v_size_893_, v___x_895_);
v___x_897_ = lean_box(v___x_896_);
v___x_898_ = lean_apply_2(v_toPure_894_, lean_box(0), v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed(lean_object* v_toApplicative_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(v_toApplicative_899_, v_a_900_);
lean_dec_ref(v_a_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_toApplicative_905_; lean_object* v_toBind_906_; lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_toApplicative_905_ = lean_ctor_get(v_inst_902_, 0);
lean_inc_ref(v_toApplicative_905_);
v_toBind_906_ = lean_ctor_get(v_inst_902_, 1);
lean_inc(v_toBind_906_);
lean_dec_ref(v_inst_902_);
v___f_907_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_907_, 0, v_toApplicative_905_);
lean_inc(v_a_904_);
v___x_908_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_908_, 0, lean_box(0));
lean_closure_set(v___x_908_, 1, lean_box(0));
lean_closure_set(v___x_908_, 2, v_a_904_);
v___x_909_ = lean_apply_2(v_inst_903_, lean_box(0), v___x_908_);
v___x_910_ = lean_apply_4(v_toBind_906_, lean_box(0), lean_box(0), v___x_909_, v___f_907_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___boxed(lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_911_, v_inst_912_, v_a_913_);
lean_dec(v_a_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(lean_object* v_m_915_, lean_object* v_00_u03b1_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_917_, v_inst_918_, v_a_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___boxed(lean_object* v_m_921_, lean_object* v_00_u03b1_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(v_m_921_, v_00_u03b1_922_, v_inst_923_, v_inst_924_, v_a_925_);
lean_dec(v_a_925_);
return v_res_926_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; lean_object* v_capacity_930_; lean_object* v_size_931_; uint8_t v___x_932_; 
v___x_929_ = lean_st_ref_get(v_a_927_);
v_capacity_930_ = lean_ctor_get(v___x_929_, 2);
lean_inc(v_capacity_930_);
v_size_931_ = lean_ctor_get(v___x_929_, 3);
lean_inc(v_size_931_);
lean_dec(v___x_929_);
v___x_932_ = lean_nat_dec_le(v_capacity_930_, v_size_931_);
lean_dec(v_size_931_);
lean_dec(v_capacity_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg___boxed(lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
uint8_t v_res_935_; lean_object* v_r_936_; 
v_res_935_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_933_);
lean_dec(v_a_933_);
v_r_936_ = lean_box(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(lean_object* v_00_u03b1_937_, lean_object* v_a_938_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_938_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___boxed(lean_object* v_00_u03b1_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_res_944_; lean_object* v_r_945_; 
v_res_944_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(v_00_u03b1_941_, v_a_942_);
lean_dec(v_a_942_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(lean_object* v_value_946_, lean_object* v_st_947_){
_start:
{
lean_object* v_producers_949_; lean_object* v_waiters_950_; lean_object* v_capacity_951_; lean_object* v_size_952_; lean_object* v_buffer_953_; lean_object* v_write_954_; lean_object* v_read_955_; lean_object* v_receivers_956_; lean_object* v_nextId_957_; uint8_t v_closed_958_; lean_object* v_pos_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_979_; 
v_producers_949_ = lean_ctor_get(v_st_947_, 0);
v_waiters_950_ = lean_ctor_get(v_st_947_, 1);
v_capacity_951_ = lean_ctor_get(v_st_947_, 2);
v_size_952_ = lean_ctor_get(v_st_947_, 3);
v_buffer_953_ = lean_ctor_get(v_st_947_, 4);
v_write_954_ = lean_ctor_get(v_st_947_, 5);
v_read_955_ = lean_ctor_get(v_st_947_, 6);
v_receivers_956_ = lean_ctor_get(v_st_947_, 7);
v_nextId_957_ = lean_ctor_get(v_st_947_, 8);
v_closed_958_ = lean_ctor_get_uint8(v_st_947_, sizeof(void*)*10);
v_pos_959_ = lean_ctor_get(v_st_947_, 9);
v_isSharedCheck_979_ = !lean_is_exclusive(v_st_947_);
if (v_isSharedCheck_979_ == 0)
{
v___x_961_ = v_st_947_;
v_isShared_962_ = v_isSharedCheck_979_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_pos_959_);
lean_inc(v_nextId_957_);
lean_inc(v_receivers_956_);
lean_inc(v_read_955_);
lean_inc(v_write_954_);
lean_inc(v_buffer_953_);
lean_inc(v_size_952_);
lean_inc(v_capacity_951_);
lean_inc(v_waiters_950_);
lean_inc(v_producers_949_);
lean_dec(v_st_947_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_979_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_tailRef_963_; lean_object* v___x_964_; lean_object* v___y_966_; 
v_tailRef_963_ = lean_array_fget_borrowed(v_buffer_953_, v_write_954_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v_value_946_);
if (lean_obj_tag(v_receivers_956_) == 0)
{
lean_object* v_size_977_; 
v_size_977_ = lean_ctor_get(v_receivers_956_, 0);
lean_inc(v_size_977_);
v___y_966_ = v_size_977_;
goto v___jp_965_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = lean_unsigned_to_nat(0u);
v___y_966_ = v___x_978_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
lean_inc(v_pos_959_);
v___x_967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_967_, 0, v___x_964_);
lean_ctor_set(v___x_967_, 1, v_pos_959_);
lean_ctor_set(v___x_967_, 2, v___y_966_);
v___x_968_ = lean_st_ref_swap(v_tailRef_963_, v___x_967_);
lean_dec(v___x_968_);
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = lean_nat_add(v_write_954_, v___x_969_);
lean_dec(v_write_954_);
v___x_971_ = lean_nat_mod(v___x_970_, v_capacity_951_);
lean_dec(v___x_970_);
v___x_972_ = lean_nat_add(v_size_952_, v___x_969_);
lean_dec(v_size_952_);
v___x_973_ = lean_nat_add(v_pos_959_, v___x_969_);
lean_dec(v_pos_959_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 9, v___x_973_);
lean_ctor_set(v___x_961_, 5, v___x_971_);
lean_ctor_set(v___x_961_, 3, v___x_972_);
v___x_975_ = v___x_961_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_producers_949_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_waiters_950_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_capacity_951_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_buffer_953_);
lean_ctor_set(v_reuseFailAlloc_976_, 5, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_976_, 6, v_read_955_);
lean_ctor_set(v_reuseFailAlloc_976_, 7, v_receivers_956_);
lean_ctor_set(v_reuseFailAlloc_976_, 8, v_nextId_957_);
lean_ctor_set(v_reuseFailAlloc_976_, 9, v___x_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_976_, sizeof(void*)*10, v_closed_958_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg___boxed(lean_object* v_value_980_, lean_object* v_st_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_980_, v_st_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(lean_object* v_00_u03b1_984_, lean_object* v_value_985_, lean_object* v_st_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_985_, v_st_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___boxed(lean_object* v_00_u03b1_989_, lean_object* v_value_990_, lean_object* v_st_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(v_00_u03b1_989_, v_value_990_, v_st_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(lean_object* v_st_994_){
_start:
{
lean_object* v_producers_995_; lean_object* v_waiters_996_; lean_object* v_capacity_997_; lean_object* v_size_998_; lean_object* v_buffer_999_; lean_object* v_write_1000_; lean_object* v_read_1001_; lean_object* v_receivers_1002_; lean_object* v_nextId_1003_; uint8_t v_closed_1004_; lean_object* v_pos_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1016_; 
v_producers_995_ = lean_ctor_get(v_st_994_, 0);
v_waiters_996_ = lean_ctor_get(v_st_994_, 1);
v_capacity_997_ = lean_ctor_get(v_st_994_, 2);
v_size_998_ = lean_ctor_get(v_st_994_, 3);
v_buffer_999_ = lean_ctor_get(v_st_994_, 4);
v_write_1000_ = lean_ctor_get(v_st_994_, 5);
v_read_1001_ = lean_ctor_get(v_st_994_, 6);
v_receivers_1002_ = lean_ctor_get(v_st_994_, 7);
v_nextId_1003_ = lean_ctor_get(v_st_994_, 8);
v_closed_1004_ = lean_ctor_get_uint8(v_st_994_, sizeof(void*)*10);
v_pos_1005_ = lean_ctor_get(v_st_994_, 9);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_st_994_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1007_ = v_st_994_;
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_pos_1005_);
lean_inc(v_nextId_1003_);
lean_inc(v_receivers_1002_);
lean_inc(v_read_1001_);
lean_inc(v_write_1000_);
lean_inc(v_buffer_999_);
lean_inc(v_size_998_);
lean_inc(v_capacity_997_);
lean_inc(v_waiters_996_);
lean_inc(v_producers_995_);
lean_dec(v_st_994_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v_size_1010_; lean_object* v___x_1011_; lean_object* v_read_1012_; lean_object* v___x_1014_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v_size_1010_ = lean_nat_sub(v_size_998_, v___x_1009_);
lean_dec(v_size_998_);
v___x_1011_ = lean_nat_add(v_read_1001_, v___x_1009_);
lean_dec(v_read_1001_);
v_read_1012_ = lean_nat_mod(v___x_1011_, v_capacity_997_);
lean_dec(v___x_1011_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 6, v_read_1012_);
lean_ctor_set(v___x_1007_, 3, v_size_1010_);
v___x_1014_ = v___x_1007_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_producers_995_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_waiters_996_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_capacity_997_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v_size_1010_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v_buffer_999_);
lean_ctor_set(v_reuseFailAlloc_1015_, 5, v_write_1000_);
lean_ctor_set(v_reuseFailAlloc_1015_, 6, v_read_1012_);
lean_ctor_set(v_reuseFailAlloc_1015_, 7, v_receivers_1002_);
lean_ctor_set(v_reuseFailAlloc_1015_, 8, v_nextId_1003_);
lean_ctor_set(v_reuseFailAlloc_1015_, 9, v_pos_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*10, v_closed_1004_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue(lean_object* v_00_u03b1_1017_, lean_object* v_st_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_st_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(lean_object* v_toApplicative_1020_, lean_object* v_place_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_capacity_1023_; lean_object* v_buffer_1024_; lean_object* v_toPure_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_capacity_1023_ = lean_ctor_get(v_a_1022_, 2);
v_buffer_1024_ = lean_ctor_get(v_a_1022_, 4);
v_toPure_1025_ = lean_ctor_get(v_toApplicative_1020_, 1);
lean_inc(v_toPure_1025_);
lean_dec_ref(v_toApplicative_1020_);
v___x_1026_ = lean_nat_mod(v_place_1021_, v_capacity_1023_);
v___x_1027_ = lean_array_fget_borrowed(v_buffer_1024_, v___x_1026_);
lean_dec(v___x_1026_);
lean_inc(v___x_1027_);
v___x_1028_ = lean_apply_2(v_toPure_1025_, lean_box(0), v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed(lean_object* v_toApplicative_1029_, lean_object* v_place_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(v_toApplicative_1029_, v_place_1030_, v_a_1031_);
lean_dec_ref(v_a_1031_);
lean_dec(v_place_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_place_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_toApplicative_1037_; lean_object* v_toBind_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_toApplicative_1037_ = lean_ctor_get(v_inst_1033_, 0);
lean_inc_ref(v_toApplicative_1037_);
v_toBind_1038_ = lean_ctor_get(v_inst_1033_, 1);
lean_inc(v_toBind_1038_);
lean_dec_ref(v_inst_1033_);
v___f_1039_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1039_, 0, v_toApplicative_1037_);
lean_closure_set(v___f_1039_, 1, v_place_1035_);
lean_inc(v_a_1036_);
v___x_1040_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1040_, 0, lean_box(0));
lean_closure_set(v___x_1040_, 1, lean_box(0));
lean_closure_set(v___x_1040_, 2, v_a_1036_);
v___x_1041_ = lean_apply_2(v_inst_1034_, lean_box(0), v___x_1040_);
v___x_1042_ = lean_apply_4(v_toBind_1038_, lean_box(0), lean_box(0), v___x_1041_, v___f_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___boxed(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_place_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1043_, v_inst_1044_, v_place_1045_, v_a_1046_);
lean_dec(v_a_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(lean_object* v_m_1048_, lean_object* v_00_u03b1_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_place_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1050_, v_inst_1051_, v_place_1052_, v_a_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___boxed(lean_object* v_m_1055_, lean_object* v_00_u03b1_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, lean_object* v_place_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(v_m_1055_, v_00_u03b1_1056_, v_inst_1057_, v_inst_1058_, v_place_1059_, v_a_1060_);
lean_dec(v_a_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(lean_object* v_as_1062_, size_t v_sz_1063_, size_t v_i_1064_, lean_object* v_b_1065_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_usize_dec_lt(v_i_1064_, v_sz_1063_);
if (v___x_1067_ == 0)
{
return v_b_1065_;
}
else
{
lean_object* v___x_1068_; lean_object* v_a_1069_; lean_object* v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; 
v___x_1068_ = lean_box(0);
v_a_1069_ = lean_array_uget_borrowed(v_as_1062_, v_i_1064_);
v___x_1070_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1069_, v___x_1067_);
v___x_1071_ = ((size_t)1ULL);
v___x_1072_ = lean_usize_add(v_i_1064_, v___x_1071_);
v_i_1064_ = v___x_1072_;
v_b_1065_ = v___x_1068_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg___boxed(lean_object* v_as_1074_, lean_object* v_sz_1075_, lean_object* v_i_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_){
_start:
{
size_t v_sz_boxed_1079_; size_t v_i_boxed_1080_; lean_object* v_res_1081_; 
v_sz_boxed_1079_ = lean_unbox_usize(v_sz_1075_);
lean_dec(v_sz_1075_);
v_i_boxed_1080_ = lean_unbox_usize(v_i_1076_);
lean_dec(v_i_1076_);
v_res_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1074_, v_sz_boxed_1079_, v_i_boxed_1080_, v_b_1077_);
lean_dec_ref(v_as_1074_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(lean_object* v_v_1082_, lean_object* v_a_1083_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_1083_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_producers_1088_; lean_object* v_waiters_1089_; lean_object* v_capacity_1090_; lean_object* v_size_1091_; lean_object* v_buffer_1092_; lean_object* v_write_1093_; lean_object* v_read_1094_; lean_object* v_receivers_1095_; lean_object* v_nextId_1096_; uint8_t v_closed_1097_; lean_object* v_pos_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1117_; 
v___x_1086_ = lean_st_ref_get(v_a_1083_);
v___x_1087_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_v_1082_, v___x_1086_);
v_producers_1088_ = lean_ctor_get(v___x_1087_, 0);
v_waiters_1089_ = lean_ctor_get(v___x_1087_, 1);
v_capacity_1090_ = lean_ctor_get(v___x_1087_, 2);
v_size_1091_ = lean_ctor_get(v___x_1087_, 3);
v_buffer_1092_ = lean_ctor_get(v___x_1087_, 4);
v_write_1093_ = lean_ctor_get(v___x_1087_, 5);
v_read_1094_ = lean_ctor_get(v___x_1087_, 6);
v_receivers_1095_ = lean_ctor_get(v___x_1087_, 7);
v_nextId_1096_ = lean_ctor_get(v___x_1087_, 8);
v_closed_1097_ = lean_ctor_get_uint8(v___x_1087_, sizeof(void*)*10);
v_pos_1098_ = lean_ctor_get(v___x_1087_, 9);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1100_ = v___x_1087_;
v_isShared_1101_ = v_isSharedCheck_1117_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_pos_1098_);
lean_inc(v_nextId_1096_);
lean_inc(v_receivers_1095_);
lean_inc(v_read_1094_);
lean_inc(v_write_1093_);
lean_inc(v_buffer_1092_);
lean_inc(v_size_1091_);
lean_inc(v_capacity_1090_);
lean_inc(v_waiters_1089_);
lean_inc(v_producers_1088_);
lean_dec(v___x_1087_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1117_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1102_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
lean_inc(v_receivers_1095_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v___x_1102_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_producers_1088_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_capacity_1090_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_size_1091_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_buffer_1092_);
lean_ctor_set(v_reuseFailAlloc_1116_, 5, v_write_1093_);
lean_ctor_set(v_reuseFailAlloc_1116_, 6, v_read_1094_);
lean_ctor_set(v_reuseFailAlloc_1116_, 7, v_receivers_1095_);
lean_ctor_set(v_reuseFailAlloc_1116_, 8, v_nextId_1096_);
lean_ctor_set(v_reuseFailAlloc_1116_, 9, v_pos_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1116_, sizeof(void*)*10, v_closed_1097_);
v___x_1104_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; size_t v_sz_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___y_1112_; 
v___x_1105_ = lean_st_ref_swap(v_a_1083_, v___x_1104_);
lean_dec(v___x_1105_);
v___x_1106_ = l_Std_Queue_toArray___redArg(v_waiters_1089_);
v___x_1107_ = lean_box(0);
v_sz_1108_ = lean_array_size(v___x_1106_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v___x_1106_, v_sz_1108_, v___x_1109_, v___x_1107_);
lean_dec_ref(v___x_1106_);
if (lean_obj_tag(v_receivers_1095_) == 0)
{
lean_object* v_size_1114_; 
v_size_1114_ = lean_ctor_get(v_receivers_1095_, 0);
lean_inc(v_size_1114_);
lean_dec_ref_known(v_receivers_1095_, 5);
v___y_1112_ = v_size_1114_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_unsigned_to_nat(0u);
v___y_1112_ = v___x_1115_;
goto v___jp_1111_;
}
v___jp_1111_:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___y_1112_);
return v___x_1113_;
}
}
}
}
else
{
lean_object* v___x_1118_; 
lean_dec(v_v_1082_);
v___x_1118_ = lean_box(0);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1119_, v_a_1120_);
lean_dec(v_a_1120_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(lean_object* v_00_u03b1_1123_, lean_object* v_v_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1124_, v_a_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_1128_, lean_object* v_v_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(v_00_u03b1_1128_, v_v_1129_, v_a_1130_);
lean_dec(v_a_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(lean_object* v_00_u03b1_1133_, lean_object* v_as_1134_, size_t v_sz_1135_, size_t v_i_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1134_, v_sz_1135_, v_i_1136_, v_b_1137_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_as_1142_, lean_object* v_sz_1143_, lean_object* v_i_1144_, lean_object* v_b_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
size_t v_sz_boxed_1148_; size_t v_i_boxed_1149_; lean_object* v_res_1150_; 
v_sz_boxed_1148_ = lean_unbox_usize(v_sz_1143_);
lean_dec(v_sz_1143_);
v_i_boxed_1149_ = lean_unbox_usize(v_i_1144_);
lean_dec(v_i_1144_);
v_res_1150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(v_00_u03b1_1141_, v_as_1142_, v_sz_boxed_1148_, v_i_boxed_1149_, v_b_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v_as_1142_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(lean_object* v_mutex_1151_, lean_object* v_k_1152_){
_start:
{
lean_object* v_ref_1154_; lean_object* v_mutex_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_ref_1154_ = lean_ctor_get(v_mutex_1151_, 0);
lean_inc(v_ref_1154_);
v_mutex_1155_ = lean_ctor_get(v_mutex_1151_, 1);
lean_inc(v_mutex_1155_);
lean_dec_ref(v_mutex_1151_);
v___x_1156_ = lean_io_basemutex_lock(v_mutex_1155_);
v___x_1157_ = lean_apply_2(v_k_1152_, v_ref_1154_, lean_box(0));
v___x_1158_ = lean_io_basemutex_unlock(v_mutex_1155_);
lean_dec(v_mutex_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg___boxed(lean_object* v_mutex_1159_, lean_object* v_k_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1159_, v_k_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_mutex_1165_, lean_object* v_k_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1165_, v_k_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_mutex_1171_, lean_object* v_k_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(v_00_u03b1_1169_, v_00_u03b2_1170_, v_mutex_1171_, v_k_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(lean_object* v_v_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; uint8_t v_closed_1181_; 
v___x_1180_ = lean_st_ref_get(v___y_1178_);
v_closed_1181_ = lean_ctor_get_uint8(v___x_1180_, sizeof(void*)*10);
lean_dec(v___x_1180_);
if (v_closed_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v_receivers_1183_; 
v___x_1182_ = lean_st_ref_get(v___y_1178_);
v_receivers_1183_ = lean_ctor_get(v___x_1182_, 7);
lean_inc(v_receivers_1183_);
lean_dec(v___x_1182_);
if (lean_obj_tag(v_receivers_1183_) == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref_known(v_receivers_1183_, 5);
v___x_1184_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1177_, v___y_1178_);
return v___x_1184_;
}
else
{
lean_object* v___x_1185_; 
lean_dec(v_v_1177_);
v___x_1185_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0));
return v___x_1185_;
}
}
else
{
lean_object* v___x_1186_; 
lean_dec(v_v_1177_);
v___x_1186_ = lean_box(0);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(v_v_1187_, v___y_1188_);
lean_dec(v___y_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(lean_object* v_ch_1191_, lean_object* v_v_1192_){
_start:
{
lean_object* v___f_1194_; lean_object* v___x_1195_; 
v___f_1194_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1194_, 0, v_v_1192_);
v___x_1195_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1191_, v___f_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___boxed(lean_object* v_ch_1196_, lean_object* v_v_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1196_, v_v_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(lean_object* v_00_u03b1_1200_, lean_object* v_ch_1201_, lean_object* v_v_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1201_, v_v_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_ch_1206_, lean_object* v_v_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(v_00_u03b1_1205_, v_ch_1206_, v_v_1207_);
return v_res_1209_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0));
v___x_1213_ = lean_task_pure(v___x_1212_);
return v___x_1213_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2));
v___x_1218_ = lean_task_pure(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(lean_object* v_v_1219_, lean_object* v___f_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; uint8_t v_closed_1224_; 
v___x_1223_ = lean_st_ref_get(v___y_1221_);
v_closed_1224_ = lean_ctor_get_uint8(v___x_1223_, sizeof(void*)*10);
lean_dec(v___x_1223_);
if (v_closed_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v_receivers_1226_; 
v___x_1225_ = lean_st_ref_get(v___y_1221_);
v_receivers_1226_ = lean_ctor_get(v___x_1225_, 7);
lean_inc(v_receivers_1226_);
lean_dec(v___x_1225_);
if (lean_obj_tag(v_receivers_1226_) == 0)
{
lean_object* v___x_1227_; 
lean_dec_ref_known(v_receivers_1226_, 5);
v___x_1227_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1219_, v___y_1221_);
if (lean_obj_tag(v___x_1227_) == 1)
{
lean_object* v_val_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v___f_1220_);
v_val_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_val_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_val_1228_);
v___x_1233_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_task_pure(v___x_1233_);
return v___x_1234_;
}
}
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_producers_1239_; lean_object* v_waiters_1240_; lean_object* v_capacity_1241_; lean_object* v_size_1242_; lean_object* v_buffer_1243_; lean_object* v_write_1244_; lean_object* v_read_1245_; lean_object* v_receivers_1246_; lean_object* v_nextId_1247_; uint8_t v_closed_1248_; lean_object* v_pos_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v___x_1227_);
v___x_1237_ = lean_io_promise_new();
v___x_1238_ = lean_st_ref_take(v___y_1221_);
v_producers_1239_ = lean_ctor_get(v___x_1238_, 0);
v_waiters_1240_ = lean_ctor_get(v___x_1238_, 1);
v_capacity_1241_ = lean_ctor_get(v___x_1238_, 2);
v_size_1242_ = lean_ctor_get(v___x_1238_, 3);
v_buffer_1243_ = lean_ctor_get(v___x_1238_, 4);
v_write_1244_ = lean_ctor_get(v___x_1238_, 5);
v_read_1245_ = lean_ctor_get(v___x_1238_, 6);
v_receivers_1246_ = lean_ctor_get(v___x_1238_, 7);
v_nextId_1247_ = lean_ctor_get(v___x_1238_, 8);
v_closed_1248_ = lean_ctor_get_uint8(v___x_1238_, sizeof(void*)*10);
v_pos_1249_ = lean_ctor_get(v___x_1238_, 9);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1251_ = v___x_1238_;
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_pos_1249_);
lean_inc(v_nextId_1247_);
lean_inc(v_receivers_1246_);
lean_inc(v_read_1245_);
lean_inc(v_write_1244_);
lean_inc(v_buffer_1243_);
lean_inc(v_size_1242_);
lean_inc(v_capacity_1241_);
lean_inc(v_waiters_1240_);
lean_inc(v_producers_1239_);
lean_dec(v___x_1238_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1261_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_inc(v___x_1237_);
v___x_1253_ = l_Std_Queue_enqueue___redArg(v___x_1237_, v_producers_1239_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_waiters_1240_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_capacity_1241_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_size_1242_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_buffer_1243_);
lean_ctor_set(v_reuseFailAlloc_1260_, 5, v_write_1244_);
lean_ctor_set(v_reuseFailAlloc_1260_, 6, v_read_1245_);
lean_ctor_set(v_reuseFailAlloc_1260_, 7, v_receivers_1246_);
lean_ctor_set(v_reuseFailAlloc_1260_, 8, v_nextId_1247_);
lean_ctor_set(v_reuseFailAlloc_1260_, 9, v_pos_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1260_, sizeof(void*)*10, v_closed_1248_);
v___x_1255_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = lean_st_ref_put(v___y_1221_, v___x_1255_);
v___x_1257_ = lean_io_promise_result_opt(v___x_1237_);
lean_dec(v___x_1237_);
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_io_bind_task(v___x_1257_, v___f_1220_, v___x_1258_, v_closed_1224_);
return v___x_1259_;
}
}
}
}
else
{
lean_object* v___x_1262_; 
lean_dec_ref(v___f_1220_);
lean_dec(v_v_1219_);
v___x_1262_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1);
return v___x_1262_;
}
}
else
{
lean_object* v___x_1263_; 
lean_dec_ref(v___f_1220_);
lean_dec(v_v_1219_);
v___x_1263_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_1264_, lean_object* v___f_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(v_v_1264_, v___f_1265_, v___y_1266_);
lean_dec(v___y_1266_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(lean_object* v_ch_1269_, lean_object* v_v_1270_, lean_object* v_res_1271_){
_start:
{
if (lean_obj_tag(v_res_1271_) == 0)
{
lean_dec(v_v_1270_);
lean_dec_ref(v_ch_1269_);
goto v___jp_1273_;
}
else
{
lean_object* v_val_1275_; uint8_t v___x_1276_; 
v_val_1275_ = lean_ctor_get(v_res_1271_, 0);
v___x_1276_ = lean_unbox(v_val_1275_);
if (v___x_1276_ == 0)
{
lean_dec(v_v_1270_);
lean_dec_ref(v_ch_1269_);
goto v___jp_1273_;
}
else
{
lean_object* v___x_1277_; 
v___x_1277_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1269_, v_v_1270_);
return v___x_1277_;
}
}
v___jp_1273_:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_1278_, lean_object* v_v_1279_, lean_object* v_res_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(v_ch_1278_, v_v_1279_, v_res_1280_);
lean_dec(v_res_1280_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(lean_object* v_ch_1283_, lean_object* v_v_1284_){
_start:
{
lean_object* v___f_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; 
lean_inc(v_v_1284_);
lean_inc_ref(v_ch_1283_);
v___f_1286_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1286_, 0, v_ch_1283_);
lean_closure_set(v___f_1286_, 1, v_v_1284_);
v___f_1287_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1287_, 0, v_v_1284_);
lean_closure_set(v___f_1287_, 1, v___f_1286_);
v___x_1288_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1283_, v___f_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___boxed(lean_object* v_ch_1289_, lean_object* v_v_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1289_, v_v_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send(lean_object* v_00_u03b1_1293_, lean_object* v_ch_1294_, lean_object* v_v_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1294_, v_v_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___boxed(lean_object* v_00_u03b1_1298_, lean_object* v_ch_1299_, lean_object* v_v_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send(v_00_u03b1_1298_, v_ch_1299_, v_v_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(lean_object* v_mutex_1303_, lean_object* v_k_1304_){
_start:
{
lean_object* v_ref_1306_; lean_object* v_mutex_1307_; lean_object* v___x_1308_; lean_object* v_r_1309_; 
v_ref_1306_ = lean_ctor_get(v_mutex_1303_, 0);
lean_inc(v_ref_1306_);
v_mutex_1307_ = lean_ctor_get(v_mutex_1303_, 1);
lean_inc(v_mutex_1307_);
lean_dec_ref(v_mutex_1303_);
v___x_1308_ = lean_io_basemutex_lock(v_mutex_1307_);
v_r_1309_ = lean_apply_2(v_k_1304_, v_ref_1306_, lean_box(0));
if (lean_obj_tag(v_r_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
v_a_1310_ = lean_ctor_get(v_r_1309_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_r_1309_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1312_ = v_r_1309_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v_r_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_io_basemutex_unlock(v_mutex_1307_);
lean_dec(v_mutex_1307_);
if (v_isShared_1313_ == 0)
{
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1310_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_a_1319_ = lean_ctor_get(v_r_1309_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_r_1309_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1321_ = v_r_1309_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v_r_1309_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_io_basemutex_unlock(v_mutex_1307_);
lean_dec(v_mutex_1307_);
if (v_isShared_1322_ == 0)
{
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1319_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg___boxed(lean_object* v_mutex_1328_, lean_object* v_k_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_mutex_1328_, v_k_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2(lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_mutex_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_mutex_1334_, v_k_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_mutex_1340_, lean_object* v_k_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2(v_00_u03b1_1338_, v_00_u03b2_1339_, v_mutex_1340_, v_k_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(uint8_t v___x_1344_, lean_object* v_as_1345_, size_t v_sz_1346_, size_t v_i_1347_, lean_object* v_b_1348_){
_start:
{
uint8_t v___x_1350_; 
v___x_1350_ = lean_usize_dec_lt(v_i_1347_, v_sz_1346_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_b_1348_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; 
v___x_1352_ = lean_box(0);
v_a_1353_ = lean_array_uget_borrowed(v_as_1345_, v_i_1347_);
v___x_1354_ = lean_box(v___x_1344_);
v___x_1355_ = lean_io_promise_resolve(v___x_1354_, v_a_1353_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_i_1347_, v___x_1356_);
v_i_1347_ = v___x_1357_;
v_b_1348_ = v___x_1352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object* v___x_1359_, lean_object* v_as_1360_, lean_object* v_sz_1361_, lean_object* v_i_1362_, lean_object* v_b_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v___x_2113__boxed_1365_; size_t v_sz_boxed_1366_; size_t v_i_boxed_1367_; lean_object* v_res_1368_; 
v___x_2113__boxed_1365_ = lean_unbox(v___x_1359_);
v_sz_boxed_1366_ = lean_unbox_usize(v_sz_1361_);
lean_dec(v_sz_1361_);
v_i_boxed_1367_ = lean_unbox_usize(v_i_1362_);
lean_dec(v_i_1362_);
v_res_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v___x_2113__boxed_1365_, v_as_1360_, v_sz_boxed_1366_, v_i_boxed_1367_, v_b_1363_);
lean_dec_ref(v_as_1360_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(uint8_t v___x_1369_, lean_object* v_as_1370_, size_t v_sz_1371_, size_t v_i_1372_, lean_object* v_b_1373_){
_start:
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_usize_dec_lt(v_i_1372_, v_sz_1371_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_b_1373_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; lean_object* v_a_1378_; lean_object* v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; 
v___x_1377_ = lean_box(0);
v_a_1378_ = lean_array_uget_borrowed(v_as_1370_, v_i_1372_);
v___x_1379_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1378_, v___x_1369_);
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1372_, v___x_1380_);
v_i_1372_ = v___x_1381_;
v_b_1373_ = v___x_1377_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_1383_, lean_object* v_as_1384_, lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v___x_2135__boxed_1389_; size_t v_sz_boxed_1390_; size_t v_i_boxed_1391_; lean_object* v_res_1392_; 
v___x_2135__boxed_1389_ = lean_unbox(v___x_1383_);
v_sz_boxed_1390_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1391_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_2135__boxed_1389_, v_as_1384_, v_sz_boxed_1390_, v_i_boxed_1391_, v_b_1387_);
lean_dec_ref(v_as_1384_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; uint8_t v_closed_1396_; 
v___x_1395_ = lean_st_ref_get(v___y_1393_);
v_closed_1396_ = lean_ctor_get_uint8(v___x_1395_, sizeof(void*)*10);
if (v_closed_1396_ == 0)
{
lean_object* v_producers_1397_; lean_object* v_waiters_1398_; lean_object* v_capacity_1399_; lean_object* v_size_1400_; lean_object* v_buffer_1401_; lean_object* v_write_1402_; lean_object* v_read_1403_; lean_object* v_receivers_1404_; lean_object* v_nextId_1405_; lean_object* v_pos_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1432_; 
v_producers_1397_ = lean_ctor_get(v___x_1395_, 0);
v_waiters_1398_ = lean_ctor_get(v___x_1395_, 1);
v_capacity_1399_ = lean_ctor_get(v___x_1395_, 2);
v_size_1400_ = lean_ctor_get(v___x_1395_, 3);
v_buffer_1401_ = lean_ctor_get(v___x_1395_, 4);
v_write_1402_ = lean_ctor_get(v___x_1395_, 5);
v_read_1403_ = lean_ctor_get(v___x_1395_, 6);
v_receivers_1404_ = lean_ctor_get(v___x_1395_, 7);
v_nextId_1405_ = lean_ctor_get(v___x_1395_, 8);
v_pos_1406_ = lean_ctor_get(v___x_1395_, 9);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1408_ = v___x_1395_;
v_isShared_1409_ = v_isSharedCheck_1432_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_pos_1406_);
lean_inc(v_nextId_1405_);
lean_inc(v_receivers_1404_);
lean_inc(v_read_1403_);
lean_inc(v_write_1402_);
lean_inc(v_buffer_1401_);
lean_inc(v_size_1400_);
lean_inc(v_capacity_1399_);
lean_inc(v_waiters_1398_);
lean_inc(v_producers_1397_);
lean_dec(v___x_1395_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1432_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; size_t v_sz_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1410_ = l_Std_Queue_toArray___redArg(v_waiters_1398_);
v___x_1411_ = lean_box(0);
v_sz_1412_ = lean_array_size(v___x_1410_);
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v_closed_1396_, v___x_1410_, v_sz_1412_, v___x_1413_, v___x_1411_);
lean_dec_ref(v___x_1410_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1415_; size_t v_sz_1416_; lean_object* v___x_1417_; 
lean_dec_ref_known(v___x_1414_, 1);
v___x_1415_ = l_Std_Queue_toArray___redArg(v_producers_1397_);
v_sz_1416_ = lean_array_size(v___x_1415_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_closed_1396_, v___x_1415_, v_sz_1416_, v___x_1413_, v___x_1411_);
lean_dec_ref(v___x_1415_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1430_; 
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v___x_1417_, 0);
lean_dec(v_unused_1431_);
v___x_1419_ = v___x_1417_;
v_isShared_1420_ = v_isSharedCheck_1430_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v___x_1417_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1430_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1424_; 
v___x_1421_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_1422_ = 1;
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v___x_1421_);
lean_ctor_set(v___x_1408_, 0, v___x_1421_);
v___x_1424_ = v___x_1408_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_capacity_1399_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_size_1400_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v_buffer_1401_);
lean_ctor_set(v_reuseFailAlloc_1429_, 5, v_write_1402_);
lean_ctor_set(v_reuseFailAlloc_1429_, 6, v_read_1403_);
lean_ctor_set(v_reuseFailAlloc_1429_, 7, v_receivers_1404_);
lean_ctor_set(v_reuseFailAlloc_1429_, 8, v_nextId_1405_);
lean_ctor_set(v_reuseFailAlloc_1429_, 9, v_pos_1406_);
v___x_1424_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_ctor_set_uint8(v___x_1424_, sizeof(void*)*10, v___x_1422_);
v___x_1425_ = lean_st_ref_swap(v___y_1393_, v___x_1424_);
lean_dec(v___x_1425_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1411_);
v___x_1427_ = v___x_1419_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1411_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_del_object(v___x_1408_);
lean_dec(v_pos_1406_);
lean_dec(v_nextId_1405_);
lean_dec(v_receivers_1404_);
lean_dec(v_read_1403_);
lean_dec(v_write_1402_);
lean_dec_ref(v_buffer_1401_);
lean_dec(v_size_1400_);
lean_dec(v_capacity_1399_);
return v___x_1417_;
}
}
else
{
lean_del_object(v___x_1408_);
lean_dec(v_pos_1406_);
lean_dec(v_nextId_1405_);
lean_dec(v_receivers_1404_);
lean_dec(v_read_1403_);
lean_dec(v_write_1402_);
lean_dec_ref(v_buffer_1401_);
lean_dec(v_size_1400_);
lean_dec(v_capacity_1399_);
lean_dec_ref(v_producers_1397_);
return v___x_1414_;
}
}
}
else
{
uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec(v___x_1395_);
v___x_1433_ = 1;
v___x_1434_ = lean_box(v___x_1433_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(v___y_1436_);
lean_dec(v___y_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(lean_object* v_ch_1440_){
_start:
{
lean_object* v___f_1442_; lean_object* v___x_1443_; 
v___f_1442_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0));
v___x_1443_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_ch_1440_, v___f_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___boxed(lean_object* v_ch_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_object* v_00_u03b1_1447_, lean_object* v_ch_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_ch_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close(v_00_u03b1_1451_, v_ch_1452_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_object* v_00_u03b1_1455_, uint8_t v___x_1456_, lean_object* v_as_1457_, size_t v_sz_1458_, size_t v_i_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1456_, v_as_1457_, v_sz_1458_, v_i_1459_, v_b_1460_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_1464_, lean_object* v___x_1465_, lean_object* v_as_1466_, lean_object* v_sz_1467_, lean_object* v_i_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
uint8_t v___x_2237__boxed_1472_; size_t v_sz_boxed_1473_; size_t v_i_boxed_1474_; lean_object* v_res_1475_; 
v___x_2237__boxed_1472_ = lean_unbox(v___x_1465_);
v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1467_);
lean_dec(v_sz_1467_);
v_i_boxed_1474_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1464_, v___x_2237__boxed_1472_, v_as_1466_, v_sz_boxed_1473_, v_i_boxed_1474_, v_b_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v_as_1466_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object* v_00_u03b1_1476_, uint8_t v___x_1477_, lean_object* v_as_1478_, size_t v_sz_1479_, size_t v_i_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v___x_1477_, v_as_1478_, v_sz_1479_, v_i_1480_, v_b_1481_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_1485_, lean_object* v___x_1486_, lean_object* v_as_1487_, lean_object* v_sz_1488_, lean_object* v_i_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v___x_2248__boxed_1493_; size_t v_sz_boxed_1494_; size_t v_i_boxed_1495_; lean_object* v_res_1496_; 
v___x_2248__boxed_1493_ = lean_unbox(v___x_1486_);
v_sz_boxed_1494_ = lean_unbox_usize(v_sz_1488_);
lean_dec(v_sz_1488_);
v_i_boxed_1495_ = lean_unbox_usize(v_i_1489_);
lean_dec(v_i_1489_);
v_res_1496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(v_00_u03b1_1485_, v___x_2248__boxed_1493_, v_as_1487_, v_sz_boxed_1494_, v_i_boxed_1495_, v_b_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v_as_1487_);
return v_res_1496_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; uint8_t v_closed_1500_; 
v___x_1499_ = lean_st_ref_get(v___y_1497_);
v_closed_1500_ = lean_ctor_get_uint8(v___x_1499_, sizeof(void*)*10);
lean_dec(v___x_1499_);
return v_closed_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_res_1503_; lean_object* v_r_1504_; 
v_res_1503_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(v___y_1501_);
lean_dec(v___y_1501_);
v_r_1504_ = lean_box(v_res_1503_);
return v_r_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object* v_ch_1506_){
_start:
{
lean_object* v___f_1508_; lean_object* v___x_1509_; 
v___f_1508_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0));
v___x_1509_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1506_, v___f_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___boxed(lean_object* v_ch_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_object* v_00_u03b1_1513_, lean_object* v_ch_1514_){
_start:
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1514_);
v___x_1517_ = lean_unbox(v___x_1516_);
lean_dec(v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___boxed(lean_object* v_00_u03b1_1518_, lean_object* v_ch_1519_, lean_object* v_a_1520_){
_start:
{
uint8_t v_res_1521_; lean_object* v_r_1522_; 
v_res_1521_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(v_00_u03b1_1518_, v_ch_1519_);
v_r_1522_ = lean_box(v_res_1521_);
return v_r_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object* v_next_1523_, lean_object* v_slot_1524_){
_start:
{
lean_object* v_value_1525_; lean_object* v_pos_1526_; lean_object* v_remaining_1527_; uint8_t v___x_1528_; 
v_value_1525_ = lean_ctor_get(v_slot_1524_, 0);
v_pos_1526_ = lean_ctor_get(v_slot_1524_, 1);
v_remaining_1527_ = lean_ctor_get(v_slot_1524_, 2);
v___x_1528_ = lean_nat_dec_eq(v_next_1523_, v_pos_1526_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_box(v___x_1528_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_slot_1524_);
return v___x_1532_;
}
else
{
lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1553_; 
lean_inc(v_remaining_1527_);
lean_inc(v_pos_1526_);
lean_inc(v_value_1525_);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_slot_1524_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; lean_object* v_unused_1555_; lean_object* v_unused_1556_; 
v_unused_1554_ = lean_ctor_get(v_slot_1524_, 2);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_slot_1524_, 1);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_slot_1524_, 0);
lean_dec(v_unused_1556_);
v___x_1534_ = v_slot_1524_;
v_isShared_1535_ = v_isSharedCheck_1553_;
goto v_resetjp_1533_;
}
else
{
lean_dec(v_slot_1524_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1553_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_dec_eq(v_remaining_1527_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1538_ = lean_box(v___x_1537_);
lean_inc(v_value_1525_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_value_1525_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_nat_sub(v_remaining_1527_, v___x_1536_);
lean_dec(v_remaining_1527_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 2, v___x_1540_);
v___x_1542_ = v___x_1534_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_value_1525_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_pos_1526_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1539_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
return v___x_1543_;
}
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
lean_dec(v_remaining_1527_);
v___x_1545_ = lean_box(v___x_1528_);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_value_1525_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_box(0);
v___x_1548_ = lean_unsigned_to_nat(0u);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 2, v___x_1548_);
lean_ctor_set(v___x_1534_, 0, v___x_1547_);
v___x_1550_ = v___x_1534_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_pos_1526_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1546_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
return v___x_1551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object* v_next_1557_, lean_object* v_slot_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(v_next_1557_, v_slot_1558_);
lean_dec(v_next_1557_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object* v_inst_1560_, lean_object* v_slot_1561_, lean_object* v_next_1562_){
_start:
{
lean_object* v___f_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___f_1563_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1563_, 0, v_next_1562_);
v___x_1564_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1564_, 0, lean_box(0));
lean_closure_set(v___x_1564_, 1, lean_box(0));
lean_closure_set(v___x_1564_, 2, lean_box(0));
lean_closure_set(v___x_1564_, 3, v_slot_1561_);
lean_closure_set(v___x_1564_, 4, v___f_1563_);
v___x_1565_ = lean_apply_2(v_inst_1560_, lean_box(0), v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object* v_m_1566_, lean_object* v_00_u03b1_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_slot_1570_, lean_object* v_next_1571_, lean_object* v_a_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1569_, v_slot_1570_, v_next_1571_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object* v_m_1574_, lean_object* v_00_u03b1_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_slot_1578_, lean_object* v_next_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(v_m_1574_, v_00_u03b1_1575_, v_inst_1576_, v_inst_1577_, v_slot_1578_, v_next_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_inst_1576_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object* v_toApplicative_1582_, lean_object* v_fst_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_toPure_1585_; lean_object* v___x_1586_; 
v_toPure_1585_ = lean_ctor_get(v_toApplicative_1582_, 1);
lean_inc(v_toPure_1585_);
lean_dec_ref(v_toApplicative_1582_);
v___x_1586_ = lean_apply_2(v_toPure_1585_, lean_box(0), v_fst_1583_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object* v_inst_1587_, lean_object* v_toBind_1588_, lean_object* v___f_1589_, lean_object* v_____r_1590_, lean_object* v_st_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_inc(v___y_1592_);
v___x_1593_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1593_, 0, lean_box(0));
lean_closure_set(v___x_1593_, 1, lean_box(0));
lean_closure_set(v___x_1593_, 2, v___y_1592_);
lean_closure_set(v___x_1593_, 3, v_st_1591_);
v___x_1594_ = lean_apply_2(v_inst_1587_, lean_box(0), v___x_1593_);
v___x_1595_ = lean_apply_4(v_toBind_1588_, lean_box(0), lean_box(0), v___x_1594_, v___f_1589_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed(lean_object* v_inst_1596_, lean_object* v_toBind_1597_, lean_object* v___f_1598_, lean_object* v_____r_1599_, lean_object* v_st_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1596_, v_toBind_1597_, v___f_1598_, v_____r_1599_, v_st_1600_, v___y_1601_);
lean_dec(v___y_1601_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object* v_snd_1603_, lean_object* v_waiters_1604_, lean_object* v_capacity_1605_, lean_object* v_size_1606_, lean_object* v_buffer_1607_, lean_object* v_write_1608_, lean_object* v_read_1609_, lean_object* v_receivers_1610_, lean_object* v_nextId_1611_, uint8_t v_closed_1612_, lean_object* v_pos_1613_, lean_object* v___f_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1617_, 0, v_snd_1603_);
lean_ctor_set(v___x_1617_, 1, v_waiters_1604_);
lean_ctor_set(v___x_1617_, 2, v_capacity_1605_);
lean_ctor_set(v___x_1617_, 3, v_size_1606_);
lean_ctor_set(v___x_1617_, 4, v_buffer_1607_);
lean_ctor_set(v___x_1617_, 5, v_write_1608_);
lean_ctor_set(v___x_1617_, 6, v_read_1609_);
lean_ctor_set(v___x_1617_, 7, v_receivers_1610_);
lean_ctor_set(v___x_1617_, 8, v_nextId_1611_);
lean_ctor_set(v___x_1617_, 9, v_pos_1613_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*10, v_closed_1612_);
v___x_1618_ = lean_box(0);
lean_inc(v_a_1615_);
v___x_1619_ = lean_apply_3(v___f_1614_, v___x_1618_, v___x_1617_, v_a_1615_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object* v_snd_1620_, lean_object* v_waiters_1621_, lean_object* v_capacity_1622_, lean_object* v_size_1623_, lean_object* v_buffer_1624_, lean_object* v_write_1625_, lean_object* v_read_1626_, lean_object* v_receivers_1627_, lean_object* v_nextId_1628_, lean_object* v_closed_1629_, lean_object* v_pos_1630_, lean_object* v___f_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
uint8_t v_closed_boxed_1634_; lean_object* v_res_1635_; 
v_closed_boxed_1634_ = lean_unbox(v_closed_1629_);
v_res_1635_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1620_, v_waiters_1621_, v_capacity_1622_, v_size_1623_, v_buffer_1624_, v_write_1625_, v_read_1626_, v_receivers_1627_, v_nextId_1628_, v_closed_boxed_1634_, v_pos_1630_, v___f_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1632_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object* v_toApplicative_1636_, lean_object* v_inst_1637_, lean_object* v_toBind_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, uint8_t v___x_1641_, lean_object* v_inst_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_fst_1644_; 
v_fst_1644_ = lean_ctor_get(v_a_1643_, 0);
lean_inc(v_fst_1644_);
if (lean_obj_tag(v_fst_1644_) == 1)
{
lean_object* v_snd_1645_; lean_object* v___f_1646_; lean_object* v___f_1647_; uint8_t v___x_1648_; 
v_snd_1645_ = lean_ctor_get(v_a_1643_, 1);
lean_inc(v_snd_1645_);
lean_dec_ref(v_a_1643_);
v___f_1646_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1646_, 0, v_toApplicative_1636_);
lean_closure_set(v___f_1646_, 1, v_fst_1644_);
lean_inc_ref(v___f_1646_);
lean_inc(v_toBind_1638_);
lean_inc(v_inst_1637_);
v___f_1647_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1647_, 0, v_inst_1637_);
lean_closure_set(v___f_1647_, 1, v_toBind_1638_);
lean_closure_set(v___f_1647_, 2, v___f_1646_);
v___x_1648_ = lean_unbox(v_snd_1645_);
lean_dec(v_snd_1645_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v___f_1647_);
lean_dec(v_inst_1642_);
v___x_1649_ = lean_box(0);
v___x_1650_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1637_, v_toBind_1638_, v___f_1646_, v___x_1649_, v_a_1639_, v_a_1640_);
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; lean_object* v_producers_1652_; lean_object* v_waiters_1653_; lean_object* v_capacity_1654_; lean_object* v_size_1655_; lean_object* v_buffer_1656_; lean_object* v_write_1657_; lean_object* v_read_1658_; lean_object* v_receivers_1659_; lean_object* v_nextId_1660_; uint8_t v_closed_1661_; lean_object* v_pos_1662_; lean_object* v___x_1663_; 
v___x_1651_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_1639_);
v_producers_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc_ref(v_producers_1652_);
v_waiters_1653_ = lean_ctor_get(v___x_1651_, 1);
lean_inc_ref(v_waiters_1653_);
v_capacity_1654_ = lean_ctor_get(v___x_1651_, 2);
lean_inc(v_capacity_1654_);
v_size_1655_ = lean_ctor_get(v___x_1651_, 3);
lean_inc(v_size_1655_);
v_buffer_1656_ = lean_ctor_get(v___x_1651_, 4);
lean_inc_ref(v_buffer_1656_);
v_write_1657_ = lean_ctor_get(v___x_1651_, 5);
lean_inc(v_write_1657_);
v_read_1658_ = lean_ctor_get(v___x_1651_, 6);
lean_inc(v_read_1658_);
v_receivers_1659_ = lean_ctor_get(v___x_1651_, 7);
lean_inc(v_receivers_1659_);
v_nextId_1660_ = lean_ctor_get(v___x_1651_, 8);
lean_inc(v_nextId_1660_);
v_closed_1661_ = lean_ctor_get_uint8(v___x_1651_, sizeof(void*)*10);
v_pos_1662_ = lean_ctor_get(v___x_1651_, 9);
lean_inc(v_pos_1662_);
v___x_1663_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1652_);
if (lean_obj_tag(v___x_1663_) == 1)
{
lean_object* v_val_1664_; lean_object* v_fst_1665_; lean_object* v_snd_1666_; lean_object* v___x_1667_; lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec_ref(v___x_1651_);
lean_dec_ref(v___f_1646_);
lean_dec(v_inst_1637_);
v_val_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_val_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v_fst_1665_ = lean_ctor_get(v_val_1664_, 0);
lean_inc(v_fst_1665_);
v_snd_1666_ = lean_ctor_get(v_val_1664_, 1);
lean_inc(v_snd_1666_);
lean_dec(v_val_1664_);
v___x_1667_ = lean_box(v_closed_1661_);
lean_inc(v_a_1640_);
v___f_1668_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1668_, 0, v_snd_1666_);
lean_closure_set(v___f_1668_, 1, v_waiters_1653_);
lean_closure_set(v___f_1668_, 2, v_capacity_1654_);
lean_closure_set(v___f_1668_, 3, v_size_1655_);
lean_closure_set(v___f_1668_, 4, v_buffer_1656_);
lean_closure_set(v___f_1668_, 5, v_write_1657_);
lean_closure_set(v___f_1668_, 6, v_read_1658_);
lean_closure_set(v___f_1668_, 7, v_receivers_1659_);
lean_closure_set(v___f_1668_, 8, v_nextId_1660_);
lean_closure_set(v___f_1668_, 9, v___x_1667_);
lean_closure_set(v___f_1668_, 10, v_pos_1662_);
lean_closure_set(v___f_1668_, 11, v___f_1647_);
lean_closure_set(v___f_1668_, 12, v_a_1640_);
v___x_1669_ = lean_box(v___x_1641_);
v___x_1670_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1670_, 0, lean_box(0));
lean_closure_set(v___x_1670_, 1, v___x_1669_);
lean_closure_set(v___x_1670_, 2, v_fst_1665_);
v___x_1671_ = lean_apply_2(v_inst_1642_, lean_box(0), v___x_1670_);
v___x_1672_ = lean_apply_4(v_toBind_1638_, lean_box(0), lean_box(0), v___x_1671_, v___f_1668_);
return v___x_1672_;
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec(v___x_1663_);
lean_dec(v_pos_1662_);
lean_dec(v_nextId_1660_);
lean_dec(v_receivers_1659_);
lean_dec(v_read_1658_);
lean_dec(v_write_1657_);
lean_dec_ref(v_buffer_1656_);
lean_dec(v_size_1655_);
lean_dec(v_capacity_1654_);
lean_dec_ref(v_waiters_1653_);
lean_dec_ref(v___f_1647_);
lean_dec(v_inst_1642_);
v___x_1673_ = lean_box(0);
v___x_1674_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1637_, v_toBind_1638_, v___f_1646_, v___x_1673_, v___x_1651_, v_a_1640_);
return v___x_1674_;
}
}
}
else
{
lean_object* v_toPure_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v_fst_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_inst_1642_);
lean_dec_ref(v_a_1639_);
lean_dec(v_toBind_1638_);
lean_dec(v_inst_1637_);
v_toPure_1675_ = lean_ctor_get(v_toApplicative_1636_, 1);
lean_inc(v_toPure_1675_);
lean_dec_ref(v_toApplicative_1636_);
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_apply_2(v_toPure_1675_, lean_box(0), v___x_1676_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object* v_toApplicative_1678_, lean_object* v_inst_1679_, lean_object* v_toBind_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v___x_1683_, lean_object* v_inst_1684_, lean_object* v_a_1685_){
_start:
{
uint8_t v___x_789__boxed_1686_; lean_object* v_res_1687_; 
v___x_789__boxed_1686_ = lean_unbox(v___x_1683_);
v_res_1687_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1678_, v_inst_1679_, v_toBind_1680_, v_a_1681_, v_a_1682_, v___x_789__boxed_1686_, v_inst_1684_, v_a_1685_);
lean_dec(v_a_1682_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object* v_inst_1688_, lean_object* v_next_1689_, lean_object* v_toBind_1690_, lean_object* v___f_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1688_, v_a_1692_, v_next_1689_);
v___x_1694_ = lean_apply_4(v_toBind_1690_, lean_box(0), lean_box(0), v___x_1693_, v___f_1691_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object* v_a_1695_, lean_object* v_toApplicative_1696_, lean_object* v_inst_1697_, lean_object* v_toBind_1698_, lean_object* v_a_1699_, lean_object* v_inst_1700_, lean_object* v_next_1701_, lean_object* v_inst_1702_, uint8_t v_a_1703_){
_start:
{
if (v_a_1703_ == 0)
{
lean_object* v_capacity_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_capacity_1704_ = lean_ctor_get(v_a_1695_, 2);
lean_inc(v_capacity_1704_);
v___x_1705_ = 1;
v___x_1706_ = lean_box(v___x_1705_);
lean_inc(v_a_1699_);
lean_inc_n(v_toBind_1698_, 2);
lean_inc_n(v_inst_1697_, 2);
v___f_1707_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1707_, 0, v_toApplicative_1696_);
lean_closure_set(v___f_1707_, 1, v_inst_1697_);
lean_closure_set(v___f_1707_, 2, v_toBind_1698_);
lean_closure_set(v___f_1707_, 3, v_a_1695_);
lean_closure_set(v___f_1707_, 4, v_a_1699_);
lean_closure_set(v___f_1707_, 5, v___x_1706_);
lean_closure_set(v___f_1707_, 6, v_inst_1700_);
lean_inc(v_next_1701_);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1708_, 0, v_inst_1697_);
lean_closure_set(v___f_1708_, 1, v_next_1701_);
lean_closure_set(v___f_1708_, 2, v_toBind_1698_);
lean_closure_set(v___f_1708_, 3, v___f_1707_);
v___x_1709_ = lean_nat_mod(v_next_1701_, v_capacity_1704_);
lean_dec(v_capacity_1704_);
lean_dec(v_next_1701_);
v___x_1710_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1702_, v_inst_1697_, v___x_1709_, v_a_1699_);
v___x_1711_ = lean_apply_4(v_toBind_1698_, lean_box(0), lean_box(0), v___x_1710_, v___f_1708_);
return v___x_1711_;
}
else
{
lean_object* v_toPure_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref(v_inst_1702_);
lean_dec(v_next_1701_);
lean_dec(v_inst_1700_);
lean_dec(v_toBind_1698_);
lean_dec(v_inst_1697_);
lean_dec_ref(v_a_1695_);
v_toPure_1712_ = lean_ctor_get(v_toApplicative_1696_, 1);
lean_inc(v_toPure_1712_);
lean_dec_ref(v_toApplicative_1696_);
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_apply_2(v_toPure_1712_, lean_box(0), v___x_1713_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object* v_a_1715_, lean_object* v_toApplicative_1716_, lean_object* v_inst_1717_, lean_object* v_toBind_1718_, lean_object* v_a_1719_, lean_object* v_inst_1720_, lean_object* v_next_1721_, lean_object* v_inst_1722_, lean_object* v_a_1723_){
_start:
{
uint8_t v_a_boxed_1724_; lean_object* v_res_1725_; 
v_a_boxed_1724_ = lean_unbox(v_a_1723_);
v_res_1725_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1715_, v_toApplicative_1716_, v_inst_1717_, v_toBind_1718_, v_a_1719_, v_inst_1720_, v_next_1721_, v_inst_1722_, v_a_boxed_1724_);
lean_dec(v_a_1719_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object* v_toApplicative_1726_, lean_object* v_inst_1727_, lean_object* v_toBind_1728_, lean_object* v_a_1729_, lean_object* v_inst_1730_, lean_object* v_next_1731_, lean_object* v_inst_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___f_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_inc_ref(v_inst_1732_);
lean_inc(v_a_1729_);
lean_inc(v_toBind_1728_);
lean_inc(v_inst_1727_);
v___f_1734_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_1734_, 0, v_a_1733_);
lean_closure_set(v___f_1734_, 1, v_toApplicative_1726_);
lean_closure_set(v___f_1734_, 2, v_inst_1727_);
lean_closure_set(v___f_1734_, 3, v_toBind_1728_);
lean_closure_set(v___f_1734_, 4, v_a_1729_);
lean_closure_set(v___f_1734_, 5, v_inst_1730_);
lean_closure_set(v___f_1734_, 6, v_next_1731_);
lean_closure_set(v___f_1734_, 7, v_inst_1732_);
v___x_1735_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_1732_, v_inst_1727_, v_a_1729_);
v___x_1736_ = lean_apply_4(v_toBind_1728_, lean_box(0), lean_box(0), v___x_1735_, v___f_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed(lean_object* v_toApplicative_1737_, lean_object* v_inst_1738_, lean_object* v_toBind_1739_, lean_object* v_a_1740_, lean_object* v_inst_1741_, lean_object* v_next_1742_, lean_object* v_inst_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(v_toApplicative_1737_, v_inst_1738_, v_toBind_1739_, v_a_1740_, v_inst_1741_, v_next_1742_, v_inst_1743_, v_a_1744_);
lean_dec(v_a_1740_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_next_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_toApplicative_1751_; lean_object* v_toBind_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_toApplicative_1751_ = lean_ctor_get(v_inst_1746_, 0);
lean_inc_ref(v_toApplicative_1751_);
v_toBind_1752_ = lean_ctor_get(v_inst_1746_, 1);
lean_inc_n(v_toBind_1752_, 2);
lean_inc_n(v_a_1750_, 2);
lean_inc(v_inst_1747_);
v___f_1753_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_1753_, 0, v_toApplicative_1751_);
lean_closure_set(v___f_1753_, 1, v_inst_1747_);
lean_closure_set(v___f_1753_, 2, v_toBind_1752_);
lean_closure_set(v___f_1753_, 3, v_a_1750_);
lean_closure_set(v___f_1753_, 4, v_inst_1748_);
lean_closure_set(v___f_1753_, 5, v_next_1749_);
lean_closure_set(v___f_1753_, 6, v_inst_1746_);
v___x_1754_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1754_, 0, lean_box(0));
lean_closure_set(v___x_1754_, 1, lean_box(0));
lean_closure_set(v___x_1754_, 2, v_a_1750_);
v___x_1755_ = lean_apply_2(v_inst_1747_, lean_box(0), v___x_1754_);
v___x_1756_ = lean_apply_4(v_toBind_1752_, lean_box(0), lean_box(0), v___x_1755_, v___f_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___boxed(lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_next_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1757_, v_inst_1758_, v_inst_1759_, v_next_1760_, v_a_1761_);
lean_dec(v_a_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object* v_m_1763_, lean_object* v_00_u03b1_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_next_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1765_, v_inst_1766_, v_inst_1767_, v_next_1768_, v_a_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___boxed(lean_object* v_m_1771_, lean_object* v_00_u03b1_1772_, lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_next_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(v_m_1771_, v_00_u03b1_1772_, v_inst_1773_, v_inst_1774_, v_inst_1775_, v_next_1776_, v_a_1777_);
lean_dec(v_a_1777_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v_capacity_1783_; lean_object* v_buffer_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1782_ = lean_st_ref_get(v_a_1780_);
v_capacity_1783_ = lean_ctor_get(v___x_1782_, 2);
lean_inc(v_capacity_1783_);
v_buffer_1784_ = lean_ctor_get(v___x_1782_, 4);
lean_inc_ref(v_buffer_1784_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_nat_mod(v_place_1779_, v_capacity_1783_);
lean_dec(v_capacity_1783_);
v___x_1786_ = lean_array_fget(v_buffer_1784_, v___x_1785_);
lean_dec(v___x_1785_);
lean_dec_ref(v_buffer_1784_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_1788_, lean_object* v_a_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec(v_place_1788_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; lean_object* v_size_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1794_ = lean_st_ref_get(v_a_1792_);
v_size_1795_ = lean_ctor_get(v___x_1794_, 3);
lean_inc(v_size_1795_);
lean_dec(v___x_1794_);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_nat_dec_eq(v_size_1795_, v___x_1796_);
lean_dec(v_size_1795_);
v___x_1798_ = lean_box(v___x_1797_);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1800_);
lean_dec(v_a_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_1803_, lean_object* v_next_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v_fst_1808_; lean_object* v_snd_1809_; lean_object* v_value_1812_; lean_object* v_pos_1813_; lean_object* v_remaining_1814_; uint8_t v___x_1815_; 
v___x_1806_ = lean_st_ref_take(v_slot_1803_);
v_value_1812_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_value_1812_);
v_pos_1813_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_pos_1813_);
v_remaining_1814_ = lean_ctor_get(v___x_1806_, 2);
lean_inc(v_remaining_1814_);
v___x_1815_ = lean_nat_dec_eq(v_next_1804_, v_pos_1813_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v_remaining_1814_);
lean_dec(v_pos_1813_);
lean_dec(v_value_1812_);
v___x_1816_ = lean_box(0);
v___x_1817_ = lean_box(v___x_1815_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v_fst_1808_ = v___x_1818_;
v_snd_1809_ = v___x_1806_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1837_; 
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; lean_object* v_unused_1839_; lean_object* v_unused_1840_; 
v_unused_1838_ = lean_ctor_get(v___x_1806_, 2);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v___x_1806_, 1);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v___x_1806_, 0);
lean_dec(v_unused_1840_);
v___x_1820_ = v___x_1806_;
v_isShared_1821_ = v_isSharedCheck_1837_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1806_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1837_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = lean_unsigned_to_nat(1u);
v___x_1823_ = lean_nat_dec_eq(v_remaining_1814_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1824_ = lean_box(v___x_1823_);
lean_inc(v_value_1812_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_value_1812_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_nat_sub(v_remaining_1814_, v___x_1822_);
lean_dec(v_remaining_1814_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 2, v___x_1826_);
v___x_1828_ = v___x_1820_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_value_1812_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_pos_1813_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
v_fst_1808_ = v___x_1825_;
v_snd_1809_ = v___x_1828_;
goto v___jp_1807_;
}
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_dec(v_remaining_1814_);
v___x_1830_ = lean_box(v___x_1815_);
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v_value_1812_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_unsigned_to_nat(0u);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 2, v___x_1833_);
lean_ctor_set(v___x_1820_, 0, v___x_1832_);
v___x_1835_ = v___x_1820_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_pos_1813_);
lean_ctor_set(v_reuseFailAlloc_1836_, 2, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
v_fst_1808_ = v___x_1831_;
v_snd_1809_ = v___x_1835_;
goto v___jp_1807_;
}
}
}
}
v___jp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_st_ref_put(v_slot_1803_, v_snd_1809_);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_fst_1808_);
return v___x_1811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_1841_, lean_object* v_next_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_1841_, v_next_1842_);
lean_dec(v_next_1842_);
lean_dec(v_slot_1841_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1923_; 
v___x_1848_ = lean_st_ref_get(v_a_1846_);
v___x_1849_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1846_);
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1923_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1923_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_unbox(v_a_1850_);
lean_dec(v_a_1850_);
if (v___x_1854_ == 0)
{
lean_object* v_capacity_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1918_; 
lean_del_object(v___x_1852_);
v_capacity_1855_ = lean_ctor_get(v___x_1848_, 2);
lean_inc(v_capacity_1855_);
v___x_1856_ = 1;
v___x_1857_ = lean_nat_mod(v_next_1845_, v_capacity_1855_);
lean_dec(v_capacity_1855_);
v___x_1858_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_1857_, v_a_1846_);
lean_dec(v___x_1857_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1918_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1918_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1917_; 
v___x_1863_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_1859_, v_next_1845_);
lean_dec(v_a_1859_);
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1917_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1917_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v_st_1871_; lean_object* v___y_1872_; 
v_fst_1868_ = lean_ctor_get(v_a_1864_, 0);
lean_inc(v_fst_1868_);
v_snd_1869_ = lean_ctor_get(v_a_1864_, 1);
lean_inc(v_snd_1869_);
lean_dec(v_a_1864_);
if (lean_obj_tag(v_fst_1868_) == 1)
{
uint8_t v___x_1877_; 
lean_del_object(v___x_1861_);
v___x_1877_ = lean_unbox(v_snd_1869_);
lean_dec(v_snd_1869_);
if (v___x_1877_ == 0)
{
v_st_1871_ = v___x_1848_;
v___y_1872_ = v_a_1846_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1878_; lean_object* v_producers_1879_; lean_object* v_waiters_1880_; lean_object* v_capacity_1881_; lean_object* v_size_1882_; lean_object* v_buffer_1883_; lean_object* v_write_1884_; lean_object* v_read_1885_; lean_object* v_receivers_1886_; lean_object* v_nextId_1887_; uint8_t v_closed_1888_; lean_object* v_pos_1889_; lean_object* v___x_1890_; 
v___x_1878_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_1848_);
v_producers_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc_ref(v_producers_1879_);
v_waiters_1880_ = lean_ctor_get(v___x_1878_, 1);
lean_inc_ref(v_waiters_1880_);
v_capacity_1881_ = lean_ctor_get(v___x_1878_, 2);
lean_inc(v_capacity_1881_);
v_size_1882_ = lean_ctor_get(v___x_1878_, 3);
lean_inc(v_size_1882_);
v_buffer_1883_ = lean_ctor_get(v___x_1878_, 4);
lean_inc_ref(v_buffer_1883_);
v_write_1884_ = lean_ctor_get(v___x_1878_, 5);
lean_inc(v_write_1884_);
v_read_1885_ = lean_ctor_get(v___x_1878_, 6);
lean_inc(v_read_1885_);
v_receivers_1886_ = lean_ctor_get(v___x_1878_, 7);
lean_inc(v_receivers_1886_);
v_nextId_1887_ = lean_ctor_get(v___x_1878_, 8);
lean_inc(v_nextId_1887_);
v_closed_1888_ = lean_ctor_get_uint8(v___x_1878_, sizeof(void*)*10);
v_pos_1889_ = lean_ctor_get(v___x_1878_, 9);
lean_inc(v_pos_1889_);
v___x_1890_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1879_);
if (lean_obj_tag(v___x_1890_) == 1)
{
lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1902_; 
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; lean_object* v_unused_1904_; lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; lean_object* v_unused_1908_; lean_object* v_unused_1909_; lean_object* v_unused_1910_; lean_object* v_unused_1911_; lean_object* v_unused_1912_; 
v_unused_1903_ = lean_ctor_get(v___x_1878_, 9);
lean_dec(v_unused_1903_);
v_unused_1904_ = lean_ctor_get(v___x_1878_, 8);
lean_dec(v_unused_1904_);
v_unused_1905_ = lean_ctor_get(v___x_1878_, 7);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v___x_1878_, 6);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v___x_1878_, 5);
lean_dec(v_unused_1907_);
v_unused_1908_ = lean_ctor_get(v___x_1878_, 4);
lean_dec(v_unused_1908_);
v_unused_1909_ = lean_ctor_get(v___x_1878_, 3);
lean_dec(v_unused_1909_);
v_unused_1910_ = lean_ctor_get(v___x_1878_, 2);
lean_dec(v_unused_1910_);
v_unused_1911_ = lean_ctor_get(v___x_1878_, 1);
lean_dec(v_unused_1911_);
v_unused_1912_ = lean_ctor_get(v___x_1878_, 0);
lean_dec(v_unused_1912_);
v___x_1892_ = v___x_1878_;
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
else
{
lean_dec(v___x_1878_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_val_1894_; lean_object* v_fst_1895_; lean_object* v_snd_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v_val_1894_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v___x_1890_, 1);
v_fst_1895_ = lean_ctor_get(v_val_1894_, 0);
lean_inc(v_fst_1895_);
v_snd_1896_ = lean_ctor_get(v_val_1894_, 1);
lean_inc(v_snd_1896_);
lean_dec(v_val_1894_);
v___x_1897_ = lean_box(v___x_1856_);
v___x_1898_ = lean_io_promise_resolve(v___x_1897_, v_fst_1895_);
lean_dec(v_fst_1895_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v_snd_1896_);
v___x_1900_ = v___x_1892_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_snd_1896_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_waiters_1880_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_capacity_1881_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_size_1882_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_buffer_1883_);
lean_ctor_set(v_reuseFailAlloc_1901_, 5, v_write_1884_);
lean_ctor_set(v_reuseFailAlloc_1901_, 6, v_read_1885_);
lean_ctor_set(v_reuseFailAlloc_1901_, 7, v_receivers_1886_);
lean_ctor_set(v_reuseFailAlloc_1901_, 8, v_nextId_1887_);
lean_ctor_set(v_reuseFailAlloc_1901_, 9, v_pos_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1901_, sizeof(void*)*10, v_closed_1888_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
v_st_1871_ = v___x_1900_;
v___y_1872_ = v_a_1846_;
goto v___jp_1870_;
}
}
}
else
{
lean_dec(v___x_1890_);
lean_dec(v_pos_1889_);
lean_dec(v_nextId_1887_);
lean_dec(v_receivers_1886_);
lean_dec(v_read_1885_);
lean_dec(v_write_1884_);
lean_dec_ref(v_buffer_1883_);
lean_dec(v_size_1882_);
lean_dec(v_capacity_1881_);
lean_dec_ref(v_waiters_1880_);
v_st_1871_ = v___x_1878_;
v___y_1872_ = v_a_1846_;
goto v___jp_1870_;
}
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_del_object(v___x_1866_);
lean_dec(v___x_1848_);
v___x_1913_ = lean_box(0);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1913_);
v___x_1915_ = v___x_1861_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
v___jp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1873_ = lean_st_ref_swap(v___y_1872_, v_st_1871_);
lean_dec(v___x_1873_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v_fst_1868_);
v___x_1875_ = v___x_1866_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_fst_1868_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
lean_dec(v___x_1848_);
v___x_1919_ = lean_box(0);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1919_);
v___x_1921_ = v___x_1852_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_1924_, lean_object* v_a_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_1924_, v_a_1925_);
lean_dec(v_a_1925_);
lean_dec(v_next_1924_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_a_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_fst_1931_; lean_object* v_snd_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1974_; 
v_fst_1931_ = lean_ctor_get(v_a_1928_, 0);
v_snd_1932_ = lean_ctor_get(v_a_1928_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_a_1928_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1934_ = v_a_1928_;
v_isShared_1935_ = v_isSharedCheck_1974_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snd_1932_);
lean_inc(v_fst_1931_);
lean_dec(v_a_1928_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1974_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
uint8_t v___y_1937_; lean_object* v_size_1969_; lean_object* v_pos_1970_; uint8_t v___x_1971_; 
v_size_1969_ = lean_ctor_get(v_fst_1931_, 3);
v_pos_1970_ = lean_ctor_get(v_fst_1931_, 9);
v___x_1971_ = lean_nat_dec_lt(v_snd_1932_, v_pos_1970_);
if (v___x_1971_ == 0)
{
v___y_1937_ = v___x_1971_;
goto v___jp_1936_;
}
else
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = lean_nat_dec_lt(v___x_1972_, v_size_1969_);
v___y_1937_ = v___x_1973_;
goto v___jp_1936_;
}
v___jp_1936_:
{
if (v___y_1937_ == 0)
{
lean_object* v___x_1939_; 
if (v_isShared_1935_ == 0)
{
v___x_1939_ = v___x_1934_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_fst_1931_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_snd_1932_);
v___x_1939_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
return v___x_1940_;
}
}
else
{
lean_object* v___x_1942_; 
v___x_1942_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_1932_, v___y_1929_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1960_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1960_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1960_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
if (lean_obj_tag(v_a_1943_) == 1)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_dec_ref_known(v_a_1943_, 1);
lean_del_object(v___x_1945_);
lean_dec(v_fst_1931_);
v___x_1947_ = lean_st_ref_get(v___y_1929_);
v___x_1948_ = lean_unsigned_to_nat(1u);
v___x_1949_ = lean_nat_add(v_snd_1932_, v___x_1948_);
lean_dec(v_snd_1932_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v___x_1949_);
lean_ctor_set(v___x_1934_, 0, v___x_1947_);
v___x_1951_ = v___x_1934_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v_a_1928_ = v___x_1951_;
goto _start;
}
}
else
{
lean_object* v___x_1955_; 
lean_dec(v_a_1943_);
if (v_isShared_1935_ == 0)
{
v___x_1955_ = v___x_1934_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_fst_1931_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_snd_1932_);
v___x_1955_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1955_);
v___x_1957_ = v___x_1945_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_del_object(v___x_1934_);
lean_dec(v_snd_1932_);
lean_dec(v_fst_1931_);
v_a_1961_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1942_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1942_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_a_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_1975_, v___y_1976_);
lean_dec(v___y_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_1979_, lean_object* v_k_1980_){
_start:
{
if (lean_obj_tag(v_t_1979_) == 0)
{
lean_object* v_k_1981_; lean_object* v_v_1982_; lean_object* v_l_1983_; lean_object* v_r_1984_; uint8_t v___x_1985_; 
v_k_1981_ = lean_ctor_get(v_t_1979_, 1);
v_v_1982_ = lean_ctor_get(v_t_1979_, 2);
v_l_1983_ = lean_ctor_get(v_t_1979_, 3);
v_r_1984_ = lean_ctor_get(v_t_1979_, 4);
v___x_1985_ = lean_nat_dec_lt(v_k_1980_, v_k_1981_);
if (v___x_1985_ == 0)
{
uint8_t v___x_1986_; 
v___x_1986_ = lean_nat_dec_eq(v_k_1980_, v_k_1981_);
if (v___x_1986_ == 0)
{
v_t_1979_ = v_r_1984_;
goto _start;
}
else
{
lean_object* v___x_1988_; 
lean_inc(v_v_1982_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_v_1982_);
return v___x_1988_;
}
}
else
{
v_t_1979_ = v_l_1983_;
goto _start;
}
}
else
{
lean_object* v___x_1990_; 
v___x_1990_ = lean_box(0);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_1991_, lean_object* v_k_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_1991_, v_k_1992_);
lean_dec(v_k_1992_);
lean_dec(v_t_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_1994_, lean_object* v_t_1995_){
_start:
{
if (lean_obj_tag(v_t_1995_) == 0)
{
lean_object* v_k_1996_; lean_object* v_v_1997_; lean_object* v_l_1998_; lean_object* v_r_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2654_; 
v_k_1996_ = lean_ctor_get(v_t_1995_, 1);
v_v_1997_ = lean_ctor_get(v_t_1995_, 2);
v_l_1998_ = lean_ctor_get(v_t_1995_, 3);
v_r_1999_ = lean_ctor_get(v_t_1995_, 4);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_t_1995_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_t_1995_, 0);
lean_dec(v_unused_2655_);
v___x_2001_ = v_t_1995_;
v_isShared_2002_ = v_isSharedCheck_2654_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_r_1999_);
lean_inc(v_l_1998_);
lean_inc(v_v_1997_);
lean_inc(v_k_1996_);
lean_dec(v_t_1995_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2654_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_nat_dec_lt(v_k_1994_, v_k_1996_);
if (v___x_2003_ == 0)
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_nat_dec_eq(v_k_1994_, v_k_1996_);
if (v___x_2004_ == 0)
{
lean_object* v_impl_2005_; lean_object* v___x_2006_; 
v_impl_2005_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1994_, v_r_1999_);
v___x_2006_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2005_) == 0)
{
if (lean_obj_tag(v_l_1998_) == 0)
{
lean_object* v_size_2007_; lean_object* v_size_2008_; lean_object* v_k_2009_; lean_object* v_v_2010_; lean_object* v_l_2011_; lean_object* v_r_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v_size_2007_ = lean_ctor_get(v_impl_2005_, 0);
lean_inc(v_size_2007_);
v_size_2008_ = lean_ctor_get(v_l_1998_, 0);
v_k_2009_ = lean_ctor_get(v_l_1998_, 1);
v_v_2010_ = lean_ctor_get(v_l_1998_, 2);
v_l_2011_ = lean_ctor_get(v_l_1998_, 3);
v_r_2012_ = lean_ctor_get(v_l_1998_, 4);
lean_inc(v_r_2012_);
v___x_2013_ = lean_unsigned_to_nat(3u);
v___x_2014_ = lean_nat_mul(v___x_2013_, v_size_2007_);
v___x_2015_ = lean_nat_dec_lt(v___x_2014_, v_size_2008_);
lean_dec(v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
lean_dec(v_r_2012_);
v___x_2016_ = lean_nat_add(v___x_2006_, v_size_2008_);
v___x_2017_ = lean_nat_add(v___x_2016_, v_size_2007_);
lean_dec(v_size_2007_);
lean_dec(v___x_2016_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_impl_2005_);
lean_ctor_set(v___x_2001_, 0, v___x_2017_);
v___x_2019_ = v___x_2001_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2020_, 3, v_l_1998_);
lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_impl_2005_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
else
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2086_; 
lean_inc(v_l_2011_);
lean_inc(v_v_2010_);
lean_inc(v_k_2009_);
lean_inc(v_size_2008_);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; lean_object* v_unused_2088_; lean_object* v_unused_2089_; lean_object* v_unused_2090_; lean_object* v_unused_2091_; 
v_unused_2087_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_l_1998_, 2);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_l_1998_, 1);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v_l_1998_, 0);
lean_dec(v_unused_2091_);
v___x_2022_ = v_l_1998_;
v_isShared_2023_ = v_isSharedCheck_2086_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v_l_1998_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2086_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_size_2024_; lean_object* v_size_2025_; lean_object* v_k_2026_; lean_object* v_v_2027_; lean_object* v_l_2028_; lean_object* v_r_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v_size_2024_ = lean_ctor_get(v_l_2011_, 0);
v_size_2025_ = lean_ctor_get(v_r_2012_, 0);
v_k_2026_ = lean_ctor_get(v_r_2012_, 1);
v_v_2027_ = lean_ctor_get(v_r_2012_, 2);
v_l_2028_ = lean_ctor_get(v_r_2012_, 3);
v_r_2029_ = lean_ctor_get(v_r_2012_, 4);
v___x_2030_ = lean_unsigned_to_nat(2u);
v___x_2031_ = lean_nat_mul(v___x_2030_, v_size_2024_);
v___x_2032_ = lean_nat_dec_lt(v_size_2025_, v___x_2031_);
lean_dec(v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2061_; 
lean_inc(v_r_2029_);
lean_inc(v_l_2028_);
lean_inc(v_v_2027_);
lean_inc(v_k_2026_);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_r_2012_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; lean_object* v_unused_2063_; lean_object* v_unused_2064_; lean_object* v_unused_2065_; lean_object* v_unused_2066_; 
v_unused_2062_ = lean_ctor_get(v_r_2012_, 4);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v_r_2012_, 3);
lean_dec(v_unused_2063_);
v_unused_2064_ = lean_ctor_get(v_r_2012_, 2);
lean_dec(v_unused_2064_);
v_unused_2065_ = lean_ctor_get(v_r_2012_, 1);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_r_2012_, 0);
lean_dec(v_unused_2066_);
v___x_2034_ = v_r_2012_;
v_isShared_2035_ = v_isSharedCheck_2061_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v_r_2012_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2061_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___x_2049_; lean_object* v___y_2051_; 
v___x_2036_ = lean_nat_add(v___x_2006_, v_size_2008_);
lean_dec(v_size_2008_);
v___x_2037_ = lean_nat_add(v___x_2036_, v_size_2007_);
lean_dec(v___x_2036_);
v___x_2049_ = lean_nat_add(v___x_2006_, v_size_2024_);
if (lean_obj_tag(v_l_2028_) == 0)
{
lean_object* v_size_2059_; 
v_size_2059_ = lean_ctor_get(v_l_2028_, 0);
lean_inc(v_size_2059_);
v___y_2051_ = v_size_2059_;
goto v___jp_2050_;
}
else
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___y_2051_ = v___x_2060_;
goto v___jp_2050_;
}
v___jp_2038_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_nat_add(v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec(v___y_2040_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_impl_2005_);
lean_ctor_set(v___x_2034_, 3, v_r_2029_);
lean_ctor_set(v___x_2034_, 2, v_v_1997_);
lean_ctor_set(v___x_2034_, 1, v_k_1996_);
lean_ctor_set(v___x_2034_, 0, v___x_2042_);
v___x_2044_ = v___x_2034_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_r_2029_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_impl_2005_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 4, v___x_2044_);
lean_ctor_set(v___x_2022_, 3, v___y_2039_);
lean_ctor_set(v___x_2022_, 2, v_v_2027_);
lean_ctor_set(v___x_2022_, 1, v_k_2026_);
lean_ctor_set(v___x_2022_, 0, v___x_2037_);
v___x_2046_ = v___x_2022_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_k_2026_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_v_2027_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v___y_2039_);
lean_ctor_set(v_reuseFailAlloc_2047_, 4, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
v___jp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = lean_nat_add(v___x_2049_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec(v___x_2049_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_l_2028_);
lean_ctor_set(v___x_2001_, 3, v_l_2011_);
lean_ctor_set(v___x_2001_, 2, v_v_2010_);
lean_ctor_set(v___x_2001_, 1, v_k_2009_);
lean_ctor_set(v___x_2001_, 0, v___x_2052_);
v___x_2054_ = v___x_2001_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_k_2009_);
lean_ctor_set(v_reuseFailAlloc_2058_, 2, v_v_2010_);
lean_ctor_set(v_reuseFailAlloc_2058_, 3, v_l_2011_);
lean_ctor_set(v_reuseFailAlloc_2058_, 4, v_l_2028_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; 
v___x_2055_ = lean_nat_add(v___x_2006_, v_size_2007_);
lean_dec(v_size_2007_);
if (lean_obj_tag(v_r_2029_) == 0)
{
lean_object* v_size_2056_; 
v_size_2056_ = lean_ctor_get(v_r_2029_, 0);
lean_inc(v_size_2056_);
v___y_2039_ = v___x_2054_;
v___y_2040_ = v___x_2055_;
v___y_2041_ = v_size_2056_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v___y_2039_ = v___x_2054_;
v___y_2040_ = v___x_2055_;
v___y_2041_ = v___x_2057_;
goto v___jp_2038_;
}
}
}
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
lean_del_object(v___x_2001_);
v___x_2067_ = lean_nat_add(v___x_2006_, v_size_2008_);
lean_dec(v_size_2008_);
v___x_2068_ = lean_nat_add(v___x_2067_, v_size_2007_);
lean_dec(v___x_2067_);
v___x_2069_ = lean_nat_add(v___x_2006_, v_size_2007_);
lean_dec(v_size_2007_);
v___x_2070_ = lean_nat_add(v___x_2069_, v_size_2025_);
lean_dec(v___x_2069_);
lean_inc_ref(v_impl_2005_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 4, v_impl_2005_);
lean_ctor_set(v___x_2022_, 3, v_r_2012_);
lean_ctor_set(v___x_2022_, 2, v_v_1997_);
lean_ctor_set(v___x_2022_, 1, v_k_1996_);
lean_ctor_set(v___x_2022_, 0, v___x_2070_);
v___x_2072_ = v___x_2022_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_r_2012_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_impl_2005_);
v___x_2072_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_isSharedCheck_2079_ = !lean_is_exclusive(v_impl_2005_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; lean_object* v_unused_2082_; lean_object* v_unused_2083_; lean_object* v_unused_2084_; 
v_unused_2080_ = lean_ctor_get(v_impl_2005_, 4);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_impl_2005_, 3);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_impl_2005_, 2);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_impl_2005_, 1);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_impl_2005_, 0);
lean_dec(v_unused_2084_);
v___x_2074_ = v_impl_2005_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_dec(v_impl_2005_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 4, v___x_2072_);
lean_ctor_set(v___x_2074_, 3, v_l_2011_);
lean_ctor_set(v___x_2074_, 2, v_v_2010_);
lean_ctor_set(v___x_2074_, 1, v_k_2009_);
lean_ctor_set(v___x_2074_, 0, v___x_2068_);
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_2009_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_2010_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_l_2011_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v___x_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v_size_2092_ = lean_ctor_get(v_impl_2005_, 0);
lean_inc(v_size_2092_);
v___x_2093_ = lean_nat_add(v___x_2006_, v_size_2092_);
lean_dec(v_size_2092_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_impl_2005_);
lean_ctor_set(v___x_2001_, 0, v___x_2093_);
v___x_2095_ = v___x_2001_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_l_1998_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_impl_2005_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
if (lean_obj_tag(v_l_1998_) == 0)
{
lean_object* v_l_2097_; 
v_l_2097_ = lean_ctor_get(v_l_1998_, 3);
if (lean_obj_tag(v_l_2097_) == 0)
{
lean_object* v_r_2098_; 
lean_inc_ref(v_l_2097_);
v_r_2098_ = lean_ctor_get(v_l_1998_, 4);
lean_inc(v_r_2098_);
if (lean_obj_tag(v_r_2098_) == 0)
{
lean_object* v_size_2099_; lean_object* v_k_2100_; lean_object* v_v_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2114_; 
v_size_2099_ = lean_ctor_get(v_l_1998_, 0);
v_k_2100_ = lean_ctor_get(v_l_1998_, 1);
v_v_2101_ = lean_ctor_get(v_l_1998_, 2);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; lean_object* v_unused_2116_; 
v_unused_2115_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2116_);
v___x_2103_ = v_l_1998_;
v_isShared_2104_ = v_isSharedCheck_2114_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_v_2101_);
lean_inc(v_k_2100_);
lean_inc(v_size_2099_);
lean_dec(v_l_1998_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2114_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v_size_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v_size_2105_ = lean_ctor_get(v_r_2098_, 0);
v___x_2106_ = lean_nat_add(v___x_2006_, v_size_2099_);
lean_dec(v_size_2099_);
v___x_2107_ = lean_nat_add(v___x_2006_, v_size_2105_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v_impl_2005_);
lean_ctor_set(v___x_2103_, 3, v_r_2098_);
lean_ctor_set(v___x_2103_, 2, v_v_1997_);
lean_ctor_set(v___x_2103_, 1, v_k_1996_);
lean_ctor_set(v___x_2103_, 0, v___x_2107_);
v___x_2109_ = v___x_2103_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_r_2098_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_impl_2005_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2111_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___x_2109_);
lean_ctor_set(v___x_2001_, 3, v_l_2097_);
lean_ctor_set(v___x_2001_, 2, v_v_2101_);
lean_ctor_set(v___x_2001_, 1, v_k_2100_);
lean_ctor_set(v___x_2001_, 0, v___x_2106_);
v___x_2111_ = v___x_2001_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_2100_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_2101_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_l_2097_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v___x_2109_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_k_2117_; lean_object* v_v_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2129_; 
v_k_2117_ = lean_ctor_get(v_l_1998_, 1);
v_v_2118_ = lean_ctor_get(v_l_1998_, 2);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2130_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_l_1998_, 0);
lean_dec(v_unused_2132_);
v___x_2120_ = v_l_1998_;
v_isShared_2121_ = v_isSharedCheck_2129_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_v_2118_);
lean_inc(v_k_2117_);
lean_dec(v_l_1998_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2129_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = lean_unsigned_to_nat(3u);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 3, v_r_2098_);
lean_ctor_set(v___x_2120_, 2, v_v_1997_);
lean_ctor_set(v___x_2120_, 1, v_k_1996_);
lean_ctor_set(v___x_2120_, 0, v___x_2006_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_r_2098_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v_r_2098_);
v___x_2124_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___x_2124_);
lean_ctor_set(v___x_2001_, 3, v_l_2097_);
lean_ctor_set(v___x_2001_, 2, v_v_2118_);
lean_ctor_set(v___x_2001_, 1, v_k_2117_);
lean_ctor_set(v___x_2001_, 0, v___x_2122_);
v___x_2126_ = v___x_2001_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_k_2117_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_v_2118_);
lean_ctor_set(v_reuseFailAlloc_2127_, 3, v_l_2097_);
lean_ctor_set(v_reuseFailAlloc_2127_, 4, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
else
{
lean_object* v_r_2133_; 
v_r_2133_ = lean_ctor_get(v_l_1998_, 4);
lean_inc(v_r_2133_);
if (lean_obj_tag(v_r_2133_) == 0)
{
lean_object* v_k_2134_; lean_object* v_v_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2158_; 
lean_inc(v_l_2097_);
v_k_2134_ = lean_ctor_get(v_l_1998_, 1);
v_v_2135_ = lean_ctor_get(v_l_1998_, 2);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2159_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_l_1998_, 0);
lean_dec(v_unused_2161_);
v___x_2137_ = v_l_1998_;
v_isShared_2138_ = v_isSharedCheck_2158_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_v_2135_);
lean_inc(v_k_2134_);
lean_dec(v_l_1998_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2158_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_k_2139_; lean_object* v_v_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2154_; 
v_k_2139_ = lean_ctor_get(v_r_2133_, 1);
v_v_2140_ = lean_ctor_get(v_r_2133_, 2);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_r_2133_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; 
v_unused_2155_ = lean_ctor_get(v_r_2133_, 4);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_r_2133_, 3);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_r_2133_, 0);
lean_dec(v_unused_2157_);
v___x_2142_ = v_r_2133_;
v_isShared_2143_ = v_isSharedCheck_2154_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_v_2140_);
lean_inc(v_k_2139_);
lean_dec(v_r_2133_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2154_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2144_ = lean_unsigned_to_nat(3u);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 4, v_l_2097_);
lean_ctor_set(v___x_2142_, 3, v_l_2097_);
lean_ctor_set(v___x_2142_, 2, v_v_2135_);
lean_ctor_set(v___x_2142_, 1, v_k_2134_);
lean_ctor_set(v___x_2142_, 0, v___x_2006_);
v___x_2146_ = v___x_2142_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2134_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2135_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_l_2097_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_l_2097_);
v___x_2146_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 4, v_l_2097_);
lean_ctor_set(v___x_2137_, 2, v_v_1997_);
lean_ctor_set(v___x_2137_, 1, v_k_1996_);
lean_ctor_set(v___x_2137_, 0, v___x_2006_);
v___x_2148_ = v___x_2137_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_l_2097_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_l_2097_);
v___x_2148_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___x_2148_);
lean_ctor_set(v___x_2001_, 3, v___x_2146_);
lean_ctor_set(v___x_2001_, 2, v_v_2140_);
lean_ctor_set(v___x_2001_, 1, v_k_2139_);
lean_ctor_set(v___x_2001_, 0, v___x_2144_);
v___x_2150_ = v___x_2001_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2151_, 3, v___x_2146_);
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
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = lean_unsigned_to_nat(2u);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_r_2133_);
lean_ctor_set(v___x_2001_, 0, v___x_2162_);
v___x_2164_ = v___x_2001_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_l_1998_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_r_2133_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v___x_2167_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_l_1998_);
lean_ctor_set(v___x_2001_, 0, v___x_2006_);
v___x_2167_ = v___x_2001_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v_l_1998_);
lean_ctor_set(v_reuseFailAlloc_2168_, 4, v_l_1998_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_del_object(v___x_2001_);
lean_dec(v_v_1997_);
lean_dec(v_k_1996_);
if (lean_obj_tag(v_l_1998_) == 0)
{
if (lean_obj_tag(v_r_1999_) == 0)
{
lean_object* v_size_2169_; lean_object* v_k_2170_; lean_object* v_v_2171_; lean_object* v_l_2172_; lean_object* v_r_2173_; lean_object* v_size_2174_; lean_object* v_k_2175_; lean_object* v_v_2176_; lean_object* v_l_2177_; lean_object* v_r_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_size_2169_ = lean_ctor_get(v_l_1998_, 0);
v_k_2170_ = lean_ctor_get(v_l_1998_, 1);
v_v_2171_ = lean_ctor_get(v_l_1998_, 2);
v_l_2172_ = lean_ctor_get(v_l_1998_, 3);
v_r_2173_ = lean_ctor_get(v_l_1998_, 4);
lean_inc(v_r_2173_);
v_size_2174_ = lean_ctor_get(v_r_1999_, 0);
v_k_2175_ = lean_ctor_get(v_r_1999_, 1);
v_v_2176_ = lean_ctor_get(v_r_1999_, 2);
v_l_2177_ = lean_ctor_get(v_r_1999_, 3);
lean_inc(v_l_2177_);
v_r_2178_ = lean_ctor_get(v_r_1999_, 4);
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_nat_dec_lt(v_size_2169_, v_size_2174_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2316_; 
lean_inc(v_l_2172_);
lean_inc(v_v_2171_);
lean_inc(v_k_2170_);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; lean_object* v_unused_2318_; lean_object* v_unused_2319_; lean_object* v_unused_2320_; lean_object* v_unused_2321_; 
v_unused_2317_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2317_);
v_unused_2318_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2318_);
v_unused_2319_ = lean_ctor_get(v_l_1998_, 2);
lean_dec(v_unused_2319_);
v_unused_2320_ = lean_ctor_get(v_l_1998_, 1);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_l_1998_, 0);
lean_dec(v_unused_2321_);
v___x_2182_ = v_l_1998_;
v_isShared_2183_ = v_isSharedCheck_2316_;
goto v_resetjp_2181_;
}
else
{
lean_dec(v_l_1998_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2316_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v_tree_2185_; 
v___x_2184_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2170_, v_v_2171_, v_l_2172_, v_r_2173_);
v_tree_2185_ = lean_ctor_get(v___x_2184_, 2);
lean_inc(v_tree_2185_);
if (lean_obj_tag(v_tree_2185_) == 0)
{
lean_object* v_k_2186_; lean_object* v_v_2187_; lean_object* v_size_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_k_2186_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_k_2186_);
v_v_2187_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_v_2187_);
lean_dec_ref(v___x_2184_);
v_size_2188_ = lean_ctor_get(v_tree_2185_, 0);
v___x_2189_ = lean_unsigned_to_nat(3u);
v___x_2190_ = lean_nat_mul(v___x_2189_, v_size_2188_);
v___x_2191_ = lean_nat_dec_lt(v___x_2190_, v_size_2174_);
lean_dec(v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_dec(v_l_2177_);
v___x_2192_ = lean_nat_add(v___x_2179_, v_size_2188_);
v___x_2193_ = lean_nat_add(v___x_2192_, v_size_2174_);
lean_dec(v___x_2192_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 4, v_r_1999_);
lean_ctor_set(v___x_2182_, 3, v_tree_2185_);
lean_ctor_set(v___x_2182_, 2, v_v_2187_);
lean_ctor_set(v___x_2182_, 1, v_k_2186_);
lean_ctor_set(v___x_2182_, 0, v___x_2193_);
v___x_2195_ = v___x_2182_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_k_2186_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_v_2187_);
lean_ctor_set(v_reuseFailAlloc_2196_, 3, v_tree_2185_);
lean_ctor_set(v_reuseFailAlloc_2196_, 4, v_r_1999_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
else
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2251_; 
lean_inc(v_r_2178_);
lean_inc(v_v_2176_);
lean_inc(v_k_2175_);
lean_inc(v_size_2174_);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2251_ == 0)
{
lean_object* v_unused_2252_; lean_object* v_unused_2253_; lean_object* v_unused_2254_; lean_object* v_unused_2255_; lean_object* v_unused_2256_; 
v_unused_2252_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2252_);
v_unused_2253_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_r_1999_, 2);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_r_1999_, 1);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_r_1999_, 0);
lean_dec(v_unused_2256_);
v___x_2198_ = v_r_1999_;
v_isShared_2199_ = v_isSharedCheck_2251_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v_r_1999_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2251_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v_size_2200_; lean_object* v_k_2201_; lean_object* v_v_2202_; lean_object* v_l_2203_; lean_object* v_r_2204_; lean_object* v_size_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_size_2200_ = lean_ctor_get(v_l_2177_, 0);
v_k_2201_ = lean_ctor_get(v_l_2177_, 1);
v_v_2202_ = lean_ctor_get(v_l_2177_, 2);
v_l_2203_ = lean_ctor_get(v_l_2177_, 3);
v_r_2204_ = lean_ctor_get(v_l_2177_, 4);
v_size_2205_ = lean_ctor_get(v_r_2178_, 0);
v___x_2206_ = lean_unsigned_to_nat(2u);
v___x_2207_ = lean_nat_mul(v___x_2206_, v_size_2205_);
v___x_2208_ = lean_nat_dec_lt(v_size_2200_, v___x_2207_);
lean_dec(v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2236_; 
lean_inc(v_r_2204_);
lean_inc(v_l_2203_);
lean_inc(v_v_2202_);
lean_inc(v_k_2201_);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_l_2177_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; lean_object* v_unused_2238_; lean_object* v_unused_2239_; lean_object* v_unused_2240_; lean_object* v_unused_2241_; 
v_unused_2237_ = lean_ctor_get(v_l_2177_, 4);
lean_dec(v_unused_2237_);
v_unused_2238_ = lean_ctor_get(v_l_2177_, 3);
lean_dec(v_unused_2238_);
v_unused_2239_ = lean_ctor_get(v_l_2177_, 2);
lean_dec(v_unused_2239_);
v_unused_2240_ = lean_ctor_get(v_l_2177_, 1);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_l_2177_, 0);
lean_dec(v_unused_2241_);
v___x_2210_ = v_l_2177_;
v_isShared_2211_ = v_isSharedCheck_2236_;
goto v_resetjp_2209_;
}
else
{
lean_dec(v_l_2177_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2236_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2226_; 
v___x_2212_ = lean_nat_add(v___x_2179_, v_size_2188_);
v___x_2213_ = lean_nat_add(v___x_2212_, v_size_2174_);
lean_dec(v_size_2174_);
if (lean_obj_tag(v_l_2203_) == 0)
{
lean_object* v_size_2234_; 
v_size_2234_ = lean_ctor_get(v_l_2203_, 0);
lean_inc(v_size_2234_);
v___y_2226_ = v_size_2234_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_unsigned_to_nat(0u);
v___y_2226_ = v___x_2235_;
goto v___jp_2225_;
}
v___jp_2214_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_nat_add(v___y_2215_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec(v___y_2215_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 4, v_r_2178_);
lean_ctor_set(v___x_2210_, 3, v_r_2204_);
lean_ctor_set(v___x_2210_, 2, v_v_2176_);
lean_ctor_set(v___x_2210_, 1, v_k_2175_);
lean_ctor_set(v___x_2210_, 0, v___x_2218_);
v___x_2220_ = v___x_2210_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_r_2204_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_r_2178_);
v___x_2220_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2222_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 4, v___x_2220_);
lean_ctor_set(v___x_2198_, 3, v___y_2216_);
lean_ctor_set(v___x_2198_, 2, v_v_2202_);
lean_ctor_set(v___x_2198_, 1, v_k_2201_);
lean_ctor_set(v___x_2198_, 0, v___x_2213_);
v___x_2222_ = v___x_2198_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2201_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2202_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v___y_2216_);
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
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = lean_nat_add(v___x_2212_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec(v___x_2212_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 4, v_l_2203_);
lean_ctor_set(v___x_2182_, 3, v_tree_2185_);
lean_ctor_set(v___x_2182_, 2, v_v_2187_);
lean_ctor_set(v___x_2182_, 1, v_k_2186_);
lean_ctor_set(v___x_2182_, 0, v___x_2227_);
v___x_2229_ = v___x_2182_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_k_2186_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_v_2187_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_tree_2185_);
lean_ctor_set(v_reuseFailAlloc_2233_, 4, v_l_2203_);
v___x_2229_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_nat_add(v___x_2179_, v_size_2205_);
if (lean_obj_tag(v_r_2204_) == 0)
{
lean_object* v_size_2231_; 
v_size_2231_ = lean_ctor_get(v_r_2204_, 0);
lean_inc(v_size_2231_);
v___y_2215_ = v___x_2230_;
v___y_2216_ = v___x_2229_;
v___y_2217_ = v_size_2231_;
goto v___jp_2214_;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_unsigned_to_nat(0u);
v___y_2215_ = v___x_2230_;
v___y_2216_ = v___x_2229_;
v___y_2217_ = v___x_2232_;
goto v___jp_2214_;
}
}
}
}
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2242_ = lean_nat_add(v___x_2179_, v_size_2188_);
v___x_2243_ = lean_nat_add(v___x_2242_, v_size_2174_);
lean_dec(v_size_2174_);
v___x_2244_ = lean_nat_add(v___x_2242_, v_size_2200_);
lean_dec(v___x_2242_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 4, v_l_2177_);
lean_ctor_set(v___x_2198_, 3, v_tree_2185_);
lean_ctor_set(v___x_2198_, 2, v_v_2187_);
lean_ctor_set(v___x_2198_, 1, v_k_2186_);
lean_ctor_set(v___x_2198_, 0, v___x_2244_);
v___x_2246_ = v___x_2198_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_k_2186_);
lean_ctor_set(v_reuseFailAlloc_2250_, 2, v_v_2187_);
lean_ctor_set(v_reuseFailAlloc_2250_, 3, v_tree_2185_);
lean_ctor_set(v_reuseFailAlloc_2250_, 4, v_l_2177_);
v___x_2246_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2248_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 4, v_r_2178_);
lean_ctor_set(v___x_2182_, 3, v___x_2246_);
lean_ctor_set(v___x_2182_, 2, v_v_2176_);
lean_ctor_set(v___x_2182_, 1, v_k_2175_);
lean_ctor_set(v___x_2182_, 0, v___x_2243_);
v___x_2248_ = v___x_2182_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_r_2178_);
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
else
{
lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2310_; 
lean_inc(v_r_2178_);
lean_inc(v_v_2176_);
lean_inc(v_k_2175_);
lean_inc(v_size_2174_);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2311_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_r_1999_, 2);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_r_1999_, 1);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_r_1999_, 0);
lean_dec(v_unused_2315_);
v___x_2258_ = v_r_1999_;
v_isShared_2259_ = v_isSharedCheck_2310_;
goto v_resetjp_2257_;
}
else
{
lean_dec(v_r_1999_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2310_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
if (lean_obj_tag(v_l_2177_) == 0)
{
if (lean_obj_tag(v_r_2178_) == 0)
{
lean_object* v_k_2260_; lean_object* v_v_2261_; lean_object* v_size_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v_k_2260_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_k_2260_);
v_v_2261_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_v_2261_);
lean_dec_ref(v___x_2184_);
v_size_2262_ = lean_ctor_get(v_l_2177_, 0);
v___x_2263_ = lean_nat_add(v___x_2179_, v_size_2174_);
lean_dec(v_size_2174_);
v___x_2264_ = lean_nat_add(v___x_2179_, v_size_2262_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 4, v_l_2177_);
lean_ctor_set(v___x_2258_, 3, v_tree_2185_);
lean_ctor_set(v___x_2258_, 2, v_v_2261_);
lean_ctor_set(v___x_2258_, 1, v_k_2260_);
lean_ctor_set(v___x_2258_, 0, v___x_2264_);
v___x_2266_ = v___x_2258_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_k_2260_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_v_2261_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_tree_2185_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v_l_2177_);
v___x_2266_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2268_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 4, v_r_2178_);
lean_ctor_set(v___x_2182_, 3, v___x_2266_);
lean_ctor_set(v___x_2182_, 2, v_v_2176_);
lean_ctor_set(v___x_2182_, 1, v_k_2175_);
lean_ctor_set(v___x_2182_, 0, v___x_2263_);
v___x_2268_ = v___x_2182_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2269_, 3, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2269_, 4, v_r_2178_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
else
{
lean_object* v_k_2271_; lean_object* v_v_2272_; lean_object* v_k_2273_; lean_object* v_v_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_size_2174_);
v_k_2271_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_k_2271_);
v_v_2272_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_v_2272_);
lean_dec_ref(v___x_2184_);
v_k_2273_ = lean_ctor_get(v_l_2177_, 1);
v_v_2274_ = lean_ctor_get(v_l_2177_, 2);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_l_2177_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; lean_object* v_unused_2290_; lean_object* v_unused_2291_; 
v_unused_2289_ = lean_ctor_get(v_l_2177_, 4);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_l_2177_, 3);
lean_dec(v_unused_2290_);
v_unused_2291_ = lean_ctor_get(v_l_2177_, 0);
lean_dec(v_unused_2291_);
v___x_2276_ = v_l_2177_;
v_isShared_2277_ = v_isSharedCheck_2288_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_v_2274_);
lean_inc(v_k_2273_);
lean_dec(v_l_2177_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2288_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_unsigned_to_nat(3u);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 4, v_r_2178_);
lean_ctor_set(v___x_2276_, 3, v_r_2178_);
lean_ctor_set(v___x_2276_, 2, v_v_2272_);
lean_ctor_set(v___x_2276_, 1, v_k_2271_);
lean_ctor_set(v___x_2276_, 0, v___x_2179_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_k_2271_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_v_2272_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_r_2178_);
lean_ctor_set(v_reuseFailAlloc_2287_, 4, v_r_2178_);
v___x_2280_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2282_; 
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 3, v_r_2178_);
lean_ctor_set(v___x_2258_, 0, v___x_2179_);
v___x_2282_ = v___x_2258_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2286_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2286_, 3, v_r_2178_);
lean_ctor_set(v_reuseFailAlloc_2286_, 4, v_r_2178_);
v___x_2282_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
lean_object* v___x_2284_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 4, v___x_2282_);
lean_ctor_set(v___x_2182_, 3, v___x_2280_);
lean_ctor_set(v___x_2182_, 2, v_v_2274_);
lean_ctor_set(v___x_2182_, 1, v_k_2273_);
lean_ctor_set(v___x_2182_, 0, v___x_2278_);
v___x_2284_ = v___x_2182_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_k_2273_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_v_2274_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2178_) == 0)
{
lean_object* v_k_2292_; lean_object* v_v_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec(v_size_2174_);
v_k_2292_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_k_2292_);
v_v_2293_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_v_2293_);
lean_dec_ref(v___x_2184_);
v___x_2294_ = lean_unsigned_to_nat(3u);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 4, v_l_2177_);
lean_ctor_set(v___x_2258_, 2, v_v_2293_);
lean_ctor_set(v___x_2258_, 1, v_k_2292_);
lean_ctor_set(v___x_2258_, 0, v___x_2179_);
v___x_2296_ = v___x_2258_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2292_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2293_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_l_2177_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_l_2177_);
v___x_2296_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2298_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 4, v_r_2178_);
lean_ctor_set(v___x_2182_, 3, v___x_2296_);
lean_ctor_set(v___x_2182_, 2, v_v_2176_);
lean_ctor_set(v___x_2182_, 1, v_k_2175_);
lean_ctor_set(v___x_2182_, 0, v___x_2294_);
v___x_2298_ = v___x_2182_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v_r_2178_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
lean_object* v_k_2301_; lean_object* v_v_2302_; lean_object* v___x_2304_; 
v_k_2301_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_k_2301_);
v_v_2302_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_v_2302_);
lean_dec_ref(v___x_2184_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 3, v_r_2178_);
v___x_2304_ = v___x_2258_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_size_2174_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_r_2178_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_r_2178_);
v___x_2304_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2305_ = lean_unsigned_to_nat(2u);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 4, v___x_2304_);
lean_ctor_set(v___x_2182_, 3, v_r_2178_);
lean_ctor_set(v___x_2182_, 2, v_v_2302_);
lean_ctor_set(v___x_2182_, 1, v_k_2301_);
lean_ctor_set(v___x_2182_, 0, v___x_2305_);
v___x_2307_ = v___x_2182_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_k_2301_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_v_2302_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_r_2178_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v___x_2304_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
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
lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2474_; 
lean_inc(v_r_2178_);
lean_inc(v_v_2176_);
lean_inc(v_k_2175_);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; lean_object* v_unused_2476_; lean_object* v_unused_2477_; lean_object* v_unused_2478_; lean_object* v_unused_2479_; 
v_unused_2475_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2476_);
v_unused_2477_ = lean_ctor_get(v_r_1999_, 2);
lean_dec(v_unused_2477_);
v_unused_2478_ = lean_ctor_get(v_r_1999_, 1);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_r_1999_, 0);
lean_dec(v_unused_2479_);
v___x_2323_ = v_r_1999_;
v_isShared_2324_ = v_isSharedCheck_2474_;
goto v_resetjp_2322_;
}
else
{
lean_dec(v_r_1999_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2474_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v_tree_2326_; 
v___x_2325_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2175_, v_v_2176_, v_l_2177_, v_r_2178_);
v_tree_2326_ = lean_ctor_get(v___x_2325_, 2);
lean_inc(v_tree_2326_);
if (lean_obj_tag(v_tree_2326_) == 0)
{
lean_object* v_k_2327_; lean_object* v_v_2328_; lean_object* v_size_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v_k_2327_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_k_2327_);
v_v_2328_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_v_2328_);
lean_dec_ref(v___x_2325_);
v_size_2329_ = lean_ctor_get(v_tree_2326_, 0);
v___x_2330_ = lean_unsigned_to_nat(3u);
v___x_2331_ = lean_nat_mul(v___x_2330_, v_size_2329_);
v___x_2332_ = lean_nat_dec_lt(v___x_2331_, v_size_2169_);
lean_dec(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
lean_dec(v_r_2173_);
v___x_2333_ = lean_nat_add(v___x_2179_, v_size_2169_);
v___x_2334_ = lean_nat_add(v___x_2333_, v_size_2329_);
lean_dec(v___x_2333_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_tree_2326_);
lean_ctor_set(v___x_2323_, 3, v_l_1998_);
lean_ctor_set(v___x_2323_, 2, v_v_2328_);
lean_ctor_set(v___x_2323_, 1, v_k_2327_);
lean_ctor_set(v___x_2323_, 0, v___x_2334_);
v___x_2336_ = v___x_2323_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_k_2327_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_v_2328_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v_l_1998_);
lean_ctor_set(v_reuseFailAlloc_2337_, 4, v_tree_2326_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
else
{
lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2403_; 
lean_inc(v_l_2172_);
lean_inc(v_v_2171_);
lean_inc(v_k_2170_);
lean_inc(v_size_2169_);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; lean_object* v_unused_2405_; lean_object* v_unused_2406_; lean_object* v_unused_2407_; lean_object* v_unused_2408_; 
v_unused_2404_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_l_1998_, 2);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_l_1998_, 1);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_l_1998_, 0);
lean_dec(v_unused_2408_);
v___x_2339_ = v_l_1998_;
v_isShared_2340_ = v_isSharedCheck_2403_;
goto v_resetjp_2338_;
}
else
{
lean_dec(v_l_1998_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2403_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_size_2341_; lean_object* v_size_2342_; lean_object* v_k_2343_; lean_object* v_v_2344_; lean_object* v_l_2345_; lean_object* v_r_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_size_2341_ = lean_ctor_get(v_l_2172_, 0);
v_size_2342_ = lean_ctor_get(v_r_2173_, 0);
v_k_2343_ = lean_ctor_get(v_r_2173_, 1);
v_v_2344_ = lean_ctor_get(v_r_2173_, 2);
v_l_2345_ = lean_ctor_get(v_r_2173_, 3);
v_r_2346_ = lean_ctor_get(v_r_2173_, 4);
v___x_2347_ = lean_unsigned_to_nat(2u);
v___x_2348_ = lean_nat_mul(v___x_2347_, v_size_2341_);
v___x_2349_ = lean_nat_dec_lt(v_size_2342_, v___x_2348_);
lean_dec(v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2387_; 
lean_inc(v_r_2346_);
lean_inc(v_l_2345_);
lean_inc(v_v_2344_);
lean_inc(v_k_2343_);
lean_del_object(v___x_2339_);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_r_2173_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; lean_object* v_unused_2389_; lean_object* v_unused_2390_; lean_object* v_unused_2391_; lean_object* v_unused_2392_; 
v_unused_2388_ = lean_ctor_get(v_r_2173_, 4);
lean_dec(v_unused_2388_);
v_unused_2389_ = lean_ctor_get(v_r_2173_, 3);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_r_2173_, 2);
lean_dec(v_unused_2390_);
v_unused_2391_ = lean_ctor_get(v_r_2173_, 1);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_r_2173_, 0);
lean_dec(v_unused_2392_);
v___x_2351_ = v_r_2173_;
v_isShared_2352_ = v_isSharedCheck_2387_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v_r_2173_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2387_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___x_2375_; lean_object* v___y_2377_; 
v___x_2353_ = lean_nat_add(v___x_2179_, v_size_2169_);
lean_dec(v_size_2169_);
v___x_2354_ = lean_nat_add(v___x_2353_, v_size_2329_);
lean_dec(v___x_2353_);
v___x_2375_ = lean_nat_add(v___x_2179_, v_size_2341_);
if (lean_obj_tag(v_l_2345_) == 0)
{
lean_object* v_size_2385_; 
v_size_2385_ = lean_ctor_get(v_l_2345_, 0);
lean_inc(v_size_2385_);
v___y_2377_ = v_size_2385_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_unsigned_to_nat(0u);
v___y_2377_ = v___x_2386_;
goto v___jp_2376_;
}
v___jp_2355_:
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2359_ = lean_nat_add(v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec(v___y_2357_);
lean_inc_ref(v_tree_2326_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 4, v_tree_2326_);
lean_ctor_set(v___x_2351_, 3, v_r_2346_);
lean_ctor_set(v___x_2351_, 2, v_v_2328_);
lean_ctor_set(v___x_2351_, 1, v_k_2327_);
lean_ctor_set(v___x_2351_, 0, v___x_2359_);
v___x_2361_ = v___x_2351_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_k_2327_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_v_2328_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_r_2346_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v_tree_2326_);
v___x_2361_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_isSharedCheck_2368_ = !lean_is_exclusive(v_tree_2326_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; lean_object* v_unused_2370_; lean_object* v_unused_2371_; lean_object* v_unused_2372_; lean_object* v_unused_2373_; 
v_unused_2369_ = lean_ctor_get(v_tree_2326_, 4);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_tree_2326_, 3);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_tree_2326_, 2);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_tree_2326_, 1);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_tree_2326_, 0);
lean_dec(v_unused_2373_);
v___x_2363_ = v_tree_2326_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v_tree_2326_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 4, v___x_2361_);
lean_ctor_set(v___x_2363_, 3, v___y_2356_);
lean_ctor_set(v___x_2363_, 2, v_v_2344_);
lean_ctor_set(v___x_2363_, 1, v_k_2343_);
lean_ctor_set(v___x_2363_, 0, v___x_2354_);
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_k_2343_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v_v_2344_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v___y_2356_);
lean_ctor_set(v_reuseFailAlloc_2367_, 4, v___x_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
v___jp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2378_ = lean_nat_add(v___x_2375_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec(v___x_2375_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_l_2345_);
lean_ctor_set(v___x_2323_, 3, v_l_2172_);
lean_ctor_set(v___x_2323_, 2, v_v_2171_);
lean_ctor_set(v___x_2323_, 1, v_k_2170_);
lean_ctor_set(v___x_2323_, 0, v___x_2378_);
v___x_2380_ = v___x_2323_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2378_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v_l_2172_);
lean_ctor_set(v_reuseFailAlloc_2384_, 4, v_l_2345_);
v___x_2380_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_nat_add(v___x_2179_, v_size_2329_);
if (lean_obj_tag(v_r_2346_) == 0)
{
lean_object* v_size_2382_; 
v_size_2382_ = lean_ctor_get(v_r_2346_, 0);
lean_inc(v_size_2382_);
v___y_2356_ = v___x_2380_;
v___y_2357_ = v___x_2381_;
v___y_2358_ = v_size_2382_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_unsigned_to_nat(0u);
v___y_2356_ = v___x_2380_;
v___y_2357_ = v___x_2381_;
v___y_2358_ = v___x_2383_;
goto v___jp_2355_;
}
}
}
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2393_ = lean_nat_add(v___x_2179_, v_size_2169_);
lean_dec(v_size_2169_);
v___x_2394_ = lean_nat_add(v___x_2393_, v_size_2329_);
lean_dec(v___x_2393_);
v___x_2395_ = lean_nat_add(v___x_2179_, v_size_2329_);
v___x_2396_ = lean_nat_add(v___x_2395_, v_size_2342_);
lean_dec(v___x_2395_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_tree_2326_);
lean_ctor_set(v___x_2323_, 3, v_r_2173_);
lean_ctor_set(v___x_2323_, 2, v_v_2328_);
lean_ctor_set(v___x_2323_, 1, v_k_2327_);
lean_ctor_set(v___x_2323_, 0, v___x_2396_);
v___x_2398_ = v___x_2323_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v_k_2327_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v_v_2328_);
lean_ctor_set(v_reuseFailAlloc_2402_, 3, v_r_2173_);
lean_ctor_set(v_reuseFailAlloc_2402_, 4, v_tree_2326_);
v___x_2398_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 4, v___x_2398_);
lean_ctor_set(v___x_2339_, 0, v___x_2394_);
v___x_2400_ = v___x_2339_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_l_2172_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2172_) == 0)
{
lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2432_; 
lean_inc_ref(v_l_2172_);
lean_inc(v_v_2171_);
lean_inc(v_k_2170_);
lean_inc(v_size_2169_);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; lean_object* v_unused_2434_; lean_object* v_unused_2435_; lean_object* v_unused_2436_; lean_object* v_unused_2437_; 
v_unused_2433_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2433_);
v_unused_2434_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_l_1998_, 2);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_l_1998_, 1);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_l_1998_, 0);
lean_dec(v_unused_2437_);
v___x_2410_ = v_l_1998_;
v_isShared_2411_ = v_isSharedCheck_2432_;
goto v_resetjp_2409_;
}
else
{
lean_dec(v_l_1998_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2432_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
if (lean_obj_tag(v_r_2173_) == 0)
{
lean_object* v_k_2412_; lean_object* v_v_2413_; lean_object* v_size_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
v_k_2412_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_k_2412_);
v_v_2413_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_v_2413_);
lean_dec_ref(v___x_2325_);
v_size_2414_ = lean_ctor_get(v_r_2173_, 0);
v___x_2415_ = lean_nat_add(v___x_2179_, v_size_2169_);
lean_dec(v_size_2169_);
v___x_2416_ = lean_nat_add(v___x_2179_, v_size_2414_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_tree_2326_);
lean_ctor_set(v___x_2323_, 3, v_r_2173_);
lean_ctor_set(v___x_2323_, 2, v_v_2413_);
lean_ctor_set(v___x_2323_, 1, v_k_2412_);
lean_ctor_set(v___x_2323_, 0, v___x_2416_);
v___x_2418_ = v___x_2323_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_k_2412_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_v_2413_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_r_2173_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_tree_2326_);
v___x_2418_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2420_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v___x_2418_);
lean_ctor_set(v___x_2410_, 0, v___x_2415_);
v___x_2420_ = v___x_2410_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2421_, 3, v_l_2172_);
lean_ctor_set(v_reuseFailAlloc_2421_, 4, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
else
{
lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
lean_dec(v_size_2169_);
v_k_2423_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_k_2423_);
v_v_2424_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_v_2424_);
lean_dec_ref(v___x_2325_);
v___x_2425_ = lean_unsigned_to_nat(3u);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_r_2173_);
lean_ctor_set(v___x_2323_, 3, v_r_2173_);
lean_ctor_set(v___x_2323_, 2, v_v_2424_);
lean_ctor_set(v___x_2323_, 1, v_k_2423_);
lean_ctor_set(v___x_2323_, 0, v___x_2179_);
v___x_2427_ = v___x_2323_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_k_2423_);
lean_ctor_set(v_reuseFailAlloc_2431_, 2, v_v_2424_);
lean_ctor_set(v_reuseFailAlloc_2431_, 3, v_r_2173_);
lean_ctor_set(v_reuseFailAlloc_2431_, 4, v_r_2173_);
v___x_2427_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2429_; 
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 4, v___x_2427_);
lean_ctor_set(v___x_2410_, 0, v___x_2425_);
v___x_2429_ = v___x_2410_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v_l_2172_);
lean_ctor_set(v_reuseFailAlloc_2430_, 4, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2173_) == 0)
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2462_; 
lean_inc(v_l_2172_);
lean_inc(v_v_2171_);
lean_inc(v_k_2170_);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_l_1998_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; lean_object* v_unused_2464_; lean_object* v_unused_2465_; lean_object* v_unused_2466_; lean_object* v_unused_2467_; 
v_unused_2463_ = lean_ctor_get(v_l_1998_, 4);
lean_dec(v_unused_2463_);
v_unused_2464_ = lean_ctor_get(v_l_1998_, 3);
lean_dec(v_unused_2464_);
v_unused_2465_ = lean_ctor_get(v_l_1998_, 2);
lean_dec(v_unused_2465_);
v_unused_2466_ = lean_ctor_get(v_l_1998_, 1);
lean_dec(v_unused_2466_);
v_unused_2467_ = lean_ctor_get(v_l_1998_, 0);
lean_dec(v_unused_2467_);
v___x_2439_ = v_l_1998_;
v_isShared_2440_ = v_isSharedCheck_2462_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v_l_1998_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2462_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v_k_2441_; lean_object* v_v_2442_; lean_object* v_k_2443_; lean_object* v_v_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2458_; 
v_k_2441_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_k_2441_);
v_v_2442_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_v_2442_);
lean_dec_ref(v___x_2325_);
v_k_2443_ = lean_ctor_get(v_r_2173_, 1);
v_v_2444_ = lean_ctor_get(v_r_2173_, 2);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_r_2173_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; lean_object* v_unused_2460_; lean_object* v_unused_2461_; 
v_unused_2459_ = lean_ctor_get(v_r_2173_, 4);
lean_dec(v_unused_2459_);
v_unused_2460_ = lean_ctor_get(v_r_2173_, 3);
lean_dec(v_unused_2460_);
v_unused_2461_ = lean_ctor_get(v_r_2173_, 0);
lean_dec(v_unused_2461_);
v___x_2446_ = v_r_2173_;
v_isShared_2447_ = v_isSharedCheck_2458_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_v_2444_);
lean_inc(v_k_2443_);
lean_dec(v_r_2173_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2458_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = lean_unsigned_to_nat(3u);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 4, v_l_2172_);
lean_ctor_set(v___x_2446_, 3, v_l_2172_);
lean_ctor_set(v___x_2446_, 2, v_v_2171_);
lean_ctor_set(v___x_2446_, 1, v_k_2170_);
lean_ctor_set(v___x_2446_, 0, v___x_2179_);
v___x_2450_ = v___x_2446_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_l_2172_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_l_2172_);
v___x_2450_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_l_2172_);
lean_ctor_set(v___x_2323_, 3, v_l_2172_);
lean_ctor_set(v___x_2323_, 2, v_v_2442_);
lean_ctor_set(v___x_2323_, 1, v_k_2441_);
lean_ctor_set(v___x_2323_, 0, v___x_2179_);
v___x_2452_ = v___x_2323_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2179_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_k_2441_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_v_2442_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v_l_2172_);
lean_ctor_set(v_reuseFailAlloc_2456_, 4, v_l_2172_);
v___x_2452_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2454_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 4, v___x_2452_);
lean_ctor_set(v___x_2439_, 3, v___x_2450_);
lean_ctor_set(v___x_2439_, 2, v_v_2444_);
lean_ctor_set(v___x_2439_, 1, v_k_2443_);
lean_ctor_set(v___x_2439_, 0, v___x_2448_);
v___x_2454_ = v___x_2439_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_k_2443_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_v_2444_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
}
else
{
lean_object* v_k_2468_; lean_object* v_v_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v_k_2468_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_k_2468_);
v_v_2469_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_v_2469_);
lean_dec_ref(v___x_2325_);
v___x_2470_ = lean_unsigned_to_nat(2u);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 4, v_r_2173_);
lean_ctor_set(v___x_2323_, 3, v_l_1998_);
lean_ctor_set(v___x_2323_, 2, v_v_2469_);
lean_ctor_set(v___x_2323_, 1, v_k_2468_);
lean_ctor_set(v___x_2323_, 0, v___x_2470_);
v___x_2472_ = v___x_2323_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_k_2468_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_v_2469_);
lean_ctor_set(v_reuseFailAlloc_2473_, 3, v_l_1998_);
lean_ctor_set(v_reuseFailAlloc_2473_, 4, v_r_2173_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
}
}
else
{
return v_l_1998_;
}
}
else
{
return v_r_1999_;
}
}
}
else
{
lean_object* v_impl_2480_; lean_object* v___x_2481_; 
v_impl_2480_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1994_, v_l_1998_);
v___x_2481_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2480_) == 0)
{
if (lean_obj_tag(v_r_1999_) == 0)
{
lean_object* v_size_2482_; lean_object* v_size_2483_; lean_object* v_k_2484_; lean_object* v_v_2485_; lean_object* v_l_2486_; lean_object* v_r_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v_size_2482_ = lean_ctor_get(v_impl_2480_, 0);
lean_inc(v_size_2482_);
v_size_2483_ = lean_ctor_get(v_r_1999_, 0);
v_k_2484_ = lean_ctor_get(v_r_1999_, 1);
v_v_2485_ = lean_ctor_get(v_r_1999_, 2);
v_l_2486_ = lean_ctor_get(v_r_1999_, 3);
lean_inc(v_l_2486_);
v_r_2487_ = lean_ctor_get(v_r_1999_, 4);
v___x_2488_ = lean_unsigned_to_nat(3u);
v___x_2489_ = lean_nat_mul(v___x_2488_, v_size_2482_);
v___x_2490_ = lean_nat_dec_lt(v___x_2489_, v_size_2483_);
lean_dec(v___x_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
lean_dec(v_l_2486_);
v___x_2491_ = lean_nat_add(v___x_2481_, v_size_2482_);
lean_dec(v_size_2482_);
v___x_2492_ = lean_nat_add(v___x_2491_, v_size_2483_);
lean_dec(v___x_2491_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 3, v_impl_2480_);
lean_ctor_set(v___x_2001_, 0, v___x_2492_);
v___x_2494_ = v___x_2001_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2495_, 3, v_impl_2480_);
lean_ctor_set(v_reuseFailAlloc_2495_, 4, v_r_1999_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
else
{
lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2559_; 
lean_inc(v_r_2487_);
lean_inc(v_v_2485_);
lean_inc(v_k_2484_);
lean_inc(v_size_2483_);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; lean_object* v_unused_2561_; lean_object* v_unused_2562_; lean_object* v_unused_2563_; lean_object* v_unused_2564_; 
v_unused_2560_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v_r_1999_, 2);
lean_dec(v_unused_2562_);
v_unused_2563_ = lean_ctor_get(v_r_1999_, 1);
lean_dec(v_unused_2563_);
v_unused_2564_ = lean_ctor_get(v_r_1999_, 0);
lean_dec(v_unused_2564_);
v___x_2497_ = v_r_1999_;
v_isShared_2498_ = v_isSharedCheck_2559_;
goto v_resetjp_2496_;
}
else
{
lean_dec(v_r_1999_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2559_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v_size_2499_; lean_object* v_k_2500_; lean_object* v_v_2501_; lean_object* v_l_2502_; lean_object* v_r_2503_; lean_object* v_size_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_size_2499_ = lean_ctor_get(v_l_2486_, 0);
v_k_2500_ = lean_ctor_get(v_l_2486_, 1);
v_v_2501_ = lean_ctor_get(v_l_2486_, 2);
v_l_2502_ = lean_ctor_get(v_l_2486_, 3);
v_r_2503_ = lean_ctor_get(v_l_2486_, 4);
v_size_2504_ = lean_ctor_get(v_r_2487_, 0);
v___x_2505_ = lean_unsigned_to_nat(2u);
v___x_2506_ = lean_nat_mul(v___x_2505_, v_size_2504_);
v___x_2507_ = lean_nat_dec_lt(v_size_2499_, v___x_2506_);
lean_dec(v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2535_; 
lean_inc(v_r_2503_);
lean_inc(v_l_2502_);
lean_inc(v_v_2501_);
lean_inc(v_k_2500_);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_l_2486_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; lean_object* v_unused_2537_; lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2536_ = lean_ctor_get(v_l_2486_, 4);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_l_2486_, 3);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_l_2486_, 2);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_l_2486_, 1);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_l_2486_, 0);
lean_dec(v_unused_2540_);
v___x_2509_ = v_l_2486_;
v_isShared_2510_ = v_isSharedCheck_2535_;
goto v_resetjp_2508_;
}
else
{
lean_dec(v_l_2486_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2535_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2525_; 
v___x_2511_ = lean_nat_add(v___x_2481_, v_size_2482_);
lean_dec(v_size_2482_);
v___x_2512_ = lean_nat_add(v___x_2511_, v_size_2483_);
lean_dec(v_size_2483_);
if (lean_obj_tag(v_l_2502_) == 0)
{
lean_object* v_size_2533_; 
v_size_2533_ = lean_ctor_get(v_l_2502_, 0);
lean_inc(v_size_2533_);
v___y_2525_ = v_size_2533_;
goto v___jp_2524_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = lean_unsigned_to_nat(0u);
v___y_2525_ = v___x_2534_;
goto v___jp_2524_;
}
v___jp_2513_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_nat_add(v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 4, v_r_2487_);
lean_ctor_set(v___x_2509_, 3, v_r_2503_);
lean_ctor_set(v___x_2509_, 2, v_v_2485_);
lean_ctor_set(v___x_2509_, 1, v_k_2484_);
lean_ctor_set(v___x_2509_, 0, v___x_2517_);
v___x_2519_ = v___x_2509_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_k_2484_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_v_2485_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_r_2503_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_r_2487_);
v___x_2519_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2521_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 4, v___x_2519_);
lean_ctor_set(v___x_2497_, 3, v___y_2514_);
lean_ctor_set(v___x_2497_, 2, v_v_2501_);
lean_ctor_set(v___x_2497_, 1, v_k_2500_);
lean_ctor_set(v___x_2497_, 0, v___x_2512_);
v___x_2521_ = v___x_2497_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_k_2500_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_v_2501_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v___y_2514_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
v___jp_2524_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_nat_add(v___x_2511_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec(v___x_2511_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_l_2502_);
lean_ctor_set(v___x_2001_, 3, v_impl_2480_);
lean_ctor_set(v___x_2001_, 0, v___x_2526_);
v___x_2528_ = v___x_2001_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_impl_2480_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_l_2502_);
v___x_2528_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_nat_add(v___x_2481_, v_size_2504_);
if (lean_obj_tag(v_r_2503_) == 0)
{
lean_object* v_size_2530_; 
v_size_2530_ = lean_ctor_get(v_r_2503_, 0);
lean_inc(v_size_2530_);
v___y_2514_ = v___x_2528_;
v___y_2515_ = v___x_2529_;
v___y_2516_ = v_size_2530_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___y_2514_ = v___x_2528_;
v___y_2515_ = v___x_2529_;
v___y_2516_ = v___x_2531_;
goto v___jp_2513_;
}
}
}
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_del_object(v___x_2001_);
v___x_2541_ = lean_nat_add(v___x_2481_, v_size_2482_);
lean_dec(v_size_2482_);
v___x_2542_ = lean_nat_add(v___x_2541_, v_size_2483_);
lean_dec(v_size_2483_);
v___x_2543_ = lean_nat_add(v___x_2541_, v_size_2499_);
lean_dec(v___x_2541_);
lean_inc_ref(v_impl_2480_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 4, v_l_2486_);
lean_ctor_set(v___x_2497_, 3, v_impl_2480_);
lean_ctor_set(v___x_2497_, 2, v_v_1997_);
lean_ctor_set(v___x_2497_, 1, v_k_1996_);
lean_ctor_set(v___x_2497_, 0, v___x_2543_);
v___x_2545_ = v___x_2497_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_impl_2480_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_l_2486_);
v___x_2545_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
v_isSharedCheck_2552_ = !lean_is_exclusive(v_impl_2480_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; lean_object* v_unused_2554_; lean_object* v_unused_2555_; lean_object* v_unused_2556_; lean_object* v_unused_2557_; 
v_unused_2553_ = lean_ctor_get(v_impl_2480_, 4);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_impl_2480_, 3);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_impl_2480_, 2);
lean_dec(v_unused_2555_);
v_unused_2556_ = lean_ctor_get(v_impl_2480_, 1);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_impl_2480_, 0);
lean_dec(v_unused_2557_);
v___x_2547_ = v_impl_2480_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_dec(v_impl_2480_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 4, v_r_2487_);
lean_ctor_set(v___x_2547_, 3, v___x_2545_);
lean_ctor_set(v___x_2547_, 2, v_v_2485_);
lean_ctor_set(v___x_2547_, 1, v_k_2484_);
lean_ctor_set(v___x_2547_, 0, v___x_2542_);
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_k_2484_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v_v_2485_);
lean_ctor_set(v_reuseFailAlloc_2551_, 3, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2551_, 4, v_r_2487_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
v_size_2565_ = lean_ctor_get(v_impl_2480_, 0);
lean_inc(v_size_2565_);
v___x_2566_ = lean_nat_add(v___x_2481_, v_size_2565_);
lean_dec(v_size_2565_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 3, v_impl_2480_);
lean_ctor_set(v___x_2001_, 0, v___x_2566_);
v___x_2568_ = v___x_2001_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_impl_2480_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v_r_1999_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
if (lean_obj_tag(v_r_1999_) == 0)
{
lean_object* v_l_2570_; 
v_l_2570_ = lean_ctor_get(v_r_1999_, 3);
lean_inc(v_l_2570_);
if (lean_obj_tag(v_l_2570_) == 0)
{
lean_object* v_r_2571_; 
v_r_2571_ = lean_ctor_get(v_r_1999_, 4);
lean_inc(v_r_2571_);
if (lean_obj_tag(v_r_2571_) == 0)
{
lean_object* v_size_2572_; lean_object* v_k_2573_; lean_object* v_v_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2587_; 
v_size_2572_ = lean_ctor_get(v_r_1999_, 0);
v_k_2573_ = lean_ctor_get(v_r_1999_, 1);
v_v_2574_ = lean_ctor_get(v_r_1999_, 2);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; lean_object* v_unused_2589_; 
v_unused_2588_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2588_);
v_unused_2589_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2589_);
v___x_2576_ = v_r_1999_;
v_isShared_2577_ = v_isSharedCheck_2587_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_v_2574_);
lean_inc(v_k_2573_);
lean_inc(v_size_2572_);
lean_dec(v_r_1999_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2587_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_size_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
v_size_2578_ = lean_ctor_get(v_l_2570_, 0);
v___x_2579_ = lean_nat_add(v___x_2481_, v_size_2572_);
lean_dec(v_size_2572_);
v___x_2580_ = lean_nat_add(v___x_2481_, v_size_2578_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 4, v_l_2570_);
lean_ctor_set(v___x_2576_, 3, v_impl_2480_);
lean_ctor_set(v___x_2576_, 2, v_v_1997_);
lean_ctor_set(v___x_2576_, 1, v_k_1996_);
lean_ctor_set(v___x_2576_, 0, v___x_2580_);
v___x_2582_ = v___x_2576_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_impl_2480_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v_l_2570_);
v___x_2582_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_r_2571_);
lean_ctor_set(v___x_2001_, 3, v___x_2582_);
lean_ctor_set(v___x_2001_, 2, v_v_2574_);
lean_ctor_set(v___x_2001_, 1, v_k_2573_);
lean_ctor_set(v___x_2001_, 0, v___x_2579_);
v___x_2584_ = v___x_2001_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_k_2573_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_v_2574_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v___x_2582_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_r_2571_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v_k_2590_; lean_object* v_v_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2614_; 
v_k_2590_ = lean_ctor_get(v_r_1999_, 1);
v_v_2591_ = lean_ctor_get(v_r_1999_, 2);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; lean_object* v_unused_2616_; lean_object* v_unused_2617_; 
v_unused_2615_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2615_);
v_unused_2616_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v_r_1999_, 0);
lean_dec(v_unused_2617_);
v___x_2593_ = v_r_1999_;
v_isShared_2594_ = v_isSharedCheck_2614_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_v_2591_);
lean_inc(v_k_2590_);
lean_dec(v_r_1999_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2614_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v_k_2595_; lean_object* v_v_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2610_; 
v_k_2595_ = lean_ctor_get(v_l_2570_, 1);
v_v_2596_ = lean_ctor_get(v_l_2570_, 2);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_l_2570_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; lean_object* v_unused_2612_; lean_object* v_unused_2613_; 
v_unused_2611_ = lean_ctor_get(v_l_2570_, 4);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v_l_2570_, 3);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v_l_2570_, 0);
lean_dec(v_unused_2613_);
v___x_2598_ = v_l_2570_;
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_v_2596_);
lean_inc(v_k_2595_);
lean_dec(v_l_2570_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2610_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2600_ = lean_unsigned_to_nat(3u);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 4, v_r_2571_);
lean_ctor_set(v___x_2598_, 3, v_r_2571_);
lean_ctor_set(v___x_2598_, 2, v_v_1997_);
lean_ctor_set(v___x_2598_, 1, v_k_1996_);
lean_ctor_set(v___x_2598_, 0, v___x_2481_);
v___x_2602_ = v___x_2598_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2609_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2609_, 3, v_r_2571_);
lean_ctor_set(v_reuseFailAlloc_2609_, 4, v_r_2571_);
v___x_2602_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 3, v_r_2571_);
lean_ctor_set(v___x_2593_, 0, v___x_2481_);
v___x_2604_ = v___x_2593_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_k_2590_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_v_2591_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_r_2571_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v_r_2571_);
v___x_2604_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2606_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___x_2604_);
lean_ctor_set(v___x_2001_, 3, v___x_2602_);
lean_ctor_set(v___x_2001_, 2, v_v_2596_);
lean_ctor_set(v___x_2001_, 1, v_k_2595_);
lean_ctor_set(v___x_2001_, 0, v___x_2600_);
v___x_2606_ = v___x_2001_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_k_2595_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_v_2596_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2618_; 
v_r_2618_ = lean_ctor_get(v_r_1999_, 4);
lean_inc(v_r_2618_);
if (lean_obj_tag(v_r_2618_) == 0)
{
lean_object* v_k_2619_; lean_object* v_v_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2631_; 
v_k_2619_ = lean_ctor_get(v_r_1999_, 1);
v_v_2620_ = lean_ctor_get(v_r_1999_, 2);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; 
v_unused_2632_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_r_1999_, 0);
lean_dec(v_unused_2634_);
v___x_2622_ = v_r_1999_;
v_isShared_2623_ = v_isSharedCheck_2631_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_v_2620_);
lean_inc(v_k_2619_);
lean_dec(v_r_1999_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2631_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_unsigned_to_nat(3u);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 4, v_l_2570_);
lean_ctor_set(v___x_2622_, 2, v_v_1997_);
lean_ctor_set(v___x_2622_, 1, v_k_1996_);
lean_ctor_set(v___x_2622_, 0, v___x_2481_);
v___x_2626_ = v___x_2622_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_l_2570_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v_l_2570_);
v___x_2626_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v_r_2618_);
lean_ctor_set(v___x_2001_, 3, v___x_2626_);
lean_ctor_set(v___x_2001_, 2, v_v_2620_);
lean_ctor_set(v___x_2001_, 1, v_k_2619_);
lean_ctor_set(v___x_2001_, 0, v___x_2624_);
v___x_2628_ = v___x_2001_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_k_2619_);
lean_ctor_set(v_reuseFailAlloc_2629_, 2, v_v_2620_);
lean_ctor_set(v_reuseFailAlloc_2629_, 3, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2629_, 4, v_r_2618_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_size_2635_; lean_object* v_k_2636_; lean_object* v_v_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2648_; 
v_size_2635_ = lean_ctor_get(v_r_1999_, 0);
v_k_2636_ = lean_ctor_get(v_r_1999_, 1);
v_v_2637_ = lean_ctor_get(v_r_1999_, 2);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_r_1999_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; lean_object* v_unused_2650_; 
v_unused_2649_ = lean_ctor_get(v_r_1999_, 4);
lean_dec(v_unused_2649_);
v_unused_2650_ = lean_ctor_get(v_r_1999_, 3);
lean_dec(v_unused_2650_);
v___x_2639_ = v_r_1999_;
v_isShared_2640_ = v_isSharedCheck_2648_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_v_2637_);
lean_inc(v_k_2636_);
lean_inc(v_size_2635_);
lean_dec(v_r_1999_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2648_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 3, v_r_2618_);
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_size_2635_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_k_2636_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_v_2637_);
lean_ctor_set(v_reuseFailAlloc_2647_, 3, v_r_2618_);
lean_ctor_set(v_reuseFailAlloc_2647_, 4, v_r_2618_);
v___x_2642_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = lean_unsigned_to_nat(2u);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 4, v___x_2642_);
lean_ctor_set(v___x_2001_, 3, v_r_2618_);
lean_ctor_set(v___x_2001_, 0, v___x_2643_);
v___x_2645_ = v___x_2001_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v_r_2618_);
lean_ctor_set(v_reuseFailAlloc_2646_, 4, v___x_2642_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
else
{
lean_object* v___x_2652_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 3, v_r_1999_);
lean_ctor_set(v___x_2001_, 0, v___x_2481_);
v___x_2652_ = v___x_2001_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_k_1996_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_v_1997_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_r_1999_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v_r_1999_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
}
else
{
return v_t_1995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2656_, lean_object* v_t_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2656_, v_t_2657_);
lean_dec(v_k_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object* v_id_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v_receivers_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_st_ref_get(v___y_2665_);
v_receivers_2668_ = lean_ctor_get(v___x_2667_, 7);
lean_inc(v_receivers_2668_);
v___x_2669_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2668_, v_id_2664_);
lean_dec(v_receivers_2668_);
if (lean_obj_tag(v___x_2669_) == 1)
{
lean_object* v_val_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_val_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_val_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2667_);
lean_ctor_set(v___x_2671_, 1, v_val_2670_);
v___x_2672_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2671_, v___y_2665_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2702_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2702_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2702_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_fst_2677_; lean_object* v_producers_2678_; lean_object* v_waiters_2679_; lean_object* v_capacity_2680_; lean_object* v_size_2681_; lean_object* v_buffer_2682_; lean_object* v_write_2683_; lean_object* v_read_2684_; lean_object* v_receivers_2685_; lean_object* v_nextId_2686_; uint8_t v_closed_2687_; lean_object* v_pos_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2701_; 
v_fst_2677_ = lean_ctor_get(v_a_2673_, 0);
lean_inc(v_fst_2677_);
lean_dec(v_a_2673_);
v_producers_2678_ = lean_ctor_get(v_fst_2677_, 0);
v_waiters_2679_ = lean_ctor_get(v_fst_2677_, 1);
v_capacity_2680_ = lean_ctor_get(v_fst_2677_, 2);
v_size_2681_ = lean_ctor_get(v_fst_2677_, 3);
v_buffer_2682_ = lean_ctor_get(v_fst_2677_, 4);
v_write_2683_ = lean_ctor_get(v_fst_2677_, 5);
v_read_2684_ = lean_ctor_get(v_fst_2677_, 6);
v_receivers_2685_ = lean_ctor_get(v_fst_2677_, 7);
v_nextId_2686_ = lean_ctor_get(v_fst_2677_, 8);
v_closed_2687_ = lean_ctor_get_uint8(v_fst_2677_, sizeof(void*)*10);
v_pos_2688_ = lean_ctor_get(v_fst_2677_, 9);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_fst_2677_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2690_ = v_fst_2677_;
v_isShared_2691_ = v_isSharedCheck_2701_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_pos_2688_);
lean_inc(v_nextId_2686_);
lean_inc(v_receivers_2685_);
lean_inc(v_read_2684_);
lean_inc(v_write_2683_);
lean_inc(v_buffer_2682_);
lean_inc(v_size_2681_);
lean_inc(v_capacity_2680_);
lean_inc(v_waiters_2679_);
lean_inc(v_producers_2678_);
lean_dec(v_fst_2677_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2701_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_id_2664_, v_receivers_2685_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 7, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_producers_2678_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_waiters_2679_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v_capacity_2680_);
lean_ctor_set(v_reuseFailAlloc_2700_, 3, v_size_2681_);
lean_ctor_set(v_reuseFailAlloc_2700_, 4, v_buffer_2682_);
lean_ctor_set(v_reuseFailAlloc_2700_, 5, v_write_2683_);
lean_ctor_set(v_reuseFailAlloc_2700_, 6, v_read_2684_);
lean_ctor_set(v_reuseFailAlloc_2700_, 7, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2700_, 8, v_nextId_2686_);
lean_ctor_set(v_reuseFailAlloc_2700_, 9, v_pos_2688_);
lean_ctor_set_uint8(v_reuseFailAlloc_2700_, sizeof(void*)*10, v_closed_2687_);
v___x_2694_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2695_ = lean_st_ref_swap(v___y_2665_, v___x_2694_);
lean_dec(v___x_2695_);
v___x_2696_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0));
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2696_);
v___x_2698_ = v___x_2675_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
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
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
v_a_2703_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2672_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2672_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec(v___x_2669_);
lean_dec(v___x_2667_);
v___x_2711_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1));
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object* v_id_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec(v_id_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object* v_bd_2717_){
_start:
{
lean_object* v_state_2719_; lean_object* v_id_2720_; lean_object* v___f_2721_; lean_object* v___x_2722_; 
v_state_2719_ = lean_ctor_get(v_bd_2717_, 0);
lean_inc_ref(v_state_2719_);
v_id_2720_ = lean_ctor_get(v_bd_2717_, 1);
lean_inc(v_id_2720_);
lean_dec_ref(v_bd_2717_);
v___f_2721_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2721_, 0, v_id_2720_);
v___x_2722_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_2719_, v___f_2721_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2747_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2747_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2747_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___y_2728_; 
if (lean_obj_tag(v_a_2723_) == 0)
{
lean_object* v_a_2733_; uint8_t v___x_2734_; 
v_a_2733_ = lean_ctor_get(v_a_2723_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v_a_2723_, 1);
v___x_2734_ = lean_unbox(v_a_2733_);
lean_dec(v_a_2733_);
switch(v___x_2734_)
{
case 0:
{
lean_object* v___x_2735_; 
v___x_2735_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_2728_ = v___x_2735_;
goto v___jp_2727_;
}
case 1:
{
lean_object* v___x_2736_; 
v___x_2736_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_2728_ = v___x_2736_;
goto v___jp_2727_;
}
default: 
{
lean_object* v___x_2737_; 
v___x_2737_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_2728_ = v___x_2737_;
goto v___jp_2727_;
}
}
}
else
{
lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2745_; 
lean_del_object(v___x_2725_);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_a_2723_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; 
v_unused_2746_ = lean_ctor_get(v_a_2723_, 0);
lean_dec(v_unused_2746_);
v___x_2739_ = v_a_2723_;
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
else
{
lean_dec(v_a_2723_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = lean_box(0);
if (v_isShared_2740_ == 0)
{
lean_ctor_set_tag(v___x_2739_, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2741_);
v___x_2743_ = v___x_2739_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
v___jp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
lean_inc_ref(v___y_2728_);
v___x_2729_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___y_2728_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 1);
lean_ctor_set(v___x_2725_, 0, v___x_2729_);
v___x_2731_ = v___x_2725_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
v_a_2748_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2722_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2722_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object* v_bd_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object* v_00_u03b1_2759_, lean_object* v_bd_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_bd_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(v_00_u03b1_2763_, v_bd_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object* v_00_u03b1_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2768_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2771_, lean_object* v_a_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(v_00_u03b1_2771_, v_a_2772_);
lean_dec(v_a_2772_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object* v_00_u03b1_2775_, lean_object* v_place_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2776_, v_a_2777_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2780_, lean_object* v_place_2781_, lean_object* v_a_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(v_00_u03b1_2780_, v_place_2781_, v_a_2782_);
lean_dec(v_a_2782_);
lean_dec(v_place_2781_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object* v_00_u03b1_2785_, lean_object* v_slot_2786_, lean_object* v_next_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2786_, v_next_2787_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2791_, lean_object* v_slot_2792_, lean_object* v_next_2793_, lean_object* v_a_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(v_00_u03b1_2791_, v_slot_2792_, v_next_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec(v_next_2793_);
lean_dec(v_slot_2792_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object* v_00_u03b1_2797_, lean_object* v_next_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2798_, v_a_2799_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object* v_00_u03b1_2802_, lean_object* v_next_2803_, lean_object* v_a_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(v_00_u03b1_2802_, v_next_2803_, v_a_2804_);
lean_dec(v_a_2804_);
lean_dec(v_next_2803_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object* v_00_u03b4_2807_, lean_object* v_t_2808_, lean_object* v_k_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2808_, v_k_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object* v_00_u03b4_2811_, lean_object* v_t_2812_, lean_object* v_k_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(v_00_u03b4_2811_, v_t_2812_, v_k_2813_);
lean_dec(v_k_2813_);
lean_dec(v_t_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2815_, lean_object* v_inst_2816_, lean_object* v_a_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_2817_, v___y_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_inst_2822_, lean_object* v_a_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2821_, v_inst_2822_, v_a_2823_, v___y_2824_);
lean_dec(v___y_2824_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2827_, lean_object* v_k_2828_, lean_object* v_t_2829_, lean_object* v_h_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2828_, v_t_2829_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2832_, lean_object* v_k_2833_, lean_object* v_t_2834_, lean_object* v_h_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2832_, v_k_2833_, v_t_2834_, v_h_2835_);
lean_dec(v_k_2833_);
return v_res_2836_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2837_, lean_object* v_y_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_nat_dec_lt(v_x_2837_, v_y_2838_);
if (v___x_2839_ == 0)
{
uint8_t v___x_2840_; 
v___x_2840_ = lean_nat_dec_eq(v_x_2837_, v_y_2838_);
if (v___x_2840_ == 0)
{
uint8_t v___x_2841_; 
v___x_2841_ = 2;
return v___x_2841_;
}
else
{
uint8_t v___x_2842_; 
v___x_2842_ = 1;
return v___x_2842_;
}
}
else
{
uint8_t v___x_2843_; 
v___x_2843_ = 0;
return v___x_2843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2844_, lean_object* v_y_2845_){
_start:
{
uint8_t v_res_2846_; lean_object* v_r_2847_; 
v_res_2846_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2844_, v_y_2845_);
lean_dec(v_y_2845_);
lean_dec(v_x_2844_);
v_r_2847_ = lean_box(v_res_2846_);
return v_r_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_unsigned_to_nat(1u);
v___x_2850_ = lean_nat_add(v_x_2848_, v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2851_);
lean_dec(v_x_2851_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2853_, lean_object* v_receiverId_2854_, lean_object* v___f_2855_, lean_object* v_receivers_2856_, lean_object* v_s_2857_){
_start:
{
lean_object* v_producers_2858_; lean_object* v_waiters_2859_; lean_object* v_capacity_2860_; lean_object* v_size_2861_; lean_object* v_buffer_2862_; lean_object* v_write_2863_; lean_object* v_read_2864_; lean_object* v_nextId_2865_; uint8_t v_closed_2866_; lean_object* v_pos_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2877_; 
v_producers_2858_ = lean_ctor_get(v_s_2857_, 0);
v_waiters_2859_ = lean_ctor_get(v_s_2857_, 1);
v_capacity_2860_ = lean_ctor_get(v_s_2857_, 2);
v_size_2861_ = lean_ctor_get(v_s_2857_, 3);
v_buffer_2862_ = lean_ctor_get(v_s_2857_, 4);
v_write_2863_ = lean_ctor_get(v_s_2857_, 5);
v_read_2864_ = lean_ctor_get(v_s_2857_, 6);
v_nextId_2865_ = lean_ctor_get(v_s_2857_, 8);
v_closed_2866_ = lean_ctor_get_uint8(v_s_2857_, sizeof(void*)*10);
v_pos_2867_ = lean_ctor_get(v_s_2857_, 9);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_s_2857_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; 
v_unused_2878_ = lean_ctor_get(v_s_2857_, 7);
lean_dec(v_unused_2878_);
v___x_2869_ = v_s_2857_;
v_isShared_2870_ = v_isSharedCheck_2877_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_pos_2867_);
lean_inc(v_nextId_2865_);
lean_inc(v_read_2864_);
lean_inc(v_write_2863_);
lean_inc(v_buffer_2862_);
lean_inc(v_size_2861_);
lean_inc(v_capacity_2860_);
lean_inc(v_waiters_2859_);
lean_inc(v_producers_2858_);
lean_dec(v_s_2857_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2877_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2871_ = lean_box(0);
v___x_2872_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2853_, v_receiverId_2854_, v___f_2855_, v_receivers_2856_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 7, v___x_2872_);
v___x_2874_ = v___x_2869_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_producers_2858_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_waiters_2859_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_capacity_2860_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_size_2861_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_buffer_2862_);
lean_ctor_set(v_reuseFailAlloc_2876_, 5, v_write_2863_);
lean_ctor_set(v_reuseFailAlloc_2876_, 6, v_read_2864_);
lean_ctor_set(v_reuseFailAlloc_2876_, 7, v___x_2872_);
lean_ctor_set(v_reuseFailAlloc_2876_, 8, v_nextId_2865_);
lean_ctor_set(v_reuseFailAlloc_2876_, 9, v_pos_2867_);
lean_ctor_set_uint8(v_reuseFailAlloc_2876_, sizeof(void*)*10, v_closed_2866_);
v___x_2874_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2871_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
return v___x_2875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_toPure_2882_; lean_object* v___x_2883_; 
v_toPure_2882_ = lean_ctor_get(v_toApplicative_2879_, 1);
lean_inc(v_toPure_2882_);
lean_dec_ref(v_toApplicative_2879_);
v___x_2883_ = lean_apply_2(v_toPure_2882_, lean_box(0), v_a_2880_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2884_, lean_object* v_a_2885_, lean_object* v___f_2886_, lean_object* v_inst_2887_, lean_object* v_toBind_2888_, lean_object* v_a_2889_){
_start:
{
if (lean_obj_tag(v_a_2889_) == 1)
{
lean_object* v___f_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___f_2890_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2890_, 0, v_toApplicative_2884_);
lean_closure_set(v___f_2890_, 1, v_a_2889_);
lean_inc(v_a_2885_);
v___x_2891_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2891_, 0, lean_box(0));
lean_closure_set(v___x_2891_, 1, lean_box(0));
lean_closure_set(v___x_2891_, 2, lean_box(0));
lean_closure_set(v___x_2891_, 3, v_a_2885_);
lean_closure_set(v___x_2891_, 4, v___f_2886_);
v___x_2892_ = lean_apply_2(v_inst_2887_, lean_box(0), v___x_2891_);
v___x_2893_ = lean_apply_4(v_toBind_2888_, lean_box(0), lean_box(0), v___x_2892_, v___f_2890_);
return v___x_2893_;
}
else
{
lean_object* v_toPure_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
lean_dec(v_a_2889_);
lean_dec(v_toBind_2888_);
lean_dec(v_inst_2887_);
lean_dec_ref(v___f_2886_);
v_toPure_2894_ = lean_ctor_get(v_toApplicative_2884_, 1);
lean_inc(v_toPure_2894_);
lean_dec_ref(v_toApplicative_2884_);
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_apply_2(v_toPure_2894_, lean_box(0), v___x_2895_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_2897_, lean_object* v_a_2898_, lean_object* v___f_2899_, lean_object* v_inst_2900_, lean_object* v_toBind_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(v_toApplicative_2897_, v_a_2898_, v___f_2899_, v_inst_2900_, v_toBind_2901_, v_a_2902_);
lean_dec(v_a_2898_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2904_, lean_object* v_receiverId_2905_, lean_object* v___f_2906_, lean_object* v___f_2907_, lean_object* v_toApplicative_2908_, lean_object* v_a_2909_, lean_object* v_inst_2910_, lean_object* v_toBind_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_receivers_2915_; lean_object* v___x_2916_; 
v_receivers_2915_ = lean_ctor_get(v_a_2914_, 7);
lean_inc_n(v_receivers_2915_, 2);
lean_dec_ref(v_a_2914_);
lean_inc(v_receiverId_2905_);
v___x_2916_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2904_, v_receivers_2915_, v_receiverId_2905_);
if (lean_obj_tag(v___x_2916_) == 1)
{
lean_object* v_val_2917_; lean_object* v___f_2918_; lean_object* v___f_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_val_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_val_2917_);
lean_dec_ref_known(v___x_2916_, 1);
v___f_2918_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2918_, 0, v___f_2906_);
lean_closure_set(v___f_2918_, 1, v_receiverId_2905_);
lean_closure_set(v___f_2918_, 2, v___f_2907_);
lean_closure_set(v___f_2918_, 3, v_receivers_2915_);
lean_inc(v_toBind_2911_);
lean_inc(v_inst_2910_);
lean_inc(v_a_2909_);
v___f_2919_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2919_, 0, v_toApplicative_2908_);
lean_closure_set(v___f_2919_, 1, v_a_2909_);
lean_closure_set(v___f_2919_, 2, v___f_2918_);
lean_closure_set(v___f_2919_, 3, v_inst_2910_);
lean_closure_set(v___f_2919_, 4, v_toBind_2911_);
v___x_2920_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2912_, v_inst_2910_, v_inst_2913_, v_val_2917_, v_a_2909_);
v___x_2921_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v___x_2920_, v___f_2919_);
return v___x_2921_;
}
else
{
lean_object* v_toPure_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec(v___x_2916_);
lean_dec(v_receivers_2915_);
lean_dec(v_inst_2913_);
lean_dec_ref(v_inst_2912_);
lean_dec(v_toBind_2911_);
lean_dec(v_inst_2910_);
lean_dec_ref(v___f_2907_);
lean_dec_ref(v___f_2906_);
lean_dec(v_receiverId_2905_);
v_toPure_2922_ = lean_ctor_get(v_toApplicative_2908_, 1);
lean_inc(v_toPure_2922_);
lean_dec_ref(v_toApplicative_2908_);
v___x_2923_ = lean_box(0);
v___x_2924_ = lean_apply_2(v_toPure_2922_, lean_box(0), v___x_2923_);
return v___x_2924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object* v___f_2925_, lean_object* v_receiverId_2926_, lean_object* v___f_2927_, lean_object* v___f_2928_, lean_object* v_toApplicative_2929_, lean_object* v_a_2930_, lean_object* v_inst_2931_, lean_object* v_toBind_2932_, lean_object* v_inst_2933_, lean_object* v_inst_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(v___f_2925_, v_receiverId_2926_, v___f_2927_, v___f_2928_, v_toApplicative_2929_, v_a_2930_, v_inst_2931_, v_toBind_2932_, v_inst_2933_, v_inst_2934_, v_a_2935_);
lean_dec(v_a_2930_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_receiverId_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_toApplicative_2944_; lean_object* v_toBind_2945_; lean_object* v___f_2946_; lean_object* v___f_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_toApplicative_2944_ = lean_ctor_get(v_inst_2939_, 0);
lean_inc_ref(v_toApplicative_2944_);
v_toBind_2945_ = lean_ctor_get(v_inst_2939_, 1);
lean_inc_n(v_toBind_2945_, 2);
v___f_2946_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_2947_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_inst_2940_);
lean_inc_n(v_a_2943_, 2);
v___f_2948_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_2948_, 0, v___f_2946_);
lean_closure_set(v___f_2948_, 1, v_receiverId_2942_);
lean_closure_set(v___f_2948_, 2, v___f_2946_);
lean_closure_set(v___f_2948_, 3, v___f_2947_);
lean_closure_set(v___f_2948_, 4, v_toApplicative_2944_);
lean_closure_set(v___f_2948_, 5, v_a_2943_);
lean_closure_set(v___f_2948_, 6, v_inst_2940_);
lean_closure_set(v___f_2948_, 7, v_toBind_2945_);
lean_closure_set(v___f_2948_, 8, v_inst_2939_);
lean_closure_set(v___f_2948_, 9, v_inst_2941_);
v___x_2949_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2949_, 0, lean_box(0));
lean_closure_set(v___x_2949_, 1, lean_box(0));
lean_closure_set(v___x_2949_, 2, v_a_2943_);
v___x_2950_ = lean_apply_2(v_inst_2940_, lean_box(0), v___x_2949_);
v___x_2951_ = lean_apply_4(v_toBind_2945_, lean_box(0), lean_box(0), v___x_2950_, v___f_2948_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_receiverId_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2952_, v_inst_2953_, v_inst_2954_, v_receiverId_2955_, v_a_2956_);
lean_dec(v_a_2956_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_2958_, lean_object* v_00_u03b1_2959_, lean_object* v_inst_2960_, lean_object* v_inst_2961_, lean_object* v_inst_2962_, lean_object* v_receiverId_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2960_, v_inst_2961_, v_inst_2962_, v_receiverId_2963_, v_a_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object* v_m_2966_, lean_object* v_00_u03b1_2967_, lean_object* v_inst_2968_, lean_object* v_inst_2969_, lean_object* v_inst_2970_, lean_object* v_receiverId_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(v_m_2966_, v_00_u03b1_2967_, v_inst_2968_, v_inst_2969_, v_inst_2970_, v_receiverId_2971_, v_a_2972_);
lean_dec(v_a_2972_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_2974_, lean_object* v_t_2975_){
_start:
{
if (lean_obj_tag(v_t_2975_) == 0)
{
lean_object* v_size_2976_; lean_object* v_k_2977_; lean_object* v_v_2978_; lean_object* v_l_2979_; lean_object* v_r_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2999_; 
v_size_2976_ = lean_ctor_get(v_t_2975_, 0);
v_k_2977_ = lean_ctor_get(v_t_2975_, 1);
v_v_2978_ = lean_ctor_get(v_t_2975_, 2);
v_l_2979_ = lean_ctor_get(v_t_2975_, 3);
v_r_2980_ = lean_ctor_get(v_t_2975_, 4);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_t_2975_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2982_ = v_t_2975_;
v_isShared_2983_ = v_isSharedCheck_2999_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_r_2980_);
lean_inc(v_l_2979_);
lean_inc(v_v_2978_);
lean_inc(v_k_2977_);
lean_inc(v_size_2976_);
lean_dec(v_t_2975_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2999_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
uint8_t v___x_2984_; 
v___x_2984_ = lean_nat_dec_lt(v_k_2974_, v_k_2977_);
if (v___x_2984_ == 0)
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_nat_dec_eq(v_k_2974_, v_k_2977_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2986_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2974_, v_r_2980_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 4, v___x_2986_);
v___x_2988_ = v___x_2982_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_size_2976_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_k_2977_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_v_2978_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v_l_2979_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v___x_2986_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
lean_dec(v_k_2977_);
v___x_2990_ = lean_unsigned_to_nat(1u);
v___x_2991_ = lean_nat_add(v_v_2978_, v___x_2990_);
lean_dec(v_v_2978_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 2, v___x_2991_);
lean_ctor_set(v___x_2982_, 1, v_k_2974_);
v___x_2993_ = v___x_2982_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_size_2976_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_k_2974_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_l_2979_);
lean_ctor_set(v_reuseFailAlloc_2994_, 4, v_r_2980_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2995_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2974_, v_l_2979_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 3, v___x_2995_);
v___x_2997_ = v___x_2982_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_size_2976_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_k_2977_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_v_2978_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v_r_2980_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_dec(v_k_2974_);
return v_t_2975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_3000_, lean_object* v_next_3001_){
_start:
{
lean_object* v___x_3003_; lean_object* v_fst_3005_; lean_object* v_snd_3006_; lean_object* v_value_3008_; lean_object* v_pos_3009_; lean_object* v_remaining_3010_; uint8_t v___x_3011_; 
v___x_3003_ = lean_st_ref_take(v_slot_3000_);
v_value_3008_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_value_3008_);
v_pos_3009_ = lean_ctor_get(v___x_3003_, 1);
lean_inc(v_pos_3009_);
v_remaining_3010_ = lean_ctor_get(v___x_3003_, 2);
lean_inc(v_remaining_3010_);
v___x_3011_ = lean_nat_dec_eq(v_next_3001_, v_pos_3009_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec(v_remaining_3010_);
lean_dec(v_pos_3009_);
lean_dec(v_value_3008_);
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_box(v___x_3011_);
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v_fst_3005_ = v___x_3014_;
v_snd_3006_ = v___x_3003_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3033_; 
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; lean_object* v_unused_3035_; lean_object* v_unused_3036_; 
v_unused_3034_ = lean_ctor_get(v___x_3003_, 2);
lean_dec(v_unused_3034_);
v_unused_3035_ = lean_ctor_get(v___x_3003_, 1);
lean_dec(v_unused_3035_);
v_unused_3036_ = lean_ctor_get(v___x_3003_, 0);
lean_dec(v_unused_3036_);
v___x_3016_ = v___x_3003_;
v_isShared_3017_ = v_isSharedCheck_3033_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v___x_3003_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3033_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3018_ = lean_unsigned_to_nat(1u);
v___x_3019_ = lean_nat_dec_eq(v_remaining_3010_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3020_ = lean_box(v___x_3019_);
lean_inc(v_value_3008_);
v___x_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3021_, 0, v_value_3008_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = lean_nat_sub(v_remaining_3010_, v___x_3018_);
lean_dec(v_remaining_3010_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 2, v___x_3022_);
v___x_3024_ = v___x_3016_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_value_3008_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_pos_3009_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
v_fst_3005_ = v___x_3021_;
v_snd_3006_ = v___x_3024_;
goto v___jp_3004_;
}
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; 
lean_dec(v_remaining_3010_);
v___x_3026_ = lean_box(v___x_3011_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_value_3008_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_unsigned_to_nat(0u);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 2, v___x_3029_);
lean_ctor_set(v___x_3016_, 0, v___x_3028_);
v___x_3031_ = v___x_3016_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_pos_3009_);
lean_ctor_set(v_reuseFailAlloc_3032_, 2, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
v_fst_3005_ = v___x_3027_;
v_snd_3006_ = v___x_3031_;
goto v___jp_3004_;
}
}
}
}
v___jp_3004_:
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_st_ref_put(v_slot_3000_, v_snd_3006_);
return v_fst_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_3037_, lean_object* v_next_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3037_, v_next_3038_);
lean_dec(v_next_3038_);
lean_dec(v_slot_3037_);
return v_res_3040_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_3041_){
_start:
{
lean_object* v___x_3043_; lean_object* v_size_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3043_ = lean_st_ref_get(v_a_3041_);
v_size_3044_ = lean_ctor_get(v___x_3043_, 3);
lean_inc(v_size_3044_);
lean_dec(v___x_3043_);
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = lean_nat_dec_eq(v_size_3044_, v___x_3045_);
lean_dec(v_size_3044_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_3047_, lean_object* v___y_3048_){
_start:
{
uint8_t v_res_3049_; lean_object* v_r_3050_; 
v_res_3049_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3047_);
lean_dec(v_a_3047_);
v_r_3050_ = lean_box(v_res_3049_);
return v_r_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v___x_3054_; lean_object* v_capacity_3055_; lean_object* v_buffer_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3054_ = lean_st_ref_get(v_a_3052_);
v_capacity_3055_ = lean_ctor_get(v___x_3054_, 2);
lean_inc(v_capacity_3055_);
v_buffer_3056_ = lean_ctor_get(v___x_3054_, 4);
lean_inc_ref(v_buffer_3056_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_nat_mod(v_place_3051_, v_capacity_3055_);
lean_dec(v_capacity_3055_);
v___x_3058_ = lean_array_fget(v_buffer_3056_, v___x_3057_);
lean_dec(v___x_3057_);
lean_dec_ref(v_buffer_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_3059_, lean_object* v_a_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3059_, v_a_3060_);
lean_dec(v_a_3060_);
lean_dec(v_place_3059_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = lean_st_ref_get(v_a_3064_);
v___x_3067_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3064_);
if (v___x_3067_ == 0)
{
lean_object* v_capacity_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v_fst_3073_; lean_object* v_snd_3074_; lean_object* v_st_3076_; lean_object* v___y_3077_; 
v_capacity_3068_ = lean_ctor_get(v___x_3066_, 2);
lean_inc(v_capacity_3068_);
v___x_3069_ = 1;
v___x_3070_ = lean_nat_mod(v_next_3063_, v_capacity_3068_);
lean_dec(v_capacity_3068_);
v___x_3071_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_3070_, v_a_3064_);
lean_dec(v___x_3070_);
v___x_3072_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_3071_, v_next_3063_);
lean_dec(v___x_3071_);
v_fst_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_fst_3073_);
v_snd_3074_ = lean_ctor_get(v___x_3072_, 1);
lean_inc(v_snd_3074_);
lean_dec_ref(v___x_3072_);
if (lean_obj_tag(v_fst_3073_) == 1)
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_unbox(v_snd_3074_);
lean_dec(v_snd_3074_);
if (v___x_3079_ == 0)
{
v_st_3076_ = v___x_3066_;
v___y_3077_ = v_a_3064_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3080_; lean_object* v_producers_3081_; lean_object* v_waiters_3082_; lean_object* v_capacity_3083_; lean_object* v_size_3084_; lean_object* v_buffer_3085_; lean_object* v_write_3086_; lean_object* v_read_3087_; lean_object* v_receivers_3088_; lean_object* v_nextId_3089_; uint8_t v_closed_3090_; lean_object* v_pos_3091_; lean_object* v___x_3092_; 
v___x_3080_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_3066_);
v_producers_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc_ref(v_producers_3081_);
v_waiters_3082_ = lean_ctor_get(v___x_3080_, 1);
lean_inc_ref(v_waiters_3082_);
v_capacity_3083_ = lean_ctor_get(v___x_3080_, 2);
lean_inc(v_capacity_3083_);
v_size_3084_ = lean_ctor_get(v___x_3080_, 3);
lean_inc(v_size_3084_);
v_buffer_3085_ = lean_ctor_get(v___x_3080_, 4);
lean_inc_ref(v_buffer_3085_);
v_write_3086_ = lean_ctor_get(v___x_3080_, 5);
lean_inc(v_write_3086_);
v_read_3087_ = lean_ctor_get(v___x_3080_, 6);
lean_inc(v_read_3087_);
v_receivers_3088_ = lean_ctor_get(v___x_3080_, 7);
lean_inc(v_receivers_3088_);
v_nextId_3089_ = lean_ctor_get(v___x_3080_, 8);
lean_inc(v_nextId_3089_);
v_closed_3090_ = lean_ctor_get_uint8(v___x_3080_, sizeof(void*)*10);
v_pos_3091_ = lean_ctor_get(v___x_3080_, 9);
lean_inc(v_pos_3091_);
v___x_3092_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3081_);
if (lean_obj_tag(v___x_3092_) == 1)
{
lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3104_; 
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3104_ == 0)
{
lean_object* v_unused_3105_; lean_object* v_unused_3106_; lean_object* v_unused_3107_; lean_object* v_unused_3108_; lean_object* v_unused_3109_; lean_object* v_unused_3110_; lean_object* v_unused_3111_; lean_object* v_unused_3112_; lean_object* v_unused_3113_; lean_object* v_unused_3114_; 
v_unused_3105_ = lean_ctor_get(v___x_3080_, 9);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v___x_3080_, 8);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v___x_3080_, 7);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v___x_3080_, 6);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v___x_3080_, 5);
lean_dec(v_unused_3109_);
v_unused_3110_ = lean_ctor_get(v___x_3080_, 4);
lean_dec(v_unused_3110_);
v_unused_3111_ = lean_ctor_get(v___x_3080_, 3);
lean_dec(v_unused_3111_);
v_unused_3112_ = lean_ctor_get(v___x_3080_, 2);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v___x_3080_, 1);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v___x_3080_, 0);
lean_dec(v_unused_3114_);
v___x_3094_ = v___x_3080_;
v_isShared_3095_ = v_isSharedCheck_3104_;
goto v_resetjp_3093_;
}
else
{
lean_dec(v___x_3080_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3104_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_val_3096_; lean_object* v_fst_3097_; lean_object* v_snd_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v_val_3096_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_val_3096_);
lean_dec_ref_known(v___x_3092_, 1);
v_fst_3097_ = lean_ctor_get(v_val_3096_, 0);
lean_inc(v_fst_3097_);
v_snd_3098_ = lean_ctor_get(v_val_3096_, 1);
lean_inc(v_snd_3098_);
lean_dec(v_val_3096_);
v___x_3099_ = lean_box(v___x_3069_);
v___x_3100_ = lean_io_promise_resolve(v___x_3099_, v_fst_3097_);
lean_dec(v_fst_3097_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v_snd_3098_);
v___x_3102_ = v___x_3094_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_snd_3098_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_waiters_3082_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_capacity_3083_);
lean_ctor_set(v_reuseFailAlloc_3103_, 3, v_size_3084_);
lean_ctor_set(v_reuseFailAlloc_3103_, 4, v_buffer_3085_);
lean_ctor_set(v_reuseFailAlloc_3103_, 5, v_write_3086_);
lean_ctor_set(v_reuseFailAlloc_3103_, 6, v_read_3087_);
lean_ctor_set(v_reuseFailAlloc_3103_, 7, v_receivers_3088_);
lean_ctor_set(v_reuseFailAlloc_3103_, 8, v_nextId_3089_);
lean_ctor_set(v_reuseFailAlloc_3103_, 9, v_pos_3091_);
lean_ctor_set_uint8(v_reuseFailAlloc_3103_, sizeof(void*)*10, v_closed_3090_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
v_st_3076_ = v___x_3102_;
v___y_3077_ = v_a_3064_;
goto v___jp_3075_;
}
}
}
else
{
lean_dec(v___x_3092_);
lean_dec(v_pos_3091_);
lean_dec(v_nextId_3089_);
lean_dec(v_receivers_3088_);
lean_dec(v_read_3087_);
lean_dec(v_write_3086_);
lean_dec_ref(v_buffer_3085_);
lean_dec(v_size_3084_);
lean_dec(v_capacity_3083_);
lean_dec_ref(v_waiters_3082_);
v_st_3076_ = v___x_3080_;
v___y_3077_ = v_a_3064_;
goto v___jp_3075_;
}
}
}
else
{
lean_object* v___x_3115_; 
lean_dec(v_snd_3074_);
lean_dec(v_fst_3073_);
lean_dec(v___x_3066_);
v___x_3115_ = lean_box(0);
return v___x_3115_;
}
v___jp_3075_:
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_st_ref_swap(v___y_3077_, v_st_3076_);
lean_dec(v___x_3078_);
return v_fst_3073_;
}
}
else
{
lean_object* v___x_3116_; 
lean_dec(v___x_3066_);
v___x_3116_ = lean_box(0);
return v___x_3116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_3117_, lean_object* v_a_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3117_, v_a_3118_);
lean_dec(v_a_3118_);
lean_dec(v_next_3117_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v___x_3124_; lean_object* v_receivers_3125_; lean_object* v___x_3126_; 
v___x_3124_ = lean_st_ref_get(v_a_3122_);
v_receivers_3125_ = lean_ctor_get(v___x_3124_, 7);
lean_inc(v_receivers_3125_);
lean_dec(v___x_3124_);
v___x_3126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3125_, v_receiverId_3121_);
if (lean_obj_tag(v___x_3126_) == 1)
{
lean_object* v_val_3127_; lean_object* v___x_3128_; 
v_val_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v___x_3128_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_3127_, v_a_3122_);
lean_dec(v_val_3127_);
if (lean_obj_tag(v___x_3128_) == 1)
{
lean_object* v___x_3129_; lean_object* v_producers_3130_; lean_object* v_waiters_3131_; lean_object* v_capacity_3132_; lean_object* v_size_3133_; lean_object* v_buffer_3134_; lean_object* v_write_3135_; lean_object* v_read_3136_; lean_object* v_nextId_3137_; uint8_t v_closed_3138_; lean_object* v_pos_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3148_; 
v___x_3129_ = lean_st_ref_take(v_a_3122_);
v_producers_3130_ = lean_ctor_get(v___x_3129_, 0);
v_waiters_3131_ = lean_ctor_get(v___x_3129_, 1);
v_capacity_3132_ = lean_ctor_get(v___x_3129_, 2);
v_size_3133_ = lean_ctor_get(v___x_3129_, 3);
v_buffer_3134_ = lean_ctor_get(v___x_3129_, 4);
v_write_3135_ = lean_ctor_get(v___x_3129_, 5);
v_read_3136_ = lean_ctor_get(v___x_3129_, 6);
v_nextId_3137_ = lean_ctor_get(v___x_3129_, 8);
v_closed_3138_ = lean_ctor_get_uint8(v___x_3129_, sizeof(void*)*10);
v_pos_3139_ = lean_ctor_get(v___x_3129_, 9);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v___x_3129_, 7);
lean_dec(v_unused_3149_);
v___x_3141_ = v___x_3129_;
v_isShared_3142_ = v_isSharedCheck_3148_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_pos_3139_);
lean_inc(v_nextId_3137_);
lean_inc(v_read_3136_);
lean_inc(v_write_3135_);
lean_inc(v_buffer_3134_);
lean_inc(v_size_3133_);
lean_inc(v_capacity_3132_);
lean_inc(v_waiters_3131_);
lean_inc(v_producers_3130_);
lean_dec(v___x_3129_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3148_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3121_, v_receivers_3125_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 7, v___x_3143_);
v___x_3145_ = v___x_3141_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_producers_3130_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_waiters_3131_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_capacity_3132_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_size_3133_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_buffer_3134_);
lean_ctor_set(v_reuseFailAlloc_3147_, 5, v_write_3135_);
lean_ctor_set(v_reuseFailAlloc_3147_, 6, v_read_3136_);
lean_ctor_set(v_reuseFailAlloc_3147_, 7, v___x_3143_);
lean_ctor_set(v_reuseFailAlloc_3147_, 8, v_nextId_3137_);
lean_ctor_set(v_reuseFailAlloc_3147_, 9, v_pos_3139_);
lean_ctor_set_uint8(v_reuseFailAlloc_3147_, sizeof(void*)*10, v_closed_3138_);
v___x_3145_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_st_ref_put(v_a_3122_, v___x_3145_);
return v___x_3128_;
}
}
}
else
{
lean_object* v___x_3150_; 
lean_dec(v___x_3128_);
lean_dec(v_receivers_3125_);
lean_dec(v_receiverId_3121_);
v___x_3150_ = lean_box(0);
return v___x_3150_;
}
}
else
{
lean_object* v___x_3151_; 
lean_dec(v___x_3126_);
lean_dec(v_receivers_3125_);
lean_dec(v_receiverId_3121_);
v___x_3151_ = lean_box(0);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3152_, lean_object* v_a_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3152_, v_a_3153_);
lean_dec(v_a_3153_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3156_, v___y_3157_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3160_, v___y_3161_);
lean_dec(v___y_3161_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3164_){
_start:
{
lean_object* v_state_3166_; lean_object* v_id_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; 
v_state_3166_ = lean_ctor_get(v_ch_3164_, 0);
lean_inc_ref(v_state_3166_);
v_id_3167_ = lean_ctor_get(v_ch_3164_, 1);
lean_inc(v_id_3167_);
lean_dec_ref(v_ch_3164_);
v___f_3168_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3168_, 0, v_id_3167_);
v___x_3169_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3166_, v___f_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3170_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3173_, lean_object* v_ch_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3177_, lean_object* v_ch_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3177_, v_ch_3178_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3181_, lean_object* v_receiverId_3182_, lean_object* v_a_3183_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3182_, v_a_3183_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3186_, lean_object* v_receiverId_3187_, lean_object* v_a_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3186_, v_receiverId_3187_, v_a_3188_);
lean_dec(v_a_3188_);
return v_res_3190_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3191_, lean_object* v_a_3192_){
_start:
{
uint8_t v___x_3194_; 
v___x_3194_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3192_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3195_, lean_object* v_a_3196_, lean_object* v___y_3197_){
_start:
{
uint8_t v_res_3198_; lean_object* v_r_3199_; 
v_res_3198_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3195_, v_a_3196_);
lean_dec(v_a_3196_);
v_r_3199_ = lean_box(v_res_3198_);
return v_r_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3200_, lean_object* v_place_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3201_, v_a_3202_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3205_, lean_object* v_place_3206_, lean_object* v_a_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3205_, v_place_3206_, v_a_3207_);
lean_dec(v_a_3207_);
lean_dec(v_place_3206_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3210_, lean_object* v_slot_3211_, lean_object* v_next_3212_, lean_object* v_a_3213_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3211_, v_next_3212_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3216_, lean_object* v_slot_3217_, lean_object* v_next_3218_, lean_object* v_a_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3216_, v_slot_3217_, v_next_3218_, v_a_3219_);
lean_dec(v_a_3219_);
lean_dec(v_next_3218_);
lean_dec(v_slot_3217_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3222_, lean_object* v_next_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3223_, v_a_3224_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3227_, lean_object* v_next_3228_, lean_object* v_a_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3227_, v_next_3228_, v_a_3229_);
lean_dec(v_a_3229_);
lean_dec(v_next_3228_);
return v_res_3231_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3232_, lean_object* v_t_3233_){
_start:
{
if (lean_obj_tag(v_t_3233_) == 0)
{
lean_object* v_k_3234_; lean_object* v_l_3235_; lean_object* v_r_3236_; uint8_t v___x_3237_; 
v_k_3234_ = lean_ctor_get(v_t_3233_, 1);
v_l_3235_ = lean_ctor_get(v_t_3233_, 3);
v_r_3236_ = lean_ctor_get(v_t_3233_, 4);
v___x_3237_ = lean_nat_dec_lt(v_k_3232_, v_k_3234_);
if (v___x_3237_ == 0)
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_nat_dec_eq(v_k_3232_, v_k_3234_);
if (v___x_3238_ == 0)
{
v_t_3233_ = v_r_3236_;
goto _start;
}
else
{
return v___x_3238_;
}
}
else
{
v_t_3233_ = v_l_3235_;
goto _start;
}
}
else
{
uint8_t v___x_3241_; 
v___x_3241_ = 0;
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3242_, lean_object* v_t_3243_){
_start:
{
uint8_t v_res_3244_; lean_object* v_r_3245_; 
v_res_3244_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3242_, v_t_3243_);
lean_dec(v_t_3243_);
lean_dec(v_k_3242_);
v_r_3245_ = lean_box(v_res_3244_);
return v_r_3245_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = lean_box(0);
v___x_3247_ = lean_task_pure(v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3248_, lean_object* v___f_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v___x_3252_; lean_object* v_receivers_3253_; uint8_t v___x_3254_; 
v___x_3252_ = lean_st_ref_get(v___y_3250_);
v_receivers_3253_ = lean_ctor_get(v___x_3252_, 7);
lean_inc(v_receivers_3253_);
lean_dec(v___x_3252_);
v___x_3254_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3248_, v_receivers_3253_);
lean_dec(v_receivers_3253_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; 
lean_dec_ref(v___f_3249_);
lean_dec(v_id_3248_);
v___x_3255_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3255_;
}
else
{
lean_object* v___x_3256_; 
v___x_3256_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3248_, v___y_3250_);
if (lean_obj_tag(v___x_3256_) == 1)
{
lean_object* v___x_3257_; 
lean_dec_ref(v___f_3249_);
v___x_3257_ = lean_task_pure(v___x_3256_);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; uint8_t v_closed_3259_; 
lean_dec(v___x_3256_);
v___x_3258_ = lean_st_ref_get(v___y_3250_);
v_closed_3259_ = lean_ctor_get_uint8(v___x_3258_, sizeof(void*)*10);
lean_dec(v___x_3258_);
if (v_closed_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v_producers_3262_; lean_object* v_waiters_3263_; lean_object* v_capacity_3264_; lean_object* v_size_3265_; lean_object* v_buffer_3266_; lean_object* v_write_3267_; lean_object* v_read_3268_; lean_object* v_receivers_3269_; lean_object* v_nextId_3270_; uint8_t v_closed_3271_; lean_object* v_pos_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3286_; 
v___x_3260_ = lean_io_promise_new();
v___x_3261_ = lean_st_ref_take(v___y_3250_);
v_producers_3262_ = lean_ctor_get(v___x_3261_, 0);
v_waiters_3263_ = lean_ctor_get(v___x_3261_, 1);
v_capacity_3264_ = lean_ctor_get(v___x_3261_, 2);
v_size_3265_ = lean_ctor_get(v___x_3261_, 3);
v_buffer_3266_ = lean_ctor_get(v___x_3261_, 4);
v_write_3267_ = lean_ctor_get(v___x_3261_, 5);
v_read_3268_ = lean_ctor_get(v___x_3261_, 6);
v_receivers_3269_ = lean_ctor_get(v___x_3261_, 7);
v_nextId_3270_ = lean_ctor_get(v___x_3261_, 8);
v_closed_3271_ = lean_ctor_get_uint8(v___x_3261_, sizeof(void*)*10);
v_pos_3272_ = lean_ctor_get(v___x_3261_, 9);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3274_ = v___x_3261_;
v_isShared_3275_ = v_isSharedCheck_3286_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_pos_3272_);
lean_inc(v_nextId_3270_);
lean_inc(v_receivers_3269_);
lean_inc(v_read_3268_);
lean_inc(v_write_3267_);
lean_inc(v_buffer_3266_);
lean_inc(v_size_3265_);
lean_inc(v_capacity_3264_);
lean_inc(v_waiters_3263_);
lean_inc(v_producers_3262_);
lean_dec(v___x_3261_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3286_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3276_ = lean_box(0);
lean_inc(v___x_3260_);
v___x_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3260_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = l_Std_Queue_enqueue___redArg(v___x_3277_, v_waiters_3263_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 1, v___x_3278_);
v___x_3280_ = v___x_3274_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_producers_3262_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_capacity_3264_);
lean_ctor_set(v_reuseFailAlloc_3285_, 3, v_size_3265_);
lean_ctor_set(v_reuseFailAlloc_3285_, 4, v_buffer_3266_);
lean_ctor_set(v_reuseFailAlloc_3285_, 5, v_write_3267_);
lean_ctor_set(v_reuseFailAlloc_3285_, 6, v_read_3268_);
lean_ctor_set(v_reuseFailAlloc_3285_, 7, v_receivers_3269_);
lean_ctor_set(v_reuseFailAlloc_3285_, 8, v_nextId_3270_);
lean_ctor_set(v_reuseFailAlloc_3285_, 9, v_pos_3272_);
lean_ctor_set_uint8(v_reuseFailAlloc_3285_, sizeof(void*)*10, v_closed_3271_);
v___x_3280_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3281_ = lean_st_ref_put(v___y_3250_, v___x_3280_);
v___x_3282_ = lean_io_promise_result_opt(v___x_3260_);
lean_dec(v___x_3260_);
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = lean_io_bind_task(v___x_3282_, v___f_3249_, v___x_3283_, v_closed_3259_);
return v___x_3284_;
}
}
}
else
{
lean_object* v___x_3287_; 
lean_dec_ref(v___f_3249_);
v___x_3287_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3288_, lean_object* v___f_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3288_, v___f_3289_, v___y_3290_);
lean_dec(v___y_3290_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3293_, lean_object* v_res_3294_){
_start:
{
if (lean_obj_tag(v_res_3294_) == 0)
{
lean_dec_ref(v_ch_3293_);
goto v___jp_3296_;
}
else
{
lean_object* v_val_3298_; uint8_t v___x_3299_; 
v_val_3298_ = lean_ctor_get(v_res_3294_, 0);
v___x_3299_ = lean_unbox(v_val_3298_);
if (v___x_3299_ == 0)
{
lean_dec_ref(v_ch_3293_);
goto v___jp_3296_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3293_);
return v___x_3300_;
}
}
v___jp_3296_:
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3301_, lean_object* v_res_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3301_, v_res_3302_);
lean_dec(v_res_3302_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3305_){
_start:
{
lean_object* v_state_3307_; lean_object* v_id_3308_; lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v___x_3311_; 
v_state_3307_ = lean_ctor_get(v_ch_3305_, 0);
lean_inc_ref(v_state_3307_);
v_id_3308_ = lean_ctor_get(v_ch_3305_, 1);
lean_inc(v_id_3308_);
v___f_3309_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3309_, 0, v_ch_3305_);
v___f_3310_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3310_, 0, v_id_3308_);
lean_closure_set(v___f_3310_, 1, v___f_3309_);
v___x_3311_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3307_, v___f_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3315_, lean_object* v_ch_3316_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3316_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3319_, lean_object* v_ch_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3319_, v_ch_3320_);
return v_res_3322_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3323_, lean_object* v_k_3324_, lean_object* v_t_3325_){
_start:
{
uint8_t v___x_3326_; 
v___x_3326_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3324_, v_t_3325_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3327_, lean_object* v_k_3328_, lean_object* v_t_3329_){
_start:
{
uint8_t v_res_3330_; lean_object* v_r_3331_; 
v_res_3330_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3327_, v_k_3328_, v_t_3329_);
lean_dec(v_t_3329_);
lean_dec(v_k_3328_);
v_r_3331_ = lean_box(v_res_3330_);
return v_r_3331_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = lean_box(0);
v___x_3333_ = lean_task_pure(v___x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3334_, lean_object* v_ch_3335_, lean_object* v_prio_3336_, lean_object* v_x_3337_){
_start:
{
if (lean_obj_tag(v_x_3337_) == 0)
{
lean_object* v___x_3339_; 
lean_dec(v_prio_3336_);
lean_dec_ref(v_ch_3335_);
lean_dec_ref(v_f_3334_);
v___x_3339_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3339_;
}
else
{
lean_object* v_val_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_val_3340_ = lean_ctor_get(v_x_3337_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v_x_3337_, 1);
lean_inc_ref(v_f_3334_);
v___x_3341_ = lean_apply_2(v_f_3334_, v_val_3340_, lean_box(0));
v___x_3342_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3334_, v_ch_3335_, v_prio_3336_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3343_, lean_object* v_ch_3344_, lean_object* v_prio_3345_, lean_object* v_x_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3343_, v_ch_3344_, v_prio_3345_, v_x_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3349_, lean_object* v_ch_3350_, lean_object* v_prio_3351_){
_start:
{
lean_object* v___f_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; 
lean_inc(v_prio_3351_);
lean_inc_ref(v_ch_3350_);
v___f_3353_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3353_, 0, v_f_3349_);
lean_closure_set(v___f_3353_, 1, v_ch_3350_);
lean_closure_set(v___f_3353_, 2, v_prio_3351_);
v___x_3354_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3350_);
v___x_3355_ = 0;
v___x_3356_ = lean_io_bind_task(v___x_3354_, v___f_3353_, v_prio_3351_, v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3357_, lean_object* v_ch_3358_, lean_object* v_prio_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3357_, v_ch_3358_, v_prio_3359_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3362_, lean_object* v_f_3363_, lean_object* v_ch_3364_, lean_object* v_prio_3365_){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3363_, v_ch_3364_, v_prio_3365_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3368_, lean_object* v_f_3369_, lean_object* v_ch_3370_, lean_object* v_prio_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3368_, v_f_3369_, v_ch_3370_, v_prio_3371_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3374_, lean_object* v_val_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_pos_3377_; lean_object* v_toPure_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_pos_3377_ = lean_ctor_get(v_a_3376_, 1);
v_toPure_3378_ = lean_ctor_get(v_toApplicative_3374_, 1);
lean_inc(v_toPure_3378_);
lean_dec_ref(v_toApplicative_3374_);
v___x_3379_ = lean_nat_dec_eq(v_pos_3377_, v_val_3375_);
v___x_3380_ = lean_box(v___x_3379_);
v___x_3381_ = lean_apply_2(v_toPure_3378_, lean_box(0), v___x_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3382_, lean_object* v_val_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3382_, v_val_3383_, v_a_3384_);
lean_dec_ref(v_a_3384_);
lean_dec(v_val_3383_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3386_, lean_object* v_toBind_3387_, lean_object* v___f_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3390_, 0, lean_box(0));
lean_closure_set(v___x_3390_, 1, lean_box(0));
lean_closure_set(v___x_3390_, 2, v_a_3389_);
v___x_3391_ = lean_apply_2(v_inst_3386_, lean_box(0), v___x_3390_);
v___x_3392_ = lean_apply_4(v_toBind_3387_, lean_box(0), lean_box(0), v___x_3391_, v___f_3388_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3393_, lean_object* v_receiverId_3394_, lean_object* v_toApplicative_3395_, lean_object* v_inst_3396_, lean_object* v_toBind_3397_, lean_object* v_inst_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
uint8_t v_closed_3401_; 
v_closed_3401_ = lean_ctor_get_uint8(v_a_3400_, sizeof(void*)*10);
if (v_closed_3401_ == 0)
{
lean_object* v_capacity_3402_; lean_object* v_size_3403_; lean_object* v_receivers_3404_; lean_object* v___x_3405_; 
v_capacity_3402_ = lean_ctor_get(v_a_3400_, 2);
lean_inc(v_capacity_3402_);
v_size_3403_ = lean_ctor_get(v_a_3400_, 3);
lean_inc(v_size_3403_);
v_receivers_3404_ = lean_ctor_get(v_a_3400_, 7);
lean_inc(v_receivers_3404_);
lean_dec_ref(v_a_3400_);
v___x_3405_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3393_, v_receivers_3404_, v_receiverId_3394_);
if (lean_obj_tag(v___x_3405_) == 1)
{
lean_object* v_val_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; 
v_val_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_val_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = lean_unsigned_to_nat(0u);
v___x_3408_ = lean_nat_dec_eq(v_size_3403_, v___x_3407_);
lean_dec(v_size_3403_);
if (v___x_3408_ == 0)
{
lean_object* v___f_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_inc(v_val_3406_);
v___f_3409_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3409_, 0, v_toApplicative_3395_);
lean_closure_set(v___f_3409_, 1, v_val_3406_);
lean_inc(v_toBind_3397_);
lean_inc(v_inst_3396_);
v___f_3410_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3410_, 0, v_inst_3396_);
lean_closure_set(v___f_3410_, 1, v_toBind_3397_);
lean_closure_set(v___f_3410_, 2, v___f_3409_);
v___x_3411_ = lean_nat_mod(v_val_3406_, v_capacity_3402_);
lean_dec(v_capacity_3402_);
lean_dec(v_val_3406_);
v___x_3412_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3398_, v_inst_3396_, v___x_3411_, v_a_3399_);
v___x_3413_ = lean_apply_4(v_toBind_3397_, lean_box(0), lean_box(0), v___x_3412_, v___f_3410_);
return v___x_3413_;
}
else
{
lean_object* v_toPure_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec(v_val_3406_);
lean_dec(v_capacity_3402_);
lean_dec_ref(v_inst_3398_);
lean_dec(v_toBind_3397_);
lean_dec(v_inst_3396_);
v_toPure_3414_ = lean_ctor_get(v_toApplicative_3395_, 1);
lean_inc(v_toPure_3414_);
lean_dec_ref(v_toApplicative_3395_);
v___x_3415_ = lean_box(v_closed_3401_);
v___x_3416_ = lean_apply_2(v_toPure_3414_, lean_box(0), v___x_3415_);
return v___x_3416_;
}
}
else
{
lean_object* v_toPure_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec(v___x_3405_);
lean_dec(v_size_3403_);
lean_dec(v_capacity_3402_);
lean_dec_ref(v_inst_3398_);
lean_dec(v_toBind_3397_);
lean_dec(v_inst_3396_);
v_toPure_3417_ = lean_ctor_get(v_toApplicative_3395_, 1);
lean_inc(v_toPure_3417_);
lean_dec_ref(v_toApplicative_3395_);
v___x_3418_ = lean_box(v_closed_3401_);
v___x_3419_ = lean_apply_2(v_toPure_3417_, lean_box(0), v___x_3418_);
return v___x_3419_;
}
}
else
{
lean_object* v_toPure_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec_ref(v_a_3400_);
lean_dec_ref(v_inst_3398_);
lean_dec(v_toBind_3397_);
lean_dec(v_inst_3396_);
lean_dec(v_receiverId_3394_);
lean_dec_ref(v___f_3393_);
v_toPure_3420_ = lean_ctor_get(v_toApplicative_3395_, 1);
lean_inc(v_toPure_3420_);
lean_dec_ref(v_toApplicative_3395_);
v___x_3421_ = lean_box(v_closed_3401_);
v___x_3422_ = lean_apply_2(v_toPure_3420_, lean_box(0), v___x_3421_);
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object* v___f_3423_, lean_object* v_receiverId_3424_, lean_object* v_toApplicative_3425_, lean_object* v_inst_3426_, lean_object* v_toBind_3427_, lean_object* v_inst_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(v___f_3423_, v_receiverId_3424_, v_toApplicative_3425_, v_inst_3426_, v_toBind_3427_, v_inst_3428_, v_a_3429_, v_a_3430_);
lean_dec(v_a_3429_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3432_, lean_object* v_inst_3433_, lean_object* v_receiverId_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v_toApplicative_3436_; lean_object* v_toBind_3437_; lean_object* v___f_3438_; lean_object* v___f_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v_toApplicative_3436_ = lean_ctor_get(v_inst_3432_, 0);
lean_inc_ref(v_toApplicative_3436_);
v_toBind_3437_ = lean_ctor_get(v_inst_3432_, 1);
lean_inc_n(v_toBind_3437_, 2);
v___f_3438_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3435_, 2);
lean_inc(v_inst_3433_);
v___f_3439_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3439_, 0, v___f_3438_);
lean_closure_set(v___f_3439_, 1, v_receiverId_3434_);
lean_closure_set(v___f_3439_, 2, v_toApplicative_3436_);
lean_closure_set(v___f_3439_, 3, v_inst_3433_);
lean_closure_set(v___f_3439_, 4, v_toBind_3437_);
lean_closure_set(v___f_3439_, 5, v_inst_3432_);
lean_closure_set(v___f_3439_, 6, v_a_3435_);
v___x_3440_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3440_, 0, lean_box(0));
lean_closure_set(v___x_3440_, 1, lean_box(0));
lean_closure_set(v___x_3440_, 2, v_a_3435_);
v___x_3441_ = lean_apply_2(v_inst_3433_, lean_box(0), v___x_3440_);
v___x_3442_ = lean_apply_4(v_toBind_3437_, lean_box(0), lean_box(0), v___x_3441_, v___f_3439_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object* v_inst_3443_, lean_object* v_inst_3444_, lean_object* v_receiverId_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(v_inst_3443_, v_inst_3444_, v_receiverId_3445_, v_a_3446_);
lean_dec(v_a_3446_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3448_, lean_object* v_00_u03b1_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_receiverId_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v_toApplicative_3456_; lean_object* v_toBind_3457_; lean_object* v___f_3458_; lean_object* v___f_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v_toApplicative_3456_ = lean_ctor_get(v_inst_3450_, 0);
lean_inc_ref(v_toApplicative_3456_);
v_toBind_3457_ = lean_ctor_get(v_inst_3450_, 1);
lean_inc_n(v_toBind_3457_, 2);
v___f_3458_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3455_, 2);
lean_inc(v_inst_3451_);
v___f_3459_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3459_, 0, v___f_3458_);
lean_closure_set(v___f_3459_, 1, v_receiverId_3454_);
lean_closure_set(v___f_3459_, 2, v_toApplicative_3456_);
lean_closure_set(v___f_3459_, 3, v_inst_3451_);
lean_closure_set(v___f_3459_, 4, v_toBind_3457_);
lean_closure_set(v___f_3459_, 5, v_inst_3450_);
lean_closure_set(v___f_3459_, 6, v_a_3455_);
v___x_3460_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3460_, 0, lean_box(0));
lean_closure_set(v___x_3460_, 1, lean_box(0));
lean_closure_set(v___x_3460_, 2, v_a_3455_);
v___x_3461_ = lean_apply_2(v_inst_3451_, lean_box(0), v___x_3460_);
v___x_3462_ = lean_apply_4(v_toBind_3457_, lean_box(0), lean_box(0), v___x_3461_, v___f_3459_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3463_, lean_object* v_00_u03b1_3464_, lean_object* v_inst_3465_, lean_object* v_inst_3466_, lean_object* v_inst_3467_, lean_object* v_inst_3468_, lean_object* v_receiverId_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3463_, v_00_u03b1_3464_, v_inst_3465_, v_inst_3466_, v_inst_3467_, v_inst_3468_, v_receiverId_3469_, v_a_3470_);
lean_dec(v_a_3470_);
lean_dec(v_inst_3468_);
lean_dec(v_inst_3467_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3474_, lean_object* v_lose_3475_){
_start:
{
lean_object* v_finished_3477_; lean_object* v_promise_3478_; lean_object* v___x_3479_; uint8_t v___y_3481_; uint8_t v___x_3489_; 
v_finished_3477_ = lean_ctor_get(v_w_3474_, 0);
v_promise_3478_ = lean_ctor_get(v_w_3474_, 1);
v___x_3479_ = lean_st_ref_take(v_finished_3477_);
v___x_3489_ = lean_unbox(v___x_3479_);
lean_dec(v___x_3479_);
if (v___x_3489_ == 0)
{
uint8_t v___x_3490_; 
v___x_3490_ = 1;
v___y_3481_ = v___x_3490_;
goto v___jp_3480_;
}
else
{
uint8_t v___x_3491_; 
v___x_3491_ = 0;
v___y_3481_ = v___x_3491_;
goto v___jp_3480_;
}
v___jp_3480_:
{
uint8_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3482_ = 1;
v___x_3483_ = lean_box(v___x_3482_);
v___x_3484_ = lean_st_ref_put(v_finished_3477_, v___x_3483_);
if (v___y_3481_ == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_apply_1(v_lose_3475_, lean_box(0));
return v___x_3485_;
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v_lose_3475_);
v___x_3486_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3487_ = lean_io_promise_resolve(v___x_3486_, v_promise_3478_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3492_, lean_object* v_lose_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3492_, v_lose_3493_);
lean_dec_ref(v_w_3492_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3496_, lean_object* v_w_3497_, lean_object* v_lose_3498_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3497_, v_lose_3498_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3501_, lean_object* v_w_3502_, lean_object* v_lose_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3501_, v_w_3502_, v_lose_3503_);
lean_dec_ref(v_w_3502_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v___x_3509_; lean_object* v_receivers_3510_; lean_object* v___x_3511_; 
v___x_3509_ = lean_st_ref_get(v_a_3507_);
v_receivers_3510_ = lean_ctor_get(v___x_3509_, 7);
lean_inc(v_receivers_3510_);
lean_dec(v___x_3509_);
v___x_3511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3510_, v_receiverId_3506_);
if (lean_obj_tag(v___x_3511_) == 1)
{
lean_object* v_val_3512_; lean_object* v___x_3513_; 
v_val_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_val_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3512_, v_a_3507_);
lean_dec(v_val_3512_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3546_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3546_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3546_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
if (lean_obj_tag(v_a_3514_) == 1)
{
lean_object* v___x_3518_; lean_object* v_producers_3519_; lean_object* v_waiters_3520_; lean_object* v_capacity_3521_; lean_object* v_size_3522_; lean_object* v_buffer_3523_; lean_object* v_write_3524_; lean_object* v_read_3525_; lean_object* v_nextId_3526_; uint8_t v_closed_3527_; lean_object* v_pos_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3540_; 
v___x_3518_ = lean_st_ref_take(v_a_3507_);
v_producers_3519_ = lean_ctor_get(v___x_3518_, 0);
v_waiters_3520_ = lean_ctor_get(v___x_3518_, 1);
v_capacity_3521_ = lean_ctor_get(v___x_3518_, 2);
v_size_3522_ = lean_ctor_get(v___x_3518_, 3);
v_buffer_3523_ = lean_ctor_get(v___x_3518_, 4);
v_write_3524_ = lean_ctor_get(v___x_3518_, 5);
v_read_3525_ = lean_ctor_get(v___x_3518_, 6);
v_nextId_3526_ = lean_ctor_get(v___x_3518_, 8);
v_closed_3527_ = lean_ctor_get_uint8(v___x_3518_, sizeof(void*)*10);
v_pos_3528_ = lean_ctor_get(v___x_3518_, 9);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3540_ == 0)
{
lean_object* v_unused_3541_; 
v_unused_3541_ = lean_ctor_get(v___x_3518_, 7);
lean_dec(v_unused_3541_);
v___x_3530_ = v___x_3518_;
v_isShared_3531_ = v_isSharedCheck_3540_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_pos_3528_);
lean_inc(v_nextId_3526_);
lean_inc(v_read_3525_);
lean_inc(v_write_3524_);
lean_inc(v_buffer_3523_);
lean_inc(v_size_3522_);
lean_inc(v_capacity_3521_);
lean_inc(v_waiters_3520_);
lean_inc(v_producers_3519_);
lean_dec(v___x_3518_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3540_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3506_, v_receivers_3510_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 7, v___x_3532_);
v___x_3534_ = v___x_3530_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_producers_3519_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_waiters_3520_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_capacity_3521_);
lean_ctor_set(v_reuseFailAlloc_3539_, 3, v_size_3522_);
lean_ctor_set(v_reuseFailAlloc_3539_, 4, v_buffer_3523_);
lean_ctor_set(v_reuseFailAlloc_3539_, 5, v_write_3524_);
lean_ctor_set(v_reuseFailAlloc_3539_, 6, v_read_3525_);
lean_ctor_set(v_reuseFailAlloc_3539_, 7, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3539_, 8, v_nextId_3526_);
lean_ctor_set(v_reuseFailAlloc_3539_, 9, v_pos_3528_);
lean_ctor_set_uint8(v_reuseFailAlloc_3539_, sizeof(void*)*10, v_closed_3527_);
v___x_3534_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; lean_object* v___x_3537_; 
v___x_3535_ = lean_st_ref_put(v_a_3507_, v___x_3534_);
if (v_isShared_3517_ == 0)
{
v___x_3537_ = v___x_3516_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3514_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
lean_dec(v_a_3514_);
lean_dec(v_receivers_3510_);
lean_dec(v_receiverId_3506_);
v___x_3542_ = lean_box(0);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3542_);
v___x_3544_ = v___x_3516_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_dec(v_receivers_3510_);
lean_dec(v_receiverId_3506_);
return v___x_3513_;
}
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
lean_dec(v___x_3511_);
lean_dec(v_receivers_3510_);
lean_dec(v_receiverId_3506_);
v___x_3547_ = lean_box(0);
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
return v___x_3548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3549_, lean_object* v_a_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3549_, v_a_3550_);
lean_dec(v_a_3550_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3553_, lean_object* v_w_3554_, lean_object* v_lose_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_finished_3558_; lean_object* v_promise_3559_; lean_object* v___x_3560_; uint8_t v___y_3562_; uint8_t v___x_3586_; 
v_finished_3558_ = lean_ctor_get(v_w_3554_, 0);
v_promise_3559_ = lean_ctor_get(v_w_3554_, 1);
v___x_3560_ = lean_st_ref_take(v_finished_3558_);
v___x_3586_ = lean_unbox(v___x_3560_);
lean_dec(v___x_3560_);
if (v___x_3586_ == 0)
{
uint8_t v___x_3587_; 
v___x_3587_ = 1;
v___y_3562_ = v___x_3587_;
goto v___jp_3561_;
}
else
{
uint8_t v___x_3588_; 
v___x_3588_ = 0;
v___y_3562_ = v___x_3588_;
goto v___jp_3561_;
}
v___jp_3561_:
{
uint8_t v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = 1;
v___x_3564_ = lean_box(v___x_3563_);
v___x_3565_ = lean_st_ref_put(v_finished_3558_, v___x_3564_);
if (v___y_3562_ == 0)
{
lean_object* v___x_3566_; 
lean_dec(v___x_3553_);
lean_inc(v___y_3556_);
v___x_3566_ = lean_apply_2(v_lose_3555_, v___y_3556_, lean_box(0));
return v___x_3566_;
}
else
{
lean_object* v___x_3567_; 
lean_dec_ref(v_lose_3555_);
v___x_3567_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3553_, v___y_3556_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3577_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3577_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3577_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3572_, 0, v_a_3568_);
v___x_3573_ = lean_io_promise_resolve(v___x_3572_, v_promise_3559_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3573_);
v___x_3575_ = v___x_3570_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3573_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
v_a_3578_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3567_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3567_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3589_, lean_object* v_w_3590_, lean_object* v_lose_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3589_, v_w_3590_, v_lose_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v_w_3590_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3595_, lean_object* v___x_3596_, lean_object* v_w_3597_, lean_object* v_lose_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3596_, v_w_3597_, v_lose_3598_, v___y_3599_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3602_, lean_object* v___x_3603_, lean_object* v_w_3604_, lean_object* v_lose_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3602_, v___x_3603_, v_w_3604_, v_lose_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v_w_3604_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3615_, lean_object* v___f_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; uint8_t v_closed_3620_; 
v___x_3619_ = lean_st_ref_get(v___y_3617_);
v_closed_3620_ = lean_ctor_get_uint8(v___x_3619_, sizeof(void*)*10);
if (v_closed_3620_ == 0)
{
lean_object* v_capacity_3621_; lean_object* v_size_3622_; lean_object* v_receivers_3623_; lean_object* v___x_3624_; 
v_capacity_3621_ = lean_ctor_get(v___x_3619_, 2);
lean_inc(v_capacity_3621_);
v_size_3622_ = lean_ctor_get(v___x_3619_, 3);
lean_inc(v_size_3622_);
v_receivers_3623_ = lean_ctor_get(v___x_3619_, 7);
lean_inc(v_receivers_3623_);
lean_dec(v___x_3619_);
v___x_3624_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3623_, v_id_3615_);
lean_dec(v_receivers_3623_);
if (lean_obj_tag(v___x_3624_) == 1)
{
lean_object* v_val_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; 
v_val_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_val_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v___x_3626_ = lean_unsigned_to_nat(0u);
v___x_3627_ = lean_nat_dec_eq(v_size_3622_, v___x_3626_);
lean_dec(v_size_3622_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = lean_nat_mod(v_val_3625_, v_capacity_3621_);
lean_dec(v_capacity_3621_);
v___x_3629_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3628_, v___y_3617_);
lean_dec(v___x_3628_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3631_; lean_object* v_pos_3632_; uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3629_, 1);
v___x_3631_ = lean_st_ref_get(v_a_3630_);
lean_dec(v_a_3630_);
v_pos_3632_ = lean_ctor_get(v___x_3631_, 1);
lean_inc(v_pos_3632_);
lean_dec(v___x_3631_);
v___x_3633_ = lean_nat_dec_eq(v_pos_3632_, v_val_3625_);
lean_dec(v_val_3625_);
lean_dec(v_pos_3632_);
v___x_3634_ = lean_box(v___x_3633_);
lean_inc(v___y_3617_);
v___x_3635_ = lean_apply_3(v___f_3616_, v___x_3634_, v___y_3617_, lean_box(0));
return v___x_3635_;
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec(v_val_3625_);
lean_dec_ref(v___f_3616_);
v_a_3636_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3629_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3629_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
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
else
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_dec(v_val_3625_);
lean_dec(v_capacity_3621_);
v___x_3644_ = lean_box(v_closed_3620_);
lean_inc(v___y_3617_);
v___x_3645_ = lean_apply_3(v___f_3616_, v___x_3644_, v___y_3617_, lean_box(0));
return v___x_3645_;
}
}
else
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
lean_dec(v___x_3624_);
lean_dec(v_size_3622_);
lean_dec(v_capacity_3621_);
v___x_3646_ = lean_box(v_closed_3620_);
lean_inc(v___y_3617_);
v___x_3647_ = lean_apply_3(v___f_3616_, v___x_3646_, v___y_3617_, lean_box(0));
return v___x_3647_;
}
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_dec(v___x_3619_);
v___x_3648_ = lean_box(v_closed_3620_);
lean_inc(v___y_3617_);
v___x_3649_ = lean_apply_3(v___f_3616_, v___x_3648_, v___y_3617_, lean_box(0));
return v___x_3649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3650_, lean_object* v___f_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3650_, v___f_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec(v_id_3650_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v_producers_3659_; lean_object* v_waiters_3660_; lean_object* v_capacity_3661_; lean_object* v_size_3662_; lean_object* v_buffer_3663_; lean_object* v_write_3664_; lean_object* v_read_3665_; lean_object* v_receivers_3666_; lean_object* v_nextId_3667_; uint8_t v_closed_3668_; lean_object* v_pos_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3692_; 
v___x_3658_ = lean_st_ref_get(v___y_3656_);
v_producers_3659_ = lean_ctor_get(v___x_3658_, 0);
v_waiters_3660_ = lean_ctor_get(v___x_3658_, 1);
v_capacity_3661_ = lean_ctor_get(v___x_3658_, 2);
v_size_3662_ = lean_ctor_get(v___x_3658_, 3);
v_buffer_3663_ = lean_ctor_get(v___x_3658_, 4);
v_write_3664_ = lean_ctor_get(v___x_3658_, 5);
v_read_3665_ = lean_ctor_get(v___x_3658_, 6);
v_receivers_3666_ = lean_ctor_get(v___x_3658_, 7);
v_nextId_3667_ = lean_ctor_get(v___x_3658_, 8);
v_closed_3668_ = lean_ctor_get_uint8(v___x_3658_, sizeof(void*)*10);
v_pos_3669_ = lean_ctor_get(v___x_3658_, 9);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3671_ = v___x_3658_;
v_isShared_3672_ = v_isSharedCheck_3692_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_pos_3669_);
lean_inc(v_nextId_3667_);
lean_inc(v_receivers_3666_);
lean_inc(v_read_3665_);
lean_inc(v_write_3664_);
lean_inc(v_buffer_3663_);
lean_inc(v_size_3662_);
lean_inc(v_capacity_3661_);
lean_inc(v_waiters_3660_);
lean_inc(v_producers_3659_);
lean_dec(v___x_3658_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3692_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3660_);
if (lean_obj_tag(v___x_3673_) == 1)
{
lean_object* v_val_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3689_; 
v_val_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3689_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_val_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3689_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_fst_3678_; lean_object* v_snd_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v_fst_3678_ = lean_ctor_get(v_val_3674_, 0);
lean_inc(v_fst_3678_);
v_snd_3679_ = lean_ctor_get(v_val_3674_, 1);
lean_inc(v_snd_3679_);
lean_dec(v_val_3674_);
v___x_3680_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3678_, v_____do__lift_3655_);
lean_dec(v_fst_3678_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 1, v_snd_3679_);
v___x_3682_ = v___x_3671_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_producers_3659_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_snd_3679_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_capacity_3661_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v_size_3662_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v_buffer_3663_);
lean_ctor_set(v_reuseFailAlloc_3688_, 5, v_write_3664_);
lean_ctor_set(v_reuseFailAlloc_3688_, 6, v_read_3665_);
lean_ctor_set(v_reuseFailAlloc_3688_, 7, v_receivers_3666_);
lean_ctor_set(v_reuseFailAlloc_3688_, 8, v_nextId_3667_);
lean_ctor_set(v_reuseFailAlloc_3688_, 9, v_pos_3669_);
lean_ctor_set_uint8(v_reuseFailAlloc_3688_, sizeof(void*)*10, v_closed_3668_);
v___x_3682_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3683_ = lean_box(0);
v___x_3684_ = lean_st_ref_swap(v___y_3656_, v___x_3682_);
lean_dec(v___x_3684_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set_tag(v___x_3676_, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3683_);
v___x_3686_ = v___x_3676_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3683_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
lean_dec(v___x_3673_);
lean_del_object(v___x_3671_);
lean_dec(v_pos_3669_);
lean_dec(v_nextId_3667_);
lean_dec(v_receivers_3666_);
lean_dec(v_read_3665_);
lean_dec(v_write_3664_);
lean_dec_ref(v_buffer_3663_);
lean_dec(v_size_3662_);
lean_dec(v_capacity_3661_);
lean_dec_ref(v_producers_3659_);
v___x_3690_ = lean_box(0);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
uint8_t v_____do__lift_3763__boxed_3696_; lean_object* v_res_3697_; 
v_____do__lift_3763__boxed_3696_ = lean_unbox(v_____do__lift_3693_);
v_res_3697_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3763__boxed_3696_, v___y_3694_);
lean_dec(v___y_3694_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3698_, lean_object* v___f_3699_, lean_object* v_id_3700_, uint8_t v_____do__lift_3701_, lean_object* v___y_3702_){
_start:
{
if (v_____do__lift_3701_ == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v_producers_3706_; lean_object* v_waiters_3707_; lean_object* v_capacity_3708_; lean_object* v_size_3709_; lean_object* v_buffer_3710_; lean_object* v_write_3711_; lean_object* v_read_3712_; lean_object* v_receivers_3713_; lean_object* v_nextId_3714_; uint8_t v_closed_3715_; lean_object* v_pos_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3730_; 
lean_dec(v_id_3700_);
v___x_3704_ = lean_io_promise_new();
v___x_3705_ = lean_st_ref_take(v___y_3702_);
v_producers_3706_ = lean_ctor_get(v___x_3705_, 0);
v_waiters_3707_ = lean_ctor_get(v___x_3705_, 1);
v_capacity_3708_ = lean_ctor_get(v___x_3705_, 2);
v_size_3709_ = lean_ctor_get(v___x_3705_, 3);
v_buffer_3710_ = lean_ctor_get(v___x_3705_, 4);
v_write_3711_ = lean_ctor_get(v___x_3705_, 5);
v_read_3712_ = lean_ctor_get(v___x_3705_, 6);
v_receivers_3713_ = lean_ctor_get(v___x_3705_, 7);
v_nextId_3714_ = lean_ctor_get(v___x_3705_, 8);
v_closed_3715_ = lean_ctor_get_uint8(v___x_3705_, sizeof(void*)*10);
v_pos_3716_ = lean_ctor_get(v___x_3705_, 9);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3718_ = v___x_3705_;
v_isShared_3719_ = v_isSharedCheck_3730_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_pos_3716_);
lean_inc(v_nextId_3714_);
lean_inc(v_receivers_3713_);
lean_inc(v_read_3712_);
lean_inc(v_write_3711_);
lean_inc(v_buffer_3710_);
lean_inc(v_size_3709_);
lean_inc(v_capacity_3708_);
lean_inc(v_waiters_3707_);
lean_inc(v_producers_3706_);
lean_dec(v___x_3705_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3730_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3720_, 0, v_waiter_3698_);
lean_inc(v___x_3704_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3704_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = l_Std_Queue_enqueue___redArg(v___x_3721_, v_waiters_3707_);
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 1, v___x_3722_);
v___x_3724_ = v___x_3718_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_producers_3706_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_capacity_3708_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_size_3709_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_buffer_3710_);
lean_ctor_set(v_reuseFailAlloc_3729_, 5, v_write_3711_);
lean_ctor_set(v_reuseFailAlloc_3729_, 6, v_read_3712_);
lean_ctor_set(v_reuseFailAlloc_3729_, 7, v_receivers_3713_);
lean_ctor_set(v_reuseFailAlloc_3729_, 8, v_nextId_3714_);
lean_ctor_set(v_reuseFailAlloc_3729_, 9, v_pos_3716_);
lean_ctor_set_uint8(v_reuseFailAlloc_3729_, sizeof(void*)*10, v_closed_3715_);
v___x_3724_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3725_ = lean_st_ref_put(v___y_3702_, v___x_3724_);
v___x_3726_ = lean_io_promise_result_opt(v___x_3704_);
lean_dec(v___x_3704_);
v___x_3727_ = lean_unsigned_to_nat(0u);
v___x_3728_ = l_EIO_chainTask___redArg(v___x_3726_, v___f_3699_, v___x_3727_, v_____do__lift_3701_);
return v___x_3728_;
}
}
}
else
{
lean_object* v___x_3731_; lean_object* v_lose_3732_; lean_object* v___x_3733_; 
lean_dec_ref(v___f_3699_);
v___x_3731_ = lean_box(v_____do__lift_3701_);
v_lose_3732_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3732_, 0, v___x_3731_);
v___x_3733_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3700_, v_waiter_3698_, v_lose_3732_, v___y_3702_);
lean_dec_ref(v_waiter_3698_);
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3734_, lean_object* v___f_3735_, lean_object* v_id_3736_, lean_object* v_____do__lift_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
uint8_t v_____do__lift_3821__boxed_3740_; lean_object* v_res_3741_; 
v_____do__lift_3821__boxed_3740_ = lean_unbox(v_____do__lift_3737_);
v_res_3741_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3734_, v___f_3735_, v_id_3736_, v_____do__lift_3821__boxed_3740_, v___y_3738_);
lean_dec(v___y_3738_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3744_, lean_object* v_ch_3745_, lean_object* v_res_x3f_3746_){
_start:
{
if (lean_obj_tag(v_res_x3f_3746_) == 0)
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
lean_dec_ref(v_ch_3745_);
lean_dec_ref(v_waiter_3744_);
v___x_3748_ = lean_box(0);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
else
{
lean_object* v_val_3750_; uint8_t v___x_3751_; 
v_val_3750_ = lean_ctor_get(v_res_x3f_3746_, 0);
v___x_3751_ = lean_unbox(v_val_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___f_3752_; lean_object* v___x_3753_; 
lean_dec_ref(v_ch_3745_);
v___f_3752_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3753_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3744_, v___f_3752_);
lean_dec_ref(v_waiter_3744_);
return v___x_3753_;
}
else
{
lean_object* v___x_3754_; 
v___x_3754_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3745_, v_waiter_3744_);
return v___x_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3755_, lean_object* v_ch_3756_, lean_object* v_res_x3f_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3755_, v_ch_3756_, v_res_x3f_3757_);
lean_dec(v_res_x3f_3757_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3760_, lean_object* v_waiter_3761_){
_start:
{
lean_object* v_state_3763_; lean_object* v_id_3764_; lean_object* v___f_3765_; lean_object* v___f_3766_; lean_object* v___f_3767_; lean_object* v___x_3768_; 
v_state_3763_ = lean_ctor_get(v_ch_3760_, 0);
lean_inc_ref(v_state_3763_);
v_id_3764_ = lean_ctor_get(v_ch_3760_, 1);
lean_inc_n(v_id_3764_, 2);
lean_inc_ref(v_waiter_3761_);
v___f_3765_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3765_, 0, v_waiter_3761_);
lean_closure_set(v___f_3765_, 1, v_ch_3760_);
v___f_3766_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3766_, 0, v_waiter_3761_);
lean_closure_set(v___f_3766_, 1, v___f_3765_);
lean_closure_set(v___f_3766_, 2, v_id_3764_);
v___f_3767_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3767_, 0, v_id_3764_);
lean_closure_set(v___f_3767_, 1, v___f_3766_);
v___x_3768_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3763_, v___f_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3769_, lean_object* v_waiter_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3769_, v_waiter_3770_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3773_, lean_object* v_ch_3774_, lean_object* v_waiter_3775_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3774_, v_waiter_3775_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3778_, lean_object* v_ch_3779_, lean_object* v_waiter_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3778_, v_ch_3779_, v_waiter_3780_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3783_, lean_object* v_receiverId_3784_, lean_object* v_a_3785_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3784_, v_a_3785_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3788_, lean_object* v_receiverId_3789_, lean_object* v_a_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3788_, v_receiverId_3789_, v_a_3790_);
lean_dec(v_a_3790_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3793_, lean_object* v_x_3794_){
_start:
{
if (lean_obj_tag(v_x_3794_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3804_; 
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
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3817_; 
v_a_3805_ = lean_ctor_get(v_x_3794_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_x_3794_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3807_ = v_x_3794_;
v_isShared_3808_ = v_isSharedCheck_3817_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v_x_3794_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3817_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_capacity_3809_; lean_object* v_buffer_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v_capacity_3809_ = lean_ctor_get(v_a_3805_, 2);
lean_inc(v_capacity_3809_);
v_buffer_3810_ = lean_ctor_get(v_a_3805_, 4);
lean_inc_ref(v_buffer_3810_);
lean_dec(v_a_3805_);
v___x_3811_ = lean_nat_mod(v_place_3793_, v_capacity_3809_);
lean_dec(v_capacity_3809_);
v___x_3812_ = lean_array_fget(v_buffer_3810_, v___x_3811_);
lean_dec(v___x_3811_);
lean_dec_ref(v_buffer_3810_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3812_);
v___x_3814_ = v___x_3807_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
return v___x_3815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3818_, lean_object* v_x_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3818_, v_x_3819_);
lean_dec(v_place_3818_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3822_, lean_object* v_a_3823_){
_start:
{
lean_object* v___f_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___f_3825_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3825_, 0, v_place_3822_);
v___x_3826_ = lean_unsigned_to_nat(0u);
v___x_3827_ = 0;
v___x_3828_ = lean_st_ref_get(v_a_3823_);
v___x_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
v___x_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
v___x_3831_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3826_, v___x_3827_, v___x_3830_, v___f_3825_);
return v___x_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3832_, lean_object* v_a_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3832_, v_a_3833_);
lean_dec(v_a_3833_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3836_, lean_object* v_place_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3837_, v_a_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3841_, lean_object* v_place_3842_, lean_object* v_a_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3841_, v_place_3842_, v_a_3843_);
lean_dec(v_a_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v___y_3846_){
_start:
{
if (lean_obj_tag(v___y_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
v_a_3847_ = lean_ctor_get(v___y_3846_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___y_3846_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___y_3846_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___y_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3863_; 
v_a_3855_ = lean_ctor_get(v___y_3846_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___y_3846_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3857_ = v___y_3846_;
v_isShared_3858_ = v_isSharedCheck_3863_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___y_3846_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3863_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v_fst_3859_; lean_object* v___x_3861_; 
v_fst_3859_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_fst_3859_);
lean_dec(v_a_3855_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v_fst_3859_);
v___x_3861_ = v___x_3857_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_fst_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_mutex_3864_, lean_object* v_x_3865_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3867_ = lean_io_basemutex_unlock(v_mutex_3864_);
v___x_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
v___x_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_3870_, lean_object* v_x_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_mutex_3870_, v_x_3871_);
lean_dec(v_x_3871_);
lean_dec(v_mutex_3870_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_k_3874_, lean_object* v_ref_3875_, lean_object* v_x_3876_){
_start:
{
if (lean_obj_tag(v_x_3876_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3886_; 
lean_dec(v_ref_3875_);
lean_dec_ref(v_k_3874_);
v_a_3878_ = lean_ctor_get(v_x_3876_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_x_3876_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3880_ = v_x_3876_;
v_isShared_3881_ = v_isSharedCheck_3886_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v_x_3876_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3886_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
return v___x_3884_;
}
}
}
else
{
lean_object* v___x_3887_; 
lean_dec_ref_known(v_x_3876_, 1);
v___x_3887_ = lean_apply_2(v_k_3874_, v_ref_3875_, lean_box(0));
return v___x_3887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_k_3888_, lean_object* v_ref_3889_, lean_object* v_x_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_k_3888_, v_ref_3889_, v_x_3890_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v_mutex_3893_, lean_object* v___f_3894_){
_start:
{
lean_object* v___x_3896_; uint8_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3896_ = lean_unsigned_to_nat(0u);
v___x_3897_ = 0;
v___x_3898_ = lean_io_basemutex_lock(v_mutex_3893_);
v___x_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
v___x_3900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
v___x_3901_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3896_, v___x_3897_, v___x_3900_, v___f_3894_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_3902_, lean_object* v___f_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(v_mutex_3902_, v___f_3903_);
lean_dec(v_mutex_3902_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_3907_, lean_object* v_k_3908_){
_start:
{
lean_object* v_ref_3910_; lean_object* v_mutex_3911_; lean_object* v___f_3912_; lean_object* v___f_3913_; lean_object* v___f_3914_; lean_object* v___f_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___y_3920_; 
v_ref_3910_ = lean_ctor_get(v_mutex_3907_, 0);
lean_inc(v_ref_3910_);
v_mutex_3911_ = lean_ctor_get(v_mutex_3907_, 1);
lean_inc_n(v_mutex_3911_, 2);
lean_dec_ref(v_mutex_3907_);
v___f_3912_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___f_3913_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3913_, 0, v_mutex_3911_);
v___f_3914_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3914_, 0, v_k_3908_);
lean_closure_set(v___f_3914_, 1, v_ref_3910_);
v___f_3915_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3915_, 0, v_mutex_3911_);
lean_closure_set(v___f_3915_, 1, v___f_3914_);
v___x_3916_ = lean_unsigned_to_nat(0u);
v___x_3917_ = 0;
v___x_3918_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_3915_, v___f_3913_, v___x_3916_, v___x_3917_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3922_; 
v_a_3922_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3918_, 1);
if (lean_obj_tag(v_a_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v_a_3923_ = lean_ctor_get(v_a_3922_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_a_3922_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v_a_3922_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v_a_3922_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
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
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
v___y_3920_ = v___x_3928_;
goto v___jp_3919_;
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3939_; 
v_a_3931_ = lean_ctor_get(v_a_3922_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_a_3922_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3933_ = v_a_3922_;
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v_a_3922_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v_fst_3935_; lean_object* v___x_3937_; 
v_fst_3935_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_fst_3935_);
lean_dec(v_a_3931_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v_fst_3935_);
v___x_3937_ = v___x_3933_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_fst_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
v___y_3920_ = v___x_3937_;
goto v___jp_3919_;
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3948_; 
v_a_3940_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3942_ = v___x_3918_;
v_isShared_3943_ = v_isSharedCheck_3948_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3918_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3948_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3944_ = lean_task_map(v___f_3912_, v_a_3940_, v___x_3916_, v___x_3917_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3944_);
v___x_3946_ = v___x_3942_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
v___jp_3919_:
{
lean_object* v___x_3921_; 
v___x_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3921_, 0, v___y_3920_);
return v___x_3921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_3949_, lean_object* v_k_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3949_, v_k_3950_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_3953_, lean_object* v_00_u03b2_3954_, lean_object* v_mutex_3955_, lean_object* v_k_3956_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3955_, v_k_3956_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_3959_, lean_object* v_00_u03b2_3960_, lean_object* v_mutex_3961_, lean_object* v_k_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v_res_3964_; 
v_res_3964_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_3959_, v_00_u03b2_3960_, v_mutex_3961_, v_k_3962_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_3969_, lean_object* v_capacity_3970_, lean_object* v_size_3971_, lean_object* v_buffer_3972_, lean_object* v_write_3973_, lean_object* v_read_3974_, lean_object* v_receivers_3975_, lean_object* v_nextId_3976_, uint8_t v_closed_3977_, lean_object* v_pos_3978_, lean_object* v___y_3979_, lean_object* v_x_3980_){
_start:
{
if (lean_obj_tag(v_x_3980_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3990_; 
lean_dec(v_pos_3978_);
lean_dec(v_nextId_3976_);
lean_dec(v_receivers_3975_);
lean_dec(v_read_3974_);
lean_dec(v_write_3973_);
lean_dec_ref(v_buffer_3972_);
lean_dec(v_size_3971_);
lean_dec(v_capacity_3970_);
lean_dec_ref(v_producers_3969_);
v_a_3982_ = lean_ctor_get(v_x_3980_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v_x_3980_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3984_ = v_x_3980_;
v_isShared_3985_ = v_isSharedCheck_3990_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v_x_3980_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3990_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3982_);
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
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v_a_3991_ = lean_ctor_get(v_x_3980_, 0);
lean_inc(v_a_3991_);
lean_dec_ref_known(v_x_3980_, 1);
v___x_3992_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3992_, 0, v_producers_3969_);
lean_ctor_set(v___x_3992_, 1, v_a_3991_);
lean_ctor_set(v___x_3992_, 2, v_capacity_3970_);
lean_ctor_set(v___x_3992_, 3, v_size_3971_);
lean_ctor_set(v___x_3992_, 4, v_buffer_3972_);
lean_ctor_set(v___x_3992_, 5, v_write_3973_);
lean_ctor_set(v___x_3992_, 6, v_read_3974_);
lean_ctor_set(v___x_3992_, 7, v_receivers_3975_);
lean_ctor_set(v___x_3992_, 8, v_nextId_3976_);
lean_ctor_set(v___x_3992_, 9, v_pos_3978_);
lean_ctor_set_uint8(v___x_3992_, sizeof(void*)*10, v_closed_3977_);
v___x_3993_ = lean_st_ref_swap(v___y_3979_, v___x_3992_);
lean_dec(v___x_3993_);
v___x_3994_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_3994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_3995_, lean_object* v_capacity_3996_, lean_object* v_size_3997_, lean_object* v_buffer_3998_, lean_object* v_write_3999_, lean_object* v_read_4000_, lean_object* v_receivers_4001_, lean_object* v_nextId_4002_, lean_object* v_closed_4003_, lean_object* v_pos_4004_, lean_object* v___y_4005_, lean_object* v_x_4006_, lean_object* v___y_4007_){
_start:
{
uint8_t v_closed_boxed_4008_; lean_object* v_res_4009_; 
v_closed_boxed_4008_ = lean_unbox(v_closed_4003_);
v_res_4009_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_3995_, v_capacity_3996_, v_size_3997_, v_buffer_3998_, v_write_3999_, v_read_4000_, v_receivers_4001_, v_nextId_4002_, v_closed_boxed_4008_, v_pos_4004_, v___y_4005_, v_x_4006_);
lean_dec(v___y_4005_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_4010_){
_start:
{
if (lean_obj_tag(v_x_4010_) == 0)
{
lean_object* v___x_4012_; 
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_x_4010_);
return v___x_4012_;
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4022_; 
v_a_4013_ = lean_ctor_get(v_x_4010_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v_x_4010_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4015_ = v_x_4010_;
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v_x_4010_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4022_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4019_; 
v___x_4017_ = l_List_reverse___redArg(v_a_4013_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v___x_4017_);
v___x_4019_ = v___x_4015_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4017_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_4023_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_4026_, lean_object* v___x_4027_, lean_object* v_x_4028_){
_start:
{
if (lean_obj_tag(v_x_4028_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4038_; 
lean_dec(v___x_4027_);
lean_dec(v_a_4026_);
v_a_4030_ = lean_ctor_get(v_x_4028_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_x_4028_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4032_ = v_x_4028_;
v_isShared_4033_ = v_isSharedCheck_4038_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v_x_4028_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4038_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4036_; 
v___x_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
return v___x_4036_;
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4055_; 
v_a_4039_ = lean_ctor_get(v_x_4028_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_x_4028_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4041_ = v_x_4028_;
v_isShared_4042_ = v_isSharedCheck_4055_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v_x_4028_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4055_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
uint8_t v___x_4043_; 
v___x_4043_ = l_List_isEmpty___redArg(v_a_4026_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4046_; 
lean_dec(v___x_4027_);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v_a_4039_);
lean_ctor_set(v___x_4044_, 1, v_a_4026_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v___x_4044_);
v___x_4046_ = v___x_4041_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4044_);
v___x_4046_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
lean_dec(v_a_4026_);
v___x_4049_ = l_List_reverse___redArg(v_a_4039_);
v___x_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4027_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v___x_4050_);
v___x_4052_ = v___x_4041_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4050_);
v___x_4052_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; 
v___x_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
return v___x_4053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_4056_, lean_object* v___x_4057_, lean_object* v_x_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_4056_, v___x_4057_, v_x_4058_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_4061_){
_start:
{
uint8_t v___y_4064_; 
if (lean_obj_tag(v_x_4061_) == 0)
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v_x_4061_);
return v___x_4068_;
}
else
{
lean_object* v_a_4069_; uint8_t v___x_4070_; 
v_a_4069_ = lean_ctor_get(v_x_4061_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v_x_4061_, 1);
v___x_4070_ = lean_unbox(v_a_4069_);
lean_dec(v_a_4069_);
if (v___x_4070_ == 0)
{
uint8_t v___x_4071_; 
v___x_4071_ = 1;
v___y_4064_ = v___x_4071_;
goto v___jp_4063_;
}
else
{
uint8_t v___x_4072_; 
v___x_4072_ = 0;
v___y_4064_ = v___x_4072_;
goto v___jp_4063_;
}
}
v___jp_4063_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4065_ = lean_box(v___y_4064_);
v___x_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
v___x_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
return v___x_4067_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4073_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_4076_, lean_object* v_x_4077_, lean_object* v_head_4078_, lean_object* v_x_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4076_, v_x_4077_, v_head_4078_, v_x_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_4088_, lean_object* v_x_4089_){
_start:
{
if (lean_obj_tag(v_x_4088_) == 0)
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4091_, 0, v_x_4089_);
v___x_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
else
{
lean_object* v_head_4093_; lean_object* v_tail_4094_; lean_object* v_waiter_4095_; lean_object* v___f_4096_; lean_object* v___x_4097_; uint8_t v___x_4098_; 
v_head_4093_ = lean_ctor_get(v_x_4088_, 0);
lean_inc(v_head_4093_);
v_tail_4094_ = lean_ctor_get(v_x_4088_, 1);
lean_inc(v_tail_4094_);
lean_dec_ref_known(v_x_4088_, 2);
v_waiter_4095_ = lean_ctor_get(v_head_4093_, 1);
lean_inc(v_waiter_4095_);
v___f_4096_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4096_, 0, v_tail_4094_);
lean_closure_set(v___f_4096_, 1, v_x_4089_);
lean_closure_set(v___f_4096_, 2, v_head_4093_);
v___x_4097_ = lean_unsigned_to_nat(0u);
v___x_4098_ = 0;
if (lean_obj_tag(v_waiter_4095_) == 0)
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v___x_4100_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4097_, v___x_4098_, v___x_4099_, v___f_4096_);
return v___x_4100_;
}
else
{
lean_object* v_val_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4114_; 
v_val_4101_ = lean_ctor_get(v_waiter_4095_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v_waiter_4095_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4103_ = v_waiter_4095_;
v_isShared_4104_ = v_isSharedCheck_4114_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_val_4101_);
lean_dec(v_waiter_4095_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4114_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v_finished_4105_; lean_object* v___f_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
v_finished_4105_ = lean_ctor_get(v_val_4101_, 0);
lean_inc(v_finished_4105_);
lean_dec(v_val_4101_);
v___f_4106_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
v___x_4107_ = lean_st_ref_get(v_finished_4105_);
lean_dec(v_finished_4105_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4107_);
v___x_4109_ = v___x_4103_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
v___x_4111_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4097_, v___x_4098_, v___x_4110_, v___f_4106_);
v___x_4112_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4097_, v___x_4098_, v___x_4111_, v___f_4096_);
return v___x_4112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_4115_, lean_object* v_x_4116_, lean_object* v_head_4117_, lean_object* v_x_4118_){
_start:
{
if (lean_obj_tag(v_x_4118_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4128_; 
lean_dec_ref(v_head_4117_);
lean_dec(v_x_4116_);
lean_dec(v_tail_4115_);
v_a_4120_ = lean_ctor_get(v_x_4118_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_x_4118_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4122_ = v_x_4118_;
v_isShared_4123_ = v_isSharedCheck_4128_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v_x_4118_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4128_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
return v___x_4126_;
}
}
}
else
{
lean_object* v_a_4129_; uint8_t v___x_4130_; 
v_a_4129_ = lean_ctor_get(v_x_4118_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v_x_4118_, 1);
v___x_4130_ = lean_unbox(v_a_4129_);
lean_dec(v_a_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; 
lean_dec_ref(v_head_4117_);
v___x_4131_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4115_, v_x_4116_);
return v___x_4131_;
}
else
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4132_, 0, v_head_4117_);
lean_ctor_set(v___x_4132_, 1, v_x_4116_);
v___x_4133_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4115_, v___x_4132_);
return v___x_4133_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_4134_, lean_object* v_x_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4134_, v_x_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v___x_4138_, lean_object* v_eList_4139_, lean_object* v___f_4140_, lean_object* v_x_4141_){
_start:
{
if (lean_obj_tag(v_x_4141_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v___f_4140_);
lean_dec(v_eList_4139_);
lean_dec(v___x_4138_);
v_a_4143_ = lean_ctor_get(v_x_4141_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v_x_4141_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4145_ = v_x_4141_;
v_isShared_4146_ = v_isSharedCheck_4151_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v_x_4141_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4151_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4149_; 
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
return v___x_4149_;
}
}
}
else
{
lean_object* v_a_4152_; lean_object* v___f_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v_a_4152_ = lean_ctor_get(v_x_4141_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v_x_4141_, 1);
lean_inc(v___x_4138_);
v___f_4153_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4153_, 0, v_a_4152_);
lean_closure_set(v___f_4153_, 1, v___x_4138_);
v___x_4154_ = lean_unsigned_to_nat(0u);
v___x_4155_ = 0;
v___x_4156_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4139_, v___x_4138_);
v___x_4157_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4154_, v___x_4155_, v___x_4156_, v___f_4140_);
v___x_4158_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4154_, v___x_4155_, v___x_4157_, v___f_4153_);
return v___x_4158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v___x_4159_, lean_object* v_eList_4160_, lean_object* v___f_4161_, lean_object* v_x_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v___x_4159_, v_eList_4160_, v___f_4161_, v_x_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v_eList_4169_; lean_object* v_dList_4170_; lean_object* v___f_4171_; lean_object* v___x_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; uint8_t v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_eList_4169_ = lean_ctor_get(v_q_4166_, 0);
lean_inc(v_eList_4169_);
v_dList_4170_ = lean_ctor_get(v_q_4166_, 1);
lean_inc(v_dList_4170_);
lean_dec_ref(v_q_4166_);
v___f_4171_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4172_ = lean_box(0);
v___f_4173_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4173_, 0, v___x_4172_);
lean_closure_set(v___f_4173_, 1, v_eList_4169_);
lean_closure_set(v___f_4173_, 2, v___f_4171_);
v___x_4174_ = lean_unsigned_to_nat(0u);
v___x_4175_ = 0;
v___x_4176_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4170_, v___x_4172_);
v___x_4177_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4174_, v___x_4175_, v___x_4176_, v___f_4171_);
v___x_4178_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4174_, v___x_4175_, v___x_4177_, v___f_4173_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4179_, v___y_4180_);
lean_dec(v___y_4180_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4183_, lean_object* v_x_4184_){
_start:
{
if (lean_obj_tag(v_x_4184_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4194_; 
v_a_4186_ = lean_ctor_get(v_x_4184_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v_x_4184_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4188_ = v_x_4184_;
v_isShared_4189_ = v_isSharedCheck_4194_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v_x_4184_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4194_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v_producers_4196_; lean_object* v_waiters_4197_; lean_object* v_capacity_4198_; lean_object* v_size_4199_; lean_object* v_buffer_4200_; lean_object* v_write_4201_; lean_object* v_read_4202_; lean_object* v_receivers_4203_; lean_object* v_nextId_4204_; uint8_t v_closed_4205_; lean_object* v_pos_4206_; lean_object* v___x_4207_; lean_object* v___f_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_a_4195_ = lean_ctor_get(v_x_4184_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v_x_4184_, 1);
v_producers_4196_ = lean_ctor_get(v_a_4195_, 0);
lean_inc_ref(v_producers_4196_);
v_waiters_4197_ = lean_ctor_get(v_a_4195_, 1);
lean_inc_ref(v_waiters_4197_);
v_capacity_4198_ = lean_ctor_get(v_a_4195_, 2);
lean_inc(v_capacity_4198_);
v_size_4199_ = lean_ctor_get(v_a_4195_, 3);
lean_inc(v_size_4199_);
v_buffer_4200_ = lean_ctor_get(v_a_4195_, 4);
lean_inc_ref(v_buffer_4200_);
v_write_4201_ = lean_ctor_get(v_a_4195_, 5);
lean_inc(v_write_4201_);
v_read_4202_ = lean_ctor_get(v_a_4195_, 6);
lean_inc(v_read_4202_);
v_receivers_4203_ = lean_ctor_get(v_a_4195_, 7);
lean_inc(v_receivers_4203_);
v_nextId_4204_ = lean_ctor_get(v_a_4195_, 8);
lean_inc(v_nextId_4204_);
v_closed_4205_ = lean_ctor_get_uint8(v_a_4195_, sizeof(void*)*10);
v_pos_4206_ = lean_ctor_get(v_a_4195_, 9);
lean_inc(v_pos_4206_);
lean_dec(v_a_4195_);
v___x_4207_ = lean_box(v_closed_4205_);
lean_inc(v___y_4183_);
v___f_4208_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4208_, 0, v_producers_4196_);
lean_closure_set(v___f_4208_, 1, v_capacity_4198_);
lean_closure_set(v___f_4208_, 2, v_size_4199_);
lean_closure_set(v___f_4208_, 3, v_buffer_4200_);
lean_closure_set(v___f_4208_, 4, v_write_4201_);
lean_closure_set(v___f_4208_, 5, v_read_4202_);
lean_closure_set(v___f_4208_, 6, v_receivers_4203_);
lean_closure_set(v___f_4208_, 7, v_nextId_4204_);
lean_closure_set(v___f_4208_, 8, v___x_4207_);
lean_closure_set(v___f_4208_, 9, v_pos_4206_);
lean_closure_set(v___f_4208_, 10, v___y_4183_);
v___x_4209_ = lean_unsigned_to_nat(0u);
v___x_4210_ = 0;
v___x_4211_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4197_, v___y_4183_);
v___x_4212_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4209_, v___x_4210_, v___x_4211_, v___f_4208_);
return v___x_4212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4213_, lean_object* v_x_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4213_, v_x_4214_);
lean_dec(v___y_4213_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4217_){
_start:
{
lean_object* v___f_4219_; lean_object* v___x_4220_; uint8_t v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
lean_inc(v___y_4217_);
v___f_4219_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4219_, 0, v___y_4217_);
v___x_4220_ = lean_unsigned_to_nat(0u);
v___x_4221_ = 0;
v___x_4222_ = lean_st_ref_get(v___y_4217_);
v___x_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
v___x_4225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4220_, v___x_4221_, v___x_4224_, v___f_4219_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4226_);
lean_dec(v___y_4226_);
return v_res_4228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4229_, lean_object* v_waiter_4230_){
_start:
{
lean_object* v_val_4233_; lean_object* v___x_4235_; 
v___x_4235_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4229_, v_waiter_4230_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4235_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
lean_ctor_set_tag(v___x_4238_, 1);
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
v_val_4233_ = v___x_4241_;
goto v___jp_4232_;
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
v_a_4244_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4235_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4235_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
lean_ctor_set_tag(v___x_4246_, 0);
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
v_val_4233_ = v___x_4249_;
goto v___jp_4232_;
}
}
}
v___jp_4232_:
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v_val_4233_);
return v___x_4234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4252_, lean_object* v_waiter_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4252_, v_waiter_4253_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4256_){
_start:
{
if (lean_obj_tag(v_x_4256_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4266_; 
v_a_4258_ = lean_ctor_get(v_x_4256_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_x_4256_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4260_ = v_x_4256_;
v_isShared_4261_ = v_isSharedCheck_4266_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v_x_4256_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4266_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4258_);
v___x_4263_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
lean_object* v___x_4264_; 
v___x_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4263_);
return v___x_4264_;
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4276_; 
v_a_4267_ = lean_ctor_get(v_x_4256_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_x_4256_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4269_ = v_x_4256_;
v_isShared_4270_ = v_isSharedCheck_4276_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v_x_4256_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4276_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4271_; lean_object* v___x_4273_; 
v___x_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4271_, 0, v_a_4267_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v___x_4271_);
v___x_4273_ = v___x_4269_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4271_);
v___x_4273_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
lean_object* v___x_4274_; 
v___x_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
return v___x_4274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4277_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4280_, lean_object* v_x_4281_){
_start:
{
if (lean_obj_tag(v_x_4281_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v_x_4280_);
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
lean_object* v___x_4292_; 
lean_dec_ref_known(v_x_4281_, 1);
v___x_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4292_, 0, v_x_4280_);
return v___x_4292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4293_, lean_object* v_x_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4293_, v_x_4294_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4299_, lean_object* v_receiverId_4300_, lean_object* v_receivers_4301_, lean_object* v_x_4302_){
_start:
{
if (lean_obj_tag(v_x_4302_) == 0)
{
lean_object* v___x_4304_; 
lean_dec(v_receivers_4301_);
lean_dec(v_receiverId_4300_);
v___x_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4304_, 0, v_x_4302_);
return v___x_4304_;
}
else
{
lean_object* v_a_4305_; 
v_a_4305_ = lean_ctor_get(v_x_4302_, 0);
if (lean_obj_tag(v_a_4305_) == 1)
{
lean_object* v___f_4306_; lean_object* v___x_4307_; uint8_t v___x_4308_; lean_object* v___x_4309_; lean_object* v_producers_4310_; lean_object* v_waiters_4311_; lean_object* v_capacity_4312_; lean_object* v_size_4313_; lean_object* v_buffer_4314_; lean_object* v_write_4315_; lean_object* v_read_4316_; lean_object* v_nextId_4317_; uint8_t v_closed_4318_; lean_object* v_pos_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4330_; 
v___f_4306_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4306_, 0, v_x_4302_);
v___x_4307_ = lean_unsigned_to_nat(0u);
v___x_4308_ = 0;
v___x_4309_ = lean_st_ref_take(v_a_4299_);
v_producers_4310_ = lean_ctor_get(v___x_4309_, 0);
v_waiters_4311_ = lean_ctor_get(v___x_4309_, 1);
v_capacity_4312_ = lean_ctor_get(v___x_4309_, 2);
v_size_4313_ = lean_ctor_get(v___x_4309_, 3);
v_buffer_4314_ = lean_ctor_get(v___x_4309_, 4);
v_write_4315_ = lean_ctor_get(v___x_4309_, 5);
v_read_4316_ = lean_ctor_get(v___x_4309_, 6);
v_nextId_4317_ = lean_ctor_get(v___x_4309_, 8);
v_closed_4318_ = lean_ctor_get_uint8(v___x_4309_, sizeof(void*)*10);
v_pos_4319_ = lean_ctor_get(v___x_4309_, 9);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4309_);
if (v_isSharedCheck_4330_ == 0)
{
lean_object* v_unused_4331_; 
v_unused_4331_ = lean_ctor_get(v___x_4309_, 7);
lean_dec(v_unused_4331_);
v___x_4321_ = v___x_4309_;
v_isShared_4322_ = v_isSharedCheck_4330_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_pos_4319_);
lean_inc(v_nextId_4317_);
lean_inc(v_read_4316_);
lean_inc(v_write_4315_);
lean_inc(v_buffer_4314_);
lean_inc(v_size_4313_);
lean_inc(v_capacity_4312_);
lean_inc(v_waiters_4311_);
lean_inc(v_producers_4310_);
lean_dec(v___x_4309_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4330_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4323_; lean_object* v___x_4325_; 
v___x_4323_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4300_, v_receivers_4301_);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 7, v___x_4323_);
v___x_4325_ = v___x_4321_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_producers_4310_);
lean_ctor_set(v_reuseFailAlloc_4329_, 1, v_waiters_4311_);
lean_ctor_set(v_reuseFailAlloc_4329_, 2, v_capacity_4312_);
lean_ctor_set(v_reuseFailAlloc_4329_, 3, v_size_4313_);
lean_ctor_set(v_reuseFailAlloc_4329_, 4, v_buffer_4314_);
lean_ctor_set(v_reuseFailAlloc_4329_, 5, v_write_4315_);
lean_ctor_set(v_reuseFailAlloc_4329_, 6, v_read_4316_);
lean_ctor_set(v_reuseFailAlloc_4329_, 7, v___x_4323_);
lean_ctor_set(v_reuseFailAlloc_4329_, 8, v_nextId_4317_);
lean_ctor_set(v_reuseFailAlloc_4329_, 9, v_pos_4319_);
lean_ctor_set_uint8(v_reuseFailAlloc_4329_, sizeof(void*)*10, v_closed_4318_);
v___x_4325_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4326_ = lean_st_ref_put(v_a_4299_, v___x_4325_);
v___x_4327_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4328_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4307_, v___x_4308_, v___x_4327_, v___f_4306_);
return v___x_4328_;
}
}
}
else
{
lean_object* v___x_4332_; 
lean_dec_ref_known(v_x_4302_, 1);
lean_dec(v_receivers_4301_);
lean_dec(v_receiverId_4300_);
v___x_4332_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4333_, lean_object* v_receiverId_4334_, lean_object* v_receivers_4335_, lean_object* v_x_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4333_, v_receiverId_4334_, v_receivers_4335_, v_x_4336_);
lean_dec(v_a_4333_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4339_){
_start:
{
if (lean_obj_tag(v_x_4339_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4349_; 
v_a_4341_ = lean_ctor_get(v_x_4339_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_x_4339_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4343_ = v_x_4339_;
v_isShared_4344_ = v_isSharedCheck_4349_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v_x_4339_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4349_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; 
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
return v___x_4347_;
}
}
}
else
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4362_; 
v_a_4350_ = lean_ctor_get(v_x_4339_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v_x_4339_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4352_ = v_x_4339_;
v_isShared_4353_ = v_isSharedCheck_4362_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v_x_4339_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4362_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v_size_4354_; lean_object* v___x_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4359_; 
v_size_4354_ = lean_ctor_get(v_a_4350_, 3);
lean_inc(v_size_4354_);
lean_dec(v_a_4350_);
v___x_4355_ = lean_unsigned_to_nat(0u);
v___x_4356_ = lean_nat_dec_eq(v_size_4354_, v___x_4355_);
lean_dec(v_size_4354_);
v___x_4357_ = lean_box(v___x_4356_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4357_);
v___x_4359_ = v___x_4352_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
lean_object* v___x_4360_; 
v___x_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4359_);
return v___x_4360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4363_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4367_){
_start:
{
lean_object* v___f_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___f_4369_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4370_ = lean_unsigned_to_nat(0u);
v___x_4371_ = 0;
v___x_4372_ = lean_st_ref_get(v_a_4367_);
v___x_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4372_);
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
v___x_4375_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4370_, v___x_4371_, v___x_4374_, v___f_4369_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4376_);
lean_dec(v_a_4376_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4379_, lean_object* v_next_4380_){
_start:
{
lean_object* v___x_4382_; lean_object* v_fst_4384_; lean_object* v_snd_4385_; lean_object* v_value_4389_; lean_object* v_pos_4390_; lean_object* v_remaining_4391_; uint8_t v___x_4392_; 
v___x_4382_ = lean_st_ref_take(v_slot_4379_);
v_value_4389_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_value_4389_);
v_pos_4390_ = lean_ctor_get(v___x_4382_, 1);
lean_inc(v_pos_4390_);
v_remaining_4391_ = lean_ctor_get(v___x_4382_, 2);
lean_inc(v_remaining_4391_);
v___x_4392_ = lean_nat_dec_eq(v_next_4380_, v_pos_4390_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_dec(v_remaining_4391_);
lean_dec(v_pos_4390_);
lean_dec(v_value_4389_);
v___x_4393_ = lean_box(0);
v___x_4394_ = lean_box(v___x_4392_);
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v_fst_4384_ = v___x_4395_;
v_snd_4385_ = v___x_4382_;
goto v___jp_4383_;
}
else
{
lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4414_; 
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4414_ == 0)
{
lean_object* v_unused_4415_; lean_object* v_unused_4416_; lean_object* v_unused_4417_; 
v_unused_4415_ = lean_ctor_get(v___x_4382_, 2);
lean_dec(v_unused_4415_);
v_unused_4416_ = lean_ctor_get(v___x_4382_, 1);
lean_dec(v_unused_4416_);
v_unused_4417_ = lean_ctor_get(v___x_4382_, 0);
lean_dec(v_unused_4417_);
v___x_4397_ = v___x_4382_;
v_isShared_4398_ = v_isSharedCheck_4414_;
goto v_resetjp_4396_;
}
else
{
lean_dec(v___x_4382_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4414_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4399_; uint8_t v___x_4400_; 
v___x_4399_ = lean_unsigned_to_nat(1u);
v___x_4400_ = lean_nat_dec_eq(v_remaining_4391_, v___x_4399_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4405_; 
v___x_4401_ = lean_box(v___x_4400_);
lean_inc(v_value_4389_);
v___x_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4402_, 0, v_value_4389_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = lean_nat_sub(v_remaining_4391_, v___x_4399_);
lean_dec(v_remaining_4391_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 2, v___x_4403_);
v___x_4405_ = v___x_4397_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_value_4389_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_pos_4390_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
v_fst_4384_ = v___x_4402_;
v_snd_4385_ = v___x_4405_;
goto v___jp_4383_;
}
}
else
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4412_; 
lean_dec(v_remaining_4391_);
v___x_4407_ = lean_box(v___x_4392_);
v___x_4408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4408_, 0, v_value_4389_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = lean_box(0);
v___x_4410_ = lean_unsigned_to_nat(0u);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 2, v___x_4410_);
lean_ctor_set(v___x_4397_, 0, v___x_4409_);
v___x_4412_ = v___x_4397_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4409_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_pos_4390_);
lean_ctor_set(v_reuseFailAlloc_4413_, 2, v___x_4410_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
v_fst_4384_ = v___x_4408_;
v_snd_4385_ = v___x_4412_;
goto v___jp_4383_;
}
}
}
}
v___jp_4383_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4386_ = lean_st_ref_put(v_slot_4379_, v_snd_4385_);
v___x_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4387_, 0, v_fst_4384_);
v___x_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
return v___x_4388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4418_, lean_object* v_next_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4418_, v_next_4419_);
lean_dec(v_next_4419_);
lean_dec(v_slot_4418_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4422_, uint8_t v_a_4423_, lean_object* v___f_4424_, lean_object* v_x_4425_){
_start:
{
if (lean_obj_tag(v_x_4425_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4435_; 
lean_dec_ref(v___f_4424_);
v_a_4427_ = lean_ctor_get(v_x_4425_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v_x_4425_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4429_ = v_x_4425_;
v_isShared_4430_ = v_isSharedCheck_4435_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v_x_4425_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4435_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
lean_object* v___x_4433_; 
v___x_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
return v___x_4433_;
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v_a_4436_ = lean_ctor_get(v_x_4425_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v_x_4425_, 1);
v___x_4437_ = lean_unsigned_to_nat(0u);
v___x_4438_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4436_, v_next_4422_);
lean_dec(v_a_4436_);
v___x_4439_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4437_, v_a_4423_, v___x_4438_, v___f_4424_);
return v___x_4439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4440_, lean_object* v_a_4441_, lean_object* v___f_4442_, lean_object* v_x_4443_, lean_object* v___y_4444_){
_start:
{
uint8_t v_a_12032__boxed_4445_; lean_object* v_res_4446_; 
v_a_12032__boxed_4445_ = lean_unbox(v_a_4441_);
v_res_4446_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4440_, v_a_12032__boxed_4445_, v___f_4442_, v_x_4443_);
lean_dec(v_next_4440_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4447_, lean_object* v___f_4448_, lean_object* v_____r_4449_, lean_object* v_st_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4453_ = lean_unsigned_to_nat(0u);
v___x_4454_ = lean_st_ref_swap(v___y_4451_, v_st_4450_);
lean_dec(v___x_4454_);
v___x_4455_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4456_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4453_, v_a_4447_, v___x_4455_, v___f_4448_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4457_, lean_object* v___f_4458_, lean_object* v_____r_4459_, lean_object* v_st_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
uint8_t v_a_12074__boxed_4463_; lean_object* v_res_4464_; 
v_a_12074__boxed_4463_ = lean_unbox(v_a_4457_);
v_res_4464_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_12074__boxed_4463_, v___f_4458_, v_____r_4459_, v_st_4460_, v___y_4461_);
lean_dec(v___y_4461_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4465_, lean_object* v_waiters_4466_, lean_object* v_capacity_4467_, lean_object* v_size_4468_, lean_object* v_buffer_4469_, lean_object* v_write_4470_, lean_object* v_read_4471_, lean_object* v_receivers_4472_, lean_object* v_nextId_4473_, uint8_t v_closed_4474_, lean_object* v_pos_4475_, lean_object* v___f_4476_, lean_object* v_a_4477_, lean_object* v_x_4478_){
_start:
{
if (lean_obj_tag(v_x_4478_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4488_; 
lean_dec_ref(v___f_4476_);
lean_dec(v_pos_4475_);
lean_dec(v_nextId_4473_);
lean_dec(v_receivers_4472_);
lean_dec(v_read_4471_);
lean_dec(v_write_4470_);
lean_dec_ref(v_buffer_4469_);
lean_dec(v_size_4468_);
lean_dec(v_capacity_4467_);
lean_dec_ref(v_waiters_4466_);
lean_dec_ref(v_snd_4465_);
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
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
lean_dec_ref_known(v_x_4478_, 1);
v___x_4489_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4489_, 0, v_snd_4465_);
lean_ctor_set(v___x_4489_, 1, v_waiters_4466_);
lean_ctor_set(v___x_4489_, 2, v_capacity_4467_);
lean_ctor_set(v___x_4489_, 3, v_size_4468_);
lean_ctor_set(v___x_4489_, 4, v_buffer_4469_);
lean_ctor_set(v___x_4489_, 5, v_write_4470_);
lean_ctor_set(v___x_4489_, 6, v_read_4471_);
lean_ctor_set(v___x_4489_, 7, v_receivers_4472_);
lean_ctor_set(v___x_4489_, 8, v_nextId_4473_);
lean_ctor_set(v___x_4489_, 9, v_pos_4475_);
lean_ctor_set_uint8(v___x_4489_, sizeof(void*)*10, v_closed_4474_);
v___x_4490_ = lean_box(0);
lean_inc(v_a_4477_);
v___x_4491_ = lean_apply_4(v___f_4476_, v___x_4490_, v___x_4489_, v_a_4477_, lean_box(0));
return v___x_4491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4492_, lean_object* v_waiters_4493_, lean_object* v_capacity_4494_, lean_object* v_size_4495_, lean_object* v_buffer_4496_, lean_object* v_write_4497_, lean_object* v_read_4498_, lean_object* v_receivers_4499_, lean_object* v_nextId_4500_, lean_object* v_closed_4501_, lean_object* v_pos_4502_, lean_object* v___f_4503_, lean_object* v_a_4504_, lean_object* v_x_4505_, lean_object* v___y_4506_){
_start:
{
uint8_t v_closed_boxed_4507_; lean_object* v_res_4508_; 
v_closed_boxed_4507_ = lean_unbox(v_closed_4501_);
v_res_4508_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4492_, v_waiters_4493_, v_capacity_4494_, v_size_4495_, v_buffer_4496_, v_write_4497_, v_read_4498_, v_receivers_4499_, v_nextId_4500_, v_closed_boxed_4507_, v_pos_4502_, v___f_4503_, v_a_4504_, v_x_4505_);
lean_dec(v_a_4504_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4509_, lean_object* v_x_4510_){
_start:
{
if (lean_obj_tag(v_x_4510_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4520_; 
lean_dec(v_fst_4509_);
v_a_4512_ = lean_ctor_get(v_x_4510_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_x_4510_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4514_ = v_x_4510_;
v_isShared_4515_ = v_isSharedCheck_4520_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v_x_4510_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4520_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; 
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
}
}
else
{
lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4528_; 
v_isSharedCheck_4528_ = !lean_is_exclusive(v_x_4510_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; 
v_unused_4529_ = lean_ctor_get(v_x_4510_, 0);
lean_dec(v_unused_4529_);
v___x_4522_ = v_x_4510_;
v_isShared_4523_ = v_isSharedCheck_4528_;
goto v_resetjp_4521_;
}
else
{
lean_dec(v_x_4510_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4528_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v_fst_4509_);
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_fst_4509_);
v___x_4525_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
return v___x_4526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4530_, lean_object* v_x_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4530_, v_x_4531_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, uint8_t v___x_4537_, lean_object* v_x_4538_){
_start:
{
if (lean_obj_tag(v_x_4538_) == 0)
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4548_; 
lean_dec_ref(v_a_4535_);
v_a_4540_ = lean_ctor_get(v_x_4538_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v_x_4538_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4542_ = v_x_4538_;
v_isShared_4543_ = v_isSharedCheck_4548_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v_x_4538_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4548_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
lean_object* v___x_4546_; 
v___x_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4545_);
return v___x_4546_;
}
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4596_; 
v_a_4549_ = lean_ctor_get(v_x_4538_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v_x_4538_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4551_ = v_x_4538_;
v_isShared_4552_ = v_isSharedCheck_4596_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v_x_4538_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4596_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v_fst_4553_; 
v_fst_4553_ = lean_ctor_get(v_a_4549_, 0);
lean_inc(v_fst_4553_);
if (lean_obj_tag(v_fst_4553_) == 1)
{
lean_object* v_snd_4554_; lean_object* v___f_4555_; lean_object* v___x_4556_; lean_object* v___f_4557_; uint8_t v___x_4558_; 
v_snd_4554_ = lean_ctor_get(v_a_4549_, 1);
lean_inc(v_snd_4554_);
lean_dec(v_a_4549_);
v___f_4555_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4555_, 0, v_fst_4553_);
v___x_4556_ = lean_box(v_a_4534_);
lean_inc_ref(v___f_4555_);
v___f_4557_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4557_, 0, v___x_4556_);
lean_closure_set(v___f_4557_, 1, v___f_4555_);
v___x_4558_ = lean_unbox(v_snd_4554_);
lean_dec(v_snd_4554_);
if (v___x_4558_ == 0)
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
lean_dec_ref(v___f_4557_);
lean_del_object(v___x_4551_);
v___x_4559_ = lean_box(0);
v___x_4560_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4534_, v___f_4555_, v___x_4559_, v_a_4535_, v_a_4536_);
return v___x_4560_;
}
else
{
lean_object* v___x_4561_; lean_object* v_producers_4562_; lean_object* v_waiters_4563_; lean_object* v_capacity_4564_; lean_object* v_size_4565_; lean_object* v_buffer_4566_; lean_object* v_write_4567_; lean_object* v_read_4568_; lean_object* v_receivers_4569_; lean_object* v_nextId_4570_; uint8_t v_closed_4571_; lean_object* v_pos_4572_; lean_object* v___x_4573_; 
v___x_4561_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4535_);
v_producers_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc_ref(v_producers_4562_);
v_waiters_4563_ = lean_ctor_get(v___x_4561_, 1);
lean_inc_ref(v_waiters_4563_);
v_capacity_4564_ = lean_ctor_get(v___x_4561_, 2);
lean_inc(v_capacity_4564_);
v_size_4565_ = lean_ctor_get(v___x_4561_, 3);
lean_inc(v_size_4565_);
v_buffer_4566_ = lean_ctor_get(v___x_4561_, 4);
lean_inc_ref(v_buffer_4566_);
v_write_4567_ = lean_ctor_get(v___x_4561_, 5);
lean_inc(v_write_4567_);
v_read_4568_ = lean_ctor_get(v___x_4561_, 6);
lean_inc(v_read_4568_);
v_receivers_4569_ = lean_ctor_get(v___x_4561_, 7);
lean_inc(v_receivers_4569_);
v_nextId_4570_ = lean_ctor_get(v___x_4561_, 8);
lean_inc(v_nextId_4570_);
v_closed_4571_ = lean_ctor_get_uint8(v___x_4561_, sizeof(void*)*10);
v_pos_4572_ = lean_ctor_get(v___x_4561_, 9);
lean_inc(v_pos_4572_);
v___x_4573_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4562_);
if (lean_obj_tag(v___x_4573_) == 1)
{
lean_object* v_val_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v___x_4561_);
lean_dec_ref(v___f_4555_);
v_val_4574_ = lean_ctor_get(v___x_4573_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4576_ = v___x_4573_;
v_isShared_4577_ = v_isSharedCheck_4592_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_val_4574_);
lean_dec(v___x_4573_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4592_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_fst_4578_; lean_object* v_snd_4579_; lean_object* v___x_4580_; lean_object* v___f_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4586_; 
v_fst_4578_ = lean_ctor_get(v_val_4574_, 0);
lean_inc(v_fst_4578_);
v_snd_4579_ = lean_ctor_get(v_val_4574_, 1);
lean_inc(v_snd_4579_);
lean_dec(v_val_4574_);
v___x_4580_ = lean_box(v_closed_4571_);
lean_inc(v_a_4536_);
v___f_4581_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4581_, 0, v_snd_4579_);
lean_closure_set(v___f_4581_, 1, v_waiters_4563_);
lean_closure_set(v___f_4581_, 2, v_capacity_4564_);
lean_closure_set(v___f_4581_, 3, v_size_4565_);
lean_closure_set(v___f_4581_, 4, v_buffer_4566_);
lean_closure_set(v___f_4581_, 5, v_write_4567_);
lean_closure_set(v___f_4581_, 6, v_read_4568_);
lean_closure_set(v___f_4581_, 7, v_receivers_4569_);
lean_closure_set(v___f_4581_, 8, v_nextId_4570_);
lean_closure_set(v___f_4581_, 9, v___x_4580_);
lean_closure_set(v___f_4581_, 10, v_pos_4572_);
lean_closure_set(v___f_4581_, 11, v___f_4557_);
lean_closure_set(v___f_4581_, 12, v_a_4536_);
v___x_4582_ = lean_unsigned_to_nat(0u);
v___x_4583_ = lean_box(v___x_4537_);
v___x_4584_ = lean_io_promise_resolve(v___x_4583_, v_fst_4578_);
lean_dec(v_fst_4578_);
if (v_isShared_4552_ == 0)
{
lean_ctor_set(v___x_4551_, 0, v___x_4584_);
v___x_4586_ = v___x_4551_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4584_);
v___x_4586_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4588_; 
if (v_isShared_4577_ == 0)
{
lean_ctor_set_tag(v___x_4576_, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4586_);
v___x_4588_ = v___x_4576_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4586_);
v___x_4588_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
lean_object* v___x_4589_; 
v___x_4589_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4582_, v_a_4534_, v___x_4588_, v___f_4581_);
return v___x_4589_;
}
}
}
}
else
{
lean_object* v___x_4593_; lean_object* v___x_4594_; 
lean_dec(v___x_4573_);
lean_dec(v_pos_4572_);
lean_dec(v_nextId_4570_);
lean_dec(v_receivers_4569_);
lean_dec(v_read_4568_);
lean_dec(v_write_4567_);
lean_dec_ref(v_buffer_4566_);
lean_dec(v_size_4565_);
lean_dec(v_capacity_4564_);
lean_dec_ref(v_waiters_4563_);
lean_dec_ref(v___f_4557_);
lean_del_object(v___x_4551_);
v___x_4593_ = lean_box(0);
v___x_4594_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4534_, v___f_4555_, v___x_4593_, v___x_4561_, v_a_4536_);
return v___x_4594_;
}
}
}
else
{
lean_object* v___x_4595_; 
lean_dec(v_fst_4553_);
lean_del_object(v___x_4551_);
lean_dec(v_a_4549_);
lean_dec_ref(v_a_4535_);
v___x_4595_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v___x_4600_, lean_object* v_x_4601_, lean_object* v___y_4602_){
_start:
{
uint8_t v_a_12186__boxed_4603_; uint8_t v___x_12188__boxed_4604_; lean_object* v_res_4605_; 
v_a_12186__boxed_4603_ = lean_unbox(v_a_4597_);
v___x_12188__boxed_4604_ = lean_unbox(v___x_4600_);
v_res_4605_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12186__boxed_4603_, v_a_4598_, v_a_4599_, v___x_12188__boxed_4604_, v_x_4601_);
lean_dec(v_a_4599_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_next_4608_, lean_object* v_x_4609_){
_start:
{
if (lean_obj_tag(v_x_4609_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4619_; 
lean_dec(v_next_4608_);
lean_dec_ref(v_a_4606_);
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
lean_object* v_a_4620_; uint8_t v___x_4621_; 
v_a_4620_ = lean_ctor_get(v_x_4609_, 0);
lean_inc(v_a_4620_);
lean_dec_ref_known(v_x_4609_, 1);
v___x_4621_ = lean_unbox(v_a_4620_);
if (v___x_4621_ == 0)
{
lean_object* v_capacity_4622_; uint8_t v___x_4623_; lean_object* v___x_4624_; lean_object* v___f_4625_; lean_object* v___f_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; uint8_t v___x_4630_; lean_object* v___x_4631_; 
v_capacity_4622_ = lean_ctor_get(v_a_4606_, 2);
lean_inc(v_capacity_4622_);
v___x_4623_ = 1;
v___x_4624_ = lean_box(v___x_4623_);
lean_inc(v_a_4607_);
lean_inc_n(v_a_4620_, 2);
v___f_4625_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4625_, 0, v_a_4620_);
lean_closure_set(v___f_4625_, 1, v_a_4606_);
lean_closure_set(v___f_4625_, 2, v_a_4607_);
lean_closure_set(v___f_4625_, 3, v___x_4624_);
lean_inc(v_next_4608_);
v___f_4626_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4626_, 0, v_next_4608_);
lean_closure_set(v___f_4626_, 1, v_a_4620_);
lean_closure_set(v___f_4626_, 2, v___f_4625_);
v___x_4627_ = lean_nat_mod(v_next_4608_, v_capacity_4622_);
lean_dec(v_capacity_4622_);
lean_dec(v_next_4608_);
v___x_4628_ = lean_unsigned_to_nat(0u);
v___x_4629_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4627_, v_a_4607_);
v___x_4630_ = lean_unbox(v_a_4620_);
lean_dec(v_a_4620_);
v___x_4631_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4628_, v___x_4630_, v___x_4629_, v___f_4626_);
return v___x_4631_;
}
else
{
lean_object* v___x_4632_; 
lean_dec(v_a_4620_);
lean_dec(v_next_4608_);
lean_dec_ref(v_a_4606_);
v___x_4632_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_next_4635_, lean_object* v_x_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v_res_4638_; 
v_res_4638_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4633_, v_a_4634_, v_next_4635_, v_x_4636_);
lean_dec(v_a_4634_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4639_, lean_object* v_next_4640_, lean_object* v_x_4641_){
_start:
{
if (lean_obj_tag(v_x_4641_) == 0)
{
lean_object* v_a_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4651_; 
lean_dec(v_next_4640_);
v_a_4643_ = lean_ctor_get(v_x_4641_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v_x_4641_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4645_ = v_x_4641_;
v_isShared_4646_ = v_isSharedCheck_4651_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_a_4643_);
lean_dec(v_x_4641_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4651_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4648_; 
if (v_isShared_4646_ == 0)
{
v___x_4648_ = v___x_4645_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4643_);
v___x_4648_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4649_; 
v___x_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
return v___x_4649_;
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___f_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v_a_4652_ = lean_ctor_get(v_x_4641_, 0);
lean_inc(v_a_4652_);
lean_dec_ref_known(v_x_4641_, 1);
lean_inc(v_a_4639_);
v___f_4653_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4653_, 0, v_a_4652_);
lean_closure_set(v___f_4653_, 1, v_a_4639_);
lean_closure_set(v___f_4653_, 2, v_next_4640_);
v___x_4654_ = lean_unsigned_to_nat(0u);
v___x_4655_ = 0;
v___x_4656_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4639_);
v___x_4657_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4654_, v___x_4655_, v___x_4656_, v___f_4653_);
return v___x_4657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4658_, lean_object* v_next_4659_, lean_object* v_x_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4658_, v_next_4659_, v_x_4660_);
lean_dec(v_a_4658_);
return v_res_4662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v___f_4666_; lean_object* v___x_4667_; uint8_t v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_inc(v_a_4664_);
v___f_4666_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4666_, 0, v_a_4664_);
lean_closure_set(v___f_4666_, 1, v_next_4663_);
v___x_4667_ = lean_unsigned_to_nat(0u);
v___x_4668_ = 0;
v___x_4669_ = lean_st_ref_get(v_a_4664_);
v___x_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4669_);
v___x_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4670_);
v___x_4672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4667_, v___x_4668_, v___x_4671_, v___f_4666_);
return v___x_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4673_, lean_object* v_a_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_res_4676_; 
v_res_4676_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4673_, v_a_4674_);
lean_dec(v_a_4674_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4677_, lean_object* v_a_4678_, lean_object* v_x_4679_){
_start:
{
if (lean_obj_tag(v_x_4679_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4689_; 
lean_dec(v_receiverId_4677_);
v_a_4681_ = lean_ctor_get(v_x_4679_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v_x_4679_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4683_ = v_x_4679_;
v_isShared_4684_ = v_isSharedCheck_4689_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v_x_4679_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4689_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
lean_object* v___x_4687_; 
v___x_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
return v___x_4687_;
}
}
}
else
{
lean_object* v_a_4690_; lean_object* v_receivers_4691_; lean_object* v___x_4692_; 
v_a_4690_ = lean_ctor_get(v_x_4679_, 0);
lean_inc(v_a_4690_);
lean_dec_ref_known(v_x_4679_, 1);
v_receivers_4691_ = lean_ctor_get(v_a_4690_, 7);
lean_inc(v_receivers_4691_);
lean_dec(v_a_4690_);
v___x_4692_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4691_, v_receiverId_4677_);
if (lean_obj_tag(v___x_4692_) == 1)
{
lean_object* v_val_4693_; lean_object* v___f_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
v_val_4693_ = lean_ctor_get(v___x_4692_, 0);
lean_inc(v_val_4693_);
lean_dec_ref_known(v___x_4692_, 1);
lean_inc(v_a_4678_);
v___f_4694_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4694_, 0, v_a_4678_);
lean_closure_set(v___f_4694_, 1, v_receiverId_4677_);
lean_closure_set(v___f_4694_, 2, v_receivers_4691_);
v___x_4695_ = lean_unsigned_to_nat(0u);
v___x_4696_ = 0;
v___x_4697_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4693_, v_a_4678_);
v___x_4698_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4695_, v___x_4696_, v___x_4697_, v___f_4694_);
return v___x_4698_;
}
else
{
lean_object* v___x_4699_; 
lean_dec(v___x_4692_);
lean_dec(v_receivers_4691_);
lean_dec(v_receiverId_4677_);
v___x_4699_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4699_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4700_, lean_object* v_a_4701_, lean_object* v_x_4702_, lean_object* v___y_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4700_, v_a_4701_, v_x_4702_);
lean_dec(v_a_4701_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v___f_4708_; lean_object* v___x_4709_; uint8_t v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
lean_inc(v_a_4706_);
v___f_4708_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4708_, 0, v_receiverId_4705_);
lean_closure_set(v___f_4708_, 1, v_a_4706_);
v___x_4709_ = lean_unsigned_to_nat(0u);
v___x_4710_ = 0;
v___x_4711_ = lean_st_ref_get(v_a_4706_);
v___x_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4711_);
v___x_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4712_);
v___x_4714_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4709_, v___x_4710_, v___x_4713_, v___f_4708_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4715_, lean_object* v_a_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4715_, v_a_4716_);
lean_dec(v_a_4716_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_id_4723_, lean_object* v___y_4724_, lean_object* v___f_4725_, lean_object* v_x_4726_){
_start:
{
if (lean_obj_tag(v_x_4726_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4736_; 
lean_dec_ref(v___f_4725_);
lean_dec(v_id_4723_);
v_a_4728_ = lean_ctor_get(v_x_4726_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v_x_4726_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4730_ = v_x_4726_;
v_isShared_4731_ = v_isSharedCheck_4736_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v_x_4726_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4736_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4734_; 
v___x_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
return v___x_4734_;
}
}
}
else
{
lean_object* v_a_4737_; uint8_t v___x_4738_; 
v_a_4737_ = lean_ctor_get(v_x_4726_, 0);
lean_inc(v_a_4737_);
lean_dec_ref_known(v_x_4726_, 1);
v___x_4738_ = lean_unbox(v_a_4737_);
lean_dec(v_a_4737_);
if (v___x_4738_ == 0)
{
lean_object* v___x_4739_; 
lean_dec_ref(v___f_4725_);
lean_dec(v_id_4723_);
v___x_4739_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__1));
return v___x_4739_;
}
else
{
lean_object* v___x_4740_; uint8_t v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4740_ = lean_unsigned_to_nat(0u);
v___x_4741_ = 0;
v___x_4742_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4723_, v___y_4724_);
v___x_4743_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4740_, v___x_4741_, v___x_4742_, v___f_4725_);
return v___x_4743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_id_4744_, lean_object* v___y_4745_, lean_object* v___f_4746_, lean_object* v_x_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_id_4744_, v___y_4745_, v___f_4746_, v_x_4747_);
lean_dec(v___y_4745_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v_val_4750_, lean_object* v_x_4751_){
_start:
{
if (lean_obj_tag(v_x_4751_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4761_; 
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
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4773_; 
v_a_4762_ = lean_ctor_get(v_x_4751_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v_x_4751_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4764_ = v_x_4751_;
v_isShared_4765_ = v_isSharedCheck_4773_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v_x_4751_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4773_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v_pos_4766_; uint8_t v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4770_; 
v_pos_4766_ = lean_ctor_get(v_a_4762_, 1);
lean_inc(v_pos_4766_);
lean_dec(v_a_4762_);
v___x_4767_ = lean_nat_dec_eq(v_pos_4766_, v_val_4750_);
lean_dec(v_pos_4766_);
v___x_4768_ = lean_box(v___x_4767_);
if (v_isShared_4765_ == 0)
{
lean_ctor_set(v___x_4764_, 0, v___x_4768_);
v___x_4770_ = v___x_4764_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4768_);
v___x_4770_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
lean_object* v___x_4771_; 
v___x_4771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4770_);
return v___x_4771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v_val_4774_, lean_object* v_x_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v_val_4774_, v_x_4775_);
lean_dec(v_val_4774_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v___x_4778_, uint8_t v_closed_4779_, lean_object* v___f_4780_, lean_object* v_x_4781_){
_start:
{
if (lean_obj_tag(v_x_4781_) == 0)
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4791_; 
lean_dec_ref(v___f_4780_);
lean_dec(v___x_4778_);
v_a_4783_ = lean_ctor_get(v_x_4781_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v_x_4781_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4785_ = v_x_4781_;
v_isShared_4786_ = v_isSharedCheck_4791_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v_x_4781_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4791_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
lean_object* v___x_4789_; 
v___x_4789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4788_);
return v___x_4789_;
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4802_; 
v_a_4792_ = lean_ctor_get(v_x_4781_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v_x_4781_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4794_ = v_x_4781_;
v_isShared_4795_ = v_isSharedCheck_4802_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v_x_4781_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4802_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4796_; lean_object* v___x_4798_; 
v___x_4796_ = lean_st_ref_get(v_a_4792_);
lean_dec(v_a_4792_);
if (v_isShared_4795_ == 0)
{
lean_ctor_set(v___x_4794_, 0, v___x_4796_);
v___x_4798_ = v___x_4794_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
v___x_4800_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4778_, v_closed_4779_, v___x_4799_, v___f_4780_);
return v___x_4800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v___x_4803_, lean_object* v_closed_4804_, lean_object* v___f_4805_, lean_object* v_x_4806_, lean_object* v___y_4807_){
_start:
{
uint8_t v_closed_boxed_4808_; lean_object* v_res_4809_; 
v_closed_boxed_4808_ = lean_unbox(v_closed_4804_);
v_res_4809_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v___x_4803_, v_closed_boxed_4808_, v___f_4805_, v_x_4806_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4810_, lean_object* v___x_4811_, lean_object* v___y_4812_, lean_object* v_x_4813_){
_start:
{
if (lean_obj_tag(v_x_4813_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4823_; 
lean_dec(v___x_4811_);
v_a_4815_ = lean_ctor_get(v_x_4813_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_x_4813_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4817_ = v_x_4813_;
v_isShared_4818_ = v_isSharedCheck_4823_;
goto v_resetjp_4816_;
}
else
{
lean_inc(v_a_4815_);
lean_dec(v_x_4813_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4823_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
lean_object* v___x_4820_; 
if (v_isShared_4818_ == 0)
{
v___x_4820_ = v___x_4817_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4815_);
v___x_4820_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
lean_object* v___x_4821_; 
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
return v___x_4821_;
}
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4862_; 
v_a_4824_ = lean_ctor_get(v_x_4813_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v_x_4813_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4826_ = v_x_4813_;
v_isShared_4827_ = v_isSharedCheck_4862_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v_x_4813_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4862_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
uint8_t v_closed_4828_; 
v_closed_4828_ = lean_ctor_get_uint8(v_a_4824_, sizeof(void*)*10);
if (v_closed_4828_ == 0)
{
lean_object* v_capacity_4829_; lean_object* v_size_4830_; lean_object* v_receivers_4831_; lean_object* v___x_4832_; 
v_capacity_4829_ = lean_ctor_get(v_a_4824_, 2);
lean_inc(v_capacity_4829_);
v_size_4830_ = lean_ctor_get(v_a_4824_, 3);
lean_inc(v_size_4830_);
v_receivers_4831_ = lean_ctor_get(v_a_4824_, 7);
lean_inc(v_receivers_4831_);
lean_dec(v_a_4824_);
v___x_4832_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4831_, v_id_4810_);
lean_dec(v_receivers_4831_);
if (lean_obj_tag(v___x_4832_) == 1)
{
lean_object* v_val_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4851_; 
v_val_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4851_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_val_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4851_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
uint8_t v___x_4837_; 
v___x_4837_ = lean_nat_dec_eq(v_size_4830_, v___x_4811_);
lean_dec(v_size_4830_);
if (v___x_4837_ == 0)
{
lean_object* v___f_4838_; lean_object* v___x_4839_; lean_object* v___f_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_del_object(v___x_4835_);
lean_del_object(v___x_4826_);
lean_inc(v_val_4833_);
v___f_4838_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4838_, 0, v_val_4833_);
v___x_4839_ = lean_box(v_closed_4828_);
lean_inc(v___x_4811_);
v___f_4840_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 5, 3);
lean_closure_set(v___f_4840_, 0, v___x_4811_);
lean_closure_set(v___f_4840_, 1, v___x_4839_);
lean_closure_set(v___f_4840_, 2, v___f_4838_);
v___x_4841_ = lean_nat_mod(v_val_4833_, v_capacity_4829_);
lean_dec(v_capacity_4829_);
lean_dec(v_val_4833_);
v___x_4842_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4841_, v___y_4812_);
v___x_4843_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4811_, v___x_4837_, v___x_4842_, v___f_4840_);
return v___x_4843_;
}
else
{
lean_object* v___x_4844_; lean_object* v___x_4846_; 
lean_dec(v_val_4833_);
lean_dec(v_capacity_4829_);
lean_dec(v___x_4811_);
v___x_4844_ = lean_box(v_closed_4828_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v___x_4844_);
v___x_4846_ = v___x_4826_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4844_);
v___x_4846_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
lean_object* v___x_4848_; 
if (v_isShared_4836_ == 0)
{
lean_ctor_set_tag(v___x_4835_, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4846_);
v___x_4848_ = v___x_4835_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v___x_4846_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
}
else
{
lean_object* v___x_4852_; lean_object* v___x_4854_; 
lean_dec(v___x_4832_);
lean_dec(v_size_4830_);
lean_dec(v_capacity_4829_);
lean_dec(v___x_4811_);
v___x_4852_ = lean_box(v_closed_4828_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v___x_4852_);
v___x_4854_ = v___x_4826_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4852_);
v___x_4854_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
lean_object* v___x_4855_; 
v___x_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
return v___x_4855_;
}
}
}
else
{
lean_object* v___x_4857_; lean_object* v___x_4859_; 
lean_dec(v_a_4824_);
lean_dec(v___x_4811_);
v___x_4857_ = lean_box(v_closed_4828_);
if (v_isShared_4827_ == 0)
{
lean_ctor_set(v___x_4826_, 0, v___x_4857_);
v___x_4859_ = v___x_4826_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4857_);
v___x_4859_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
lean_object* v___x_4860_; 
v___x_4860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4859_);
return v___x_4860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4863_, lean_object* v___x_4864_, lean_object* v___y_4865_, lean_object* v_x_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4863_, v___x_4864_, v___y_4865_, v_x_4866_);
lean_dec(v___y_4865_);
lean_dec(v_id_4863_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4869_, lean_object* v___f_4870_, lean_object* v___y_4871_){
_start:
{
lean_object* v___f_4873_; lean_object* v___x_4874_; lean_object* v___f_4875_; uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
lean_inc_n(v___y_4871_, 2);
lean_inc(v_id_4869_);
v___f_4873_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4873_, 0, v_id_4869_);
lean_closure_set(v___f_4873_, 1, v___y_4871_);
lean_closure_set(v___f_4873_, 2, v___f_4870_);
v___x_4874_ = lean_unsigned_to_nat(0u);
v___f_4875_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4875_, 0, v_id_4869_);
lean_closure_set(v___f_4875_, 1, v___x_4874_);
lean_closure_set(v___f_4875_, 2, v___y_4871_);
v___x_4876_ = 0;
v___x_4877_ = lean_st_ref_get(v___y_4871_);
v___x_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
v___x_4880_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4874_, v___x_4876_, v___x_4879_, v___f_4875_);
v___x_4881_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4874_, v___x_4876_, v___x_4880_, v___f_4873_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4882_, lean_object* v___f_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4882_, v___f_4883_, v___y_4884_);
lean_dec(v___y_4884_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4889_){
_start:
{
lean_object* v_state_4890_; lean_object* v_id_4891_; lean_object* v___f_4892_; lean_object* v___f_4893_; lean_object* v___f_4894_; lean_object* v___f_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v_state_4890_ = lean_ctor_get(v_ch_4889_, 0);
lean_inc_ref_n(v_state_4890_, 2);
v_id_4891_ = lean_ctor_get(v_ch_4889_, 1);
lean_inc(v_id_4891_);
v___f_4892_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4893_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4893_, 0, v_ch_4889_);
v___f_4894_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4895_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4895_, 0, v_id_4891_);
lean_closure_set(v___f_4895_, 1, v___f_4894_);
v___x_4896_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4896_, 0, lean_box(0));
lean_closure_set(v___x_4896_, 1, lean_box(0));
lean_closure_set(v___x_4896_, 2, v_state_4890_);
lean_closure_set(v___x_4896_, 3, v___f_4895_);
v___x_4897_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4897_, 0, lean_box(0));
lean_closure_set(v___x_4897_, 1, lean_box(0));
lean_closure_set(v___x_4897_, 2, v_state_4890_);
lean_closure_set(v___x_4897_, 3, v___f_4892_);
v___x_4898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4896_);
lean_ctor_set(v___x_4898_, 1, v___f_4893_);
lean_ctor_set(v___x_4898_, 2, v___x_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4899_, lean_object* v_ch_4900_){
_start:
{
lean_object* v___x_4901_; 
v___x_4901_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4900_);
return v___x_4901_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4902_, lean_object* v_receiverId_4903_, lean_object* v_a_4904_){
_start:
{
lean_object* v___x_4906_; 
v___x_4906_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4903_, v_a_4904_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4907_, lean_object* v_receiverId_4908_, lean_object* v_a_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4907_, v_receiverId_4908_, v_a_4909_);
lean_dec(v_a_4909_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4912_, lean_object* v_q_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v___x_4916_; 
v___x_4916_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4913_, v___y_4914_);
return v___x_4916_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4917_, lean_object* v_q_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4917_, v_q_4918_, v___y_4919_);
lean_dec(v___y_4919_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4922_, lean_object* v_slot_4923_, lean_object* v_next_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v___x_4927_; 
v___x_4927_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4923_, v_next_4924_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4928_, lean_object* v_slot_4929_, lean_object* v_next_4930_, lean_object* v_a_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4928_, v_slot_4929_, v_next_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec(v_next_4930_);
lean_dec(v_slot_4929_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4934_, lean_object* v_a_4935_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4935_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4938_, lean_object* v_a_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4938_, v_a_4939_);
lean_dec(v_a_4939_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4942_, lean_object* v_next_4943_, lean_object* v_a_4944_){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4943_, v_a_4944_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4947_, lean_object* v_next_4948_, lean_object* v_a_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4947_, v_next_4948_, v_a_4949_);
lean_dec(v_a_4949_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4952_, lean_object* v_x_4953_, lean_object* v_x_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; 
v___x_4957_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4953_, v_x_4954_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4958_, lean_object* v_x_4959_, lean_object* v_x_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4958_, v_x_4959_, v_x_4960_, v___y_4961_);
lean_dec(v___y_4961_);
return v_res_4963_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4965_){
_start:
{
lean_object* v___x_4967_; 
v___x_4967_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4965_);
return v___x_4967_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4968_, lean_object* v_a_4969_){
_start:
{
lean_object* v_res_4970_; 
v_res_4970_ = l_Std_Broadcast_new___redArg(v_capacity_4968_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4971_, lean_object* v_capacity_4972_, lean_object* v_h_4973_){
_start:
{
lean_object* v___x_4975_; 
v___x_4975_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4972_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4976_, lean_object* v_capacity_4977_, lean_object* v_h_4978_, lean_object* v_a_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l_Std_Broadcast_new(v_00_u03b1_4976_, v_capacity_4977_, v_h_4978_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4981_, lean_object* v_v_4982_){
_start:
{
lean_object* v___x_4984_; 
v___x_4984_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4981_, v_v_4982_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4985_, lean_object* v_v_4986_, lean_object* v_a_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Std_Broadcast_trySend___redArg(v_ch_4985_, v_v_4986_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4989_, lean_object* v_ch_4990_, lean_object* v_v_4991_){
_start:
{
lean_object* v___x_4993_; 
v___x_4993_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4990_, v_v_4991_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4994_, lean_object* v_ch_4995_, lean_object* v_v_4996_, lean_object* v_a_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Std_Broadcast_trySend(v_00_u03b1_4994_, v_ch_4995_, v_v_4996_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4999_){
_start:
{
lean_object* v___x_5001_; 
v___x_5001_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4999_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_5001_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_5001_);
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
return v___x_5007_;
}
}
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
v_a_5010_ = lean_ctor_get(v___x_5001_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_5001_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v___x_5001_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v___x_5001_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_5018_, lean_object* v_a_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_Std_Broadcast_subscribe___redArg(v_ch_5018_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_5021_, lean_object* v_ch_5022_){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_5022_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_5024_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5024_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
v_a_5033_ = lean_ctor_get(v___x_5024_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5024_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5024_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5024_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_5041_, lean_object* v_ch_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Std_Broadcast_subscribe(v_00_u03b1_5041_, v_ch_5042_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_5045_){
_start:
{
lean_object* v___x_5047_; 
v___x_5047_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5045_);
if (lean_obj_tag(v___x_5047_) == 0)
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
v_a_5048_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v___x_5047_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v___x_5047_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5073_; 
v_a_5056_ = lean_ctor_get(v___x_5047_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5058_ = v___x_5047_;
v_isShared_5059_ = v_isSharedCheck_5073_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5047_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5073_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
uint8_t v___x_5060_; 
v___x_5060_ = lean_unbox(v_a_5056_);
lean_dec(v_a_5056_);
switch(v___x_5060_)
{
case 0:
{
lean_object* v___x_5061_; lean_object* v___x_5063_; 
v___x_5061_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v___x_5061_);
v___x_5063_ = v___x_5058_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5061_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
case 1:
{
lean_object* v___x_5065_; lean_object* v___x_5067_; 
v___x_5065_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v___x_5065_);
v___x_5067_ = v___x_5058_;
goto v_reusejp_5066_;
}
else
{
lean_object* v_reuseFailAlloc_5068_; 
v_reuseFailAlloc_5068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5068_, 0, v___x_5065_);
v___x_5067_ = v_reuseFailAlloc_5068_;
goto v_reusejp_5066_;
}
v_reusejp_5066_:
{
return v___x_5067_;
}
}
default: 
{
lean_object* v___x_5069_; lean_object* v___x_5071_; 
v___x_5069_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v___x_5069_);
v___x_5071_ = v___x_5058_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
return v___x_5071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5074_, lean_object* v_a_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l_Std_Broadcast_close___redArg(v_ch_5074_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5077_, lean_object* v_ch_5078_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5078_);
if (lean_obj_tag(v___x_5080_) == 0)
{
lean_object* v_a_5081_; lean_object* v___x_5083_; uint8_t v_isShared_5084_; uint8_t v_isSharedCheck_5088_; 
v_a_5081_ = lean_ctor_get(v___x_5080_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5083_ = v___x_5080_;
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
else
{
lean_inc(v_a_5081_);
lean_dec(v___x_5080_);
v___x_5083_ = lean_box(0);
v_isShared_5084_ = v_isSharedCheck_5088_;
goto v_resetjp_5082_;
}
v_resetjp_5082_:
{
lean_object* v___x_5086_; 
if (v_isShared_5084_ == 0)
{
v___x_5086_ = v___x_5083_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
v___x_5086_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
return v___x_5086_;
}
}
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5091_; uint8_t v_isShared_5092_; uint8_t v_isSharedCheck_5106_; 
v_a_5089_ = lean_ctor_get(v___x_5080_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_5080_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5091_ = v___x_5080_;
v_isShared_5092_ = v_isSharedCheck_5106_;
goto v_resetjp_5090_;
}
else
{
lean_inc(v_a_5089_);
lean_dec(v___x_5080_);
v___x_5091_ = lean_box(0);
v_isShared_5092_ = v_isSharedCheck_5106_;
goto v_resetjp_5090_;
}
v_resetjp_5090_:
{
uint8_t v___x_5093_; 
v___x_5093_ = lean_unbox(v_a_5089_);
lean_dec(v_a_5089_);
switch(v___x_5093_)
{
case 0:
{
lean_object* v___x_5094_; lean_object* v___x_5096_; 
v___x_5094_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v___x_5094_);
v___x_5096_ = v___x_5091_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
case 1:
{
lean_object* v___x_5098_; lean_object* v___x_5100_; 
v___x_5098_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v___x_5098_);
v___x_5100_ = v___x_5091_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5098_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
return v___x_5100_;
}
}
default: 
{
lean_object* v___x_5102_; lean_object* v___x_5104_; 
v___x_5102_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5092_ == 0)
{
lean_ctor_set(v___x_5091_, 0, v___x_5102_);
v___x_5104_ = v___x_5091_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v___x_5102_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5107_, lean_object* v_ch_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l_Std_Broadcast_close(v_00_u03b1_5107_, v_ch_5108_);
return v_res_5110_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5111_){
_start:
{
lean_object* v___y_5114_; 
if (lean_obj_tag(v_x_5111_) == 0)
{
lean_object* v_a_5118_; uint8_t v___x_5119_; 
v_a_5118_ = lean_ctor_get(v_x_5111_, 0);
lean_inc(v_a_5118_);
lean_dec_ref_known(v_x_5111_, 1);
v___x_5119_ = lean_unbox(v_a_5118_);
lean_dec(v_a_5118_);
switch(v___x_5119_)
{
case 0:
{
lean_object* v___x_5120_; 
v___x_5120_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5114_ = v___x_5120_;
goto v___jp_5113_;
}
case 1:
{
lean_object* v___x_5121_; 
v___x_5121_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5114_ = v___x_5121_;
goto v___jp_5113_;
}
default: 
{
lean_object* v___x_5122_; 
v___x_5122_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5114_ = v___x_5122_;
goto v___jp_5113_;
}
}
}
else
{
lean_object* v_a_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5131_; 
v_a_5123_ = lean_ctor_get(v_x_5111_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v_x_5111_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5125_ = v_x_5111_;
v_isShared_5126_ = v_isSharedCheck_5131_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_a_5123_);
lean_dec(v_x_5111_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5131_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___x_5128_; 
if (v_isShared_5126_ == 0)
{
v___x_5128_ = v___x_5125_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5123_);
v___x_5128_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
lean_object* v___x_5129_; 
v___x_5129_ = lean_task_pure(v___x_5128_);
return v___x_5129_;
}
}
}
v___jp_5113_:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_inc_ref(v___y_5114_);
v___x_5115_ = lean_mk_io_user_error(v___y_5114_);
v___x_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5116_, 0, v___x_5115_);
v___x_5117_ = lean_task_pure(v___x_5116_);
return v___x_5117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5132_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5136_, lean_object* v_v_5137_){
_start:
{
lean_object* v___f_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; uint8_t v___x_5142_; lean_object* v___x_5143_; 
v___f_5139_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5140_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5136_, v_v_5137_);
v___x_5141_ = lean_unsigned_to_nat(0u);
v___x_5142_ = 1;
v___x_5143_ = lean_io_bind_task(v___x_5140_, v___f_5139_, v___x_5141_, v___x_5142_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5144_, lean_object* v_v_5145_, lean_object* v_a_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l_Std_Broadcast_send___redArg(v_ch_5144_, v_v_5145_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5148_, lean_object* v_ch_5149_, lean_object* v_v_5150_){
_start:
{
lean_object* v___f_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; uint8_t v___x_5155_; lean_object* v___x_5156_; 
v___f_5152_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5153_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5149_, v_v_5150_);
v___x_5154_ = lean_unsigned_to_nat(0u);
v___x_5155_ = 1;
v___x_5156_ = lean_io_bind_task(v___x_5153_, v___f_5152_, v___x_5154_, v___x_5155_);
return v___x_5156_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5157_, lean_object* v_ch_5158_, lean_object* v_v_5159_, lean_object* v_a_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_Std_Broadcast_send(v_00_u03b1_5157_, v_ch_5158_, v_v_5159_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5162_){
_start:
{
lean_object* v___x_5164_; 
v___x_5164_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5162_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5165_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5168_, lean_object* v_ch_5169_){
_start:
{
lean_object* v___x_5171_; 
v___x_5171_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5169_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5172_, lean_object* v_ch_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5172_, v_ch_5173_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5176_){
_start:
{
lean_object* v___x_5178_; 
v___x_5178_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5176_);
return v___x_5178_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5179_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5182_, lean_object* v_inst_5183_, lean_object* v_ch_5184_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5184_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5187_, lean_object* v_inst_5188_, lean_object* v_ch_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5187_, v_inst_5188_, v_ch_5189_);
lean_dec(v_inst_5188_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5192_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5192_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5194_, lean_object* v_inst_5195_, lean_object* v_ch_5196_){
_start:
{
lean_object* v___x_5197_; 
v___x_5197_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5196_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5198_, lean_object* v_inst_5199_, lean_object* v_ch_5200_){
_start:
{
lean_object* v_res_5201_; 
v_res_5201_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5198_, v_inst_5199_, v_ch_5200_);
lean_dec(v_inst_5199_);
return v_res_5201_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5202_){
_start:
{
lean_object* v___x_5204_; 
v___x_5204_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5202_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5205_, lean_object* v_a_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5205_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5208_, lean_object* v_ch_5209_){
_start:
{
lean_object* v___x_5211_; 
v___x_5211_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5209_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5212_, lean_object* v_ch_5213_, lean_object* v_a_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5212_, v_ch_5213_);
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5216_, lean_object* v_ch_5217_, lean_object* v_prio_5218_){
_start:
{
lean_object* v___x_5220_; 
v___x_5220_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5216_, v_ch_5217_, v_prio_5218_);
return v___x_5220_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5221_, lean_object* v_ch_5222_, lean_object* v_prio_5223_, lean_object* v_a_5224_){
_start:
{
lean_object* v_res_5225_; 
v_res_5225_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5221_, v_ch_5222_, v_prio_5223_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5226_, lean_object* v_f_5227_, lean_object* v_ch_5228_, lean_object* v_prio_5229_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5227_, v_ch_5228_, v_prio_5229_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5232_, lean_object* v_f_5233_, lean_object* v_ch_5234_, lean_object* v_prio_5235_, lean_object* v_a_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5232_, v_f_5233_, v_ch_5234_, v_prio_5235_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg(){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__2));
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object* v___dummy_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
return v_res_5246_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5248_, lean_object* v_inst_5249_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5251_, lean_object* v_inst_5252_){
_start:
{
lean_object* v_res_5253_; 
v_res_5253_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5251_, v_inst_5252_);
lean_dec(v_inst_5252_);
return v_res_5253_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object* v_a_5254_){
_start:
{
lean_object* v___x_5255_; 
v___x_5255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5255_, 0, v_a_5254_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object* v___f_5256_, lean_object* v_x_5257_){
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
lean_object* v_a_5268_; 
v_a_5268_ = lean_ctor_get(v_x_5257_, 0);
lean_inc(v_a_5268_);
lean_dec_ref_known(v_x_5257_, 1);
if (lean_obj_tag(v_a_5268_) == 0)
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5277_; 
lean_dec_ref(v___f_5256_);
v_a_5269_ = lean_ctor_get(v_a_5268_, 0);
v_isSharedCheck_5277_ = !lean_is_exclusive(v_a_5268_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5271_ = v_a_5268_;
v_isShared_5272_ = v_isSharedCheck_5277_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v_a_5268_);
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
lean_object* v_a_5278_; lean_object* v___x_5279_; uint8_t v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v_a_5278_ = lean_ctor_get(v_a_5268_, 0);
lean_inc(v_a_5278_);
lean_dec_ref_known(v_a_5268_, 1);
v___x_5279_ = lean_unsigned_to_nat(0u);
v___x_5280_ = 0;
v___x_5281_ = lean_task_map(v___f_5256_, v_a_5278_, v___x_5279_, v___x_5280_);
v___x_5282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5281_);
return v___x_5282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5283_, lean_object* v_x_5284_, lean_object* v___y_5285_){
_start:
{
lean_object* v_res_5286_; 
v_res_5286_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_5283_, v_x_5284_);
return v_res_5286_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object* v___f_5287_, lean_object* v_receiver_5288_){
_start:
{
lean_object* v___x_5290_; uint8_t v___x_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; 
v___x_5290_ = lean_unsigned_to_nat(0u);
v___x_5291_ = 0;
v___x_5292_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5288_);
v___x_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5293_, 0, v___x_5292_);
v___x_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5293_);
v___x_5295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5294_);
v___x_5296_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5290_, v___x_5291_, v___x_5295_, v___f_5287_);
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5297_, lean_object* v_receiver_5298_, lean_object* v___y_5299_){
_start:
{
lean_object* v_res_5300_; 
v_res_5300_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_5297_, v_receiver_5298_);
return v_res_5300_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg(){
_start:
{
lean_object* v___f_5307_; 
v___f_5307_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__2));
return v___f_5307_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object* v___dummy_5308_){
_start:
{
lean_object* v_res_5309_; 
v_res_5309_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
return v_res_5309_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5310_; 
v___x_5310_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
return v___x_5310_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5311_, lean_object* v_inst_5312_){
_start:
{
lean_object* v___x_5313_; 
v___x_5313_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5314_, lean_object* v_inst_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5314_, v_inst_5315_);
lean_dec(v_inst_5315_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v_x_5321_){
_start:
{
if (lean_obj_tag(v_x_5321_) == 0)
{
lean_object* v_a_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5331_; 
v_a_5323_ = lean_ctor_get(v_x_5321_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v_x_5321_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5325_ = v_x_5321_;
v_isShared_5326_ = v_isSharedCheck_5331_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_a_5323_);
lean_dec(v_x_5321_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5331_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___x_5328_; 
if (v_isShared_5326_ == 0)
{
v___x_5328_ = v___x_5325_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5323_);
v___x_5328_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
lean_object* v___x_5329_; 
v___x_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5328_);
return v___x_5329_;
}
}
}
else
{
lean_object* v_a_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; uint8_t v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; 
v_a_5332_ = lean_ctor_get(v_x_5321_, 0);
lean_inc(v_a_5332_);
lean_dec_ref_known(v_x_5321_, 1);
v___x_5333_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__1));
v___x_5334_ = lean_unsigned_to_nat(0u);
v___x_5335_ = 0;
v___x_5336_ = lean_task_map(v___x_5333_, v_a_5332_, v___x_5334_, v___x_5335_);
v___x_5337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5337_, 0, v___x_5336_);
return v___x_5337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object* v_x_5338_, lean_object* v___y_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(v_x_5338_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v___f_5341_, lean_object* v___f_5342_, lean_object* v_receiver_5343_, lean_object* v_x_5344_){
_start:
{
lean_object* v___x_5346_; uint8_t v___x_5347_; lean_object* v___x_5348_; uint8_t v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5346_ = lean_unsigned_to_nat(0u);
v___x_5347_ = 0;
v___x_5348_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5343_, v_x_5344_);
v___x_5349_ = 1;
v___x_5350_ = lean_io_bind_task(v___x_5348_, v___f_5341_, v___x_5346_, v___x_5349_);
v___x_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5351_, 0, v___x_5350_);
v___x_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5352_, 0, v___x_5351_);
v___x_5353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5346_, v___x_5347_, v___x_5352_, v___f_5342_);
return v___x_5353_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5354_, lean_object* v___f_5355_, lean_object* v_receiver_5356_, lean_object* v_x_5357_, lean_object* v___y_5358_){
_start:
{
lean_object* v_res_5359_; 
v_res_5359_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5354_, v___f_5355_, v_receiver_5356_, v_x_5357_);
return v_res_5359_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v_x_5360_){
_start:
{
lean_object* v___x_5362_; 
v___x_5362_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v_x_5363_, lean_object* v___y_5364_){
_start:
{
lean_object* v_res_5365_; 
v_res_5365_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(v_x_5363_);
lean_dec_ref(v_x_5363_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(lean_object* v___f_5366_, lean_object* v_socket_5367_, lean_object* v_x_5368_, lean_object* v___y_5369_){
_start:
{
lean_object* v___x_5371_; 
v___x_5371_ = lean_apply_3(v___f_5366_, v_socket_5367_, v___y_5369_, lean_box(0));
return v___x_5371_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object* v___f_5372_, lean_object* v_socket_5373_, lean_object* v_x_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(v___f_5372_, v_socket_5373_, v_x_5374_, v___y_5375_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(lean_object* v___f_5378_, lean_object* v___x_5379_, lean_object* v_socket_5380_, lean_object* v_data_5381_){
_start:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; uint8_t v___x_5386_; 
v___x_5383_ = lean_unsigned_to_nat(0u);
v___x_5384_ = lean_array_get_size(v_data_5381_);
v___x_5385_ = lean_box(0);
v___x_5386_ = lean_nat_dec_lt(v___x_5383_, v___x_5384_);
if (v___x_5386_ == 0)
{
lean_object* v___x_5387_; 
lean_dec_ref(v_data_5381_);
lean_dec_ref(v_socket_5380_);
lean_dec_ref(v___x_5379_);
lean_dec_ref(v___f_5378_);
v___x_5387_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5387_;
}
else
{
lean_object* v___f_5388_; uint8_t v___x_5389_; 
v___f_5388_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_5388_, 0, v___f_5378_);
lean_closure_set(v___f_5388_, 1, v_socket_5380_);
v___x_5389_ = lean_nat_dec_le(v___x_5384_, v___x_5384_);
if (v___x_5389_ == 0)
{
if (v___x_5386_ == 0)
{
lean_object* v___x_5390_; 
lean_dec_ref(v___f_5388_);
lean_dec_ref(v_data_5381_);
lean_dec_ref(v___x_5379_);
v___x_5390_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5390_;
}
else
{
size_t v___x_5391_; size_t v___x_5392_; lean_object* v___x_873__overap_5393_; lean_object* v___x_5394_; 
v___x_5391_ = ((size_t)0ULL);
v___x_5392_ = lean_usize_of_nat(v___x_5384_);
v___x_873__overap_5393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5379_, v___f_5388_, v_data_5381_, v___x_5391_, v___x_5392_, v___x_5385_);
v___x_5394_ = lean_apply_1(v___x_873__overap_5393_, lean_box(0));
return v___x_5394_;
}
}
else
{
size_t v___x_5395_; size_t v___x_5396_; lean_object* v___x_876__overap_5397_; lean_object* v___x_5398_; 
v___x_5395_ = ((size_t)0ULL);
v___x_5396_ = lean_usize_of_nat(v___x_5384_);
v___x_876__overap_5397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5379_, v___f_5388_, v_data_5381_, v___x_5395_, v___x_5396_, v___x_5385_);
v___x_5398_ = lean_apply_1(v___x_876__overap_5397_, lean_box(0));
return v___x_5398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object* v___f_5399_, lean_object* v___x_5400_, lean_object* v_socket_5401_, lean_object* v_data_5402_, lean_object* v___y_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(v___f_5399_, v___x_5400_, v_socket_5401_, v_data_5402_);
return v_res_5404_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_5410_; 
v___x_5410_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_5410_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_5411_; lean_object* v___f_5412_; lean_object* v___f_5413_; 
v___x_5411_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5412_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1));
v___f_5413_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5413_, 0, v___f_5412_);
lean_closure_set(v___f_5413_, 1, v___x_5411_);
return v___f_5413_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5(void){
_start:
{
lean_object* v___f_5414_; lean_object* v___f_5415_; lean_object* v___f_5416_; lean_object* v___x_5417_; 
v___f_5414_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5415_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4);
v___f_5416_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1));
v___x_5417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5417_, 0, v___f_5416_);
lean_ctor_set(v___x_5417_, 1, v___f_5415_);
lean_ctor_set(v___x_5417_, 2, v___f_5414_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_5419_; 
v___x_5419_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
return v_res_5421_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5422_; 
v___x_5422_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
return v___x_5422_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5423_, lean_object* v_inst_5424_){
_start:
{
lean_object* v___x_5425_; 
v___x_5425_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0);
return v___x_5425_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5426_, lean_object* v_inst_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5426_, v_inst_5427_);
lean_dec(v_inst_5427_);
return v_res_5428_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5429_; 
v___x_5429_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5429_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5430_){
_start:
{
lean_object* v___x_5432_; 
v___x_5432_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5430_);
return v___x_5432_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5433_, lean_object* v_a_5434_){
_start:
{
lean_object* v_res_5435_; 
v_res_5435_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5433_);
return v_res_5435_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5436_, lean_object* v_capacity_5437_, lean_object* v_h_5438_){
_start:
{
lean_object* v___x_5440_; 
v___x_5440_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5437_);
return v___x_5440_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5441_, lean_object* v_capacity_5442_, lean_object* v_h_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5441_, v_capacity_5442_, v_h_5443_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5446_, lean_object* v_v_5447_){
_start:
{
lean_object* v___x_5449_; 
v___x_5449_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5446_, v_v_5447_);
return v___x_5449_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5450_, lean_object* v_v_5451_, lean_object* v_a_5452_){
_start:
{
lean_object* v_res_5453_; 
v_res_5453_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5450_, v_v_5451_);
return v_res_5453_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5454_, lean_object* v_ch_5455_, lean_object* v_v_5456_){
_start:
{
lean_object* v___x_5458_; 
v___x_5458_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5455_, v_v_5456_);
return v___x_5458_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5459_, lean_object* v_ch_5460_, lean_object* v_v_5461_, lean_object* v_a_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5459_, v_ch_5460_, v_v_5461_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5465_, lean_object* v_v_5466_){
_start:
{
lean_object* v___f_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; uint8_t v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; 
v___f_5468_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5469_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5470_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5465_, v_v_5466_);
v___x_5471_ = lean_unsigned_to_nat(0u);
v___x_5472_ = 1;
v___x_5473_ = lean_io_bind_task(v___x_5470_, v___f_5468_, v___x_5471_, v___x_5472_);
v___x_5474_ = lean_io_wait(v___x_5473_);
v___x_5475_ = l_IO_ofExcept___redArg(v___x_5469_, v___x_5474_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5476_, lean_object* v_v_5477_, lean_object* v_a_5478_){
_start:
{
lean_object* v_res_5479_; 
v_res_5479_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5476_, v_v_5477_);
return v_res_5479_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5480_, lean_object* v_ch_5481_, lean_object* v_v_5482_){
_start:
{
lean_object* v___f_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; uint8_t v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; 
v___f_5484_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5485_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5486_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5481_, v_v_5482_);
v___x_5487_ = lean_unsigned_to_nat(0u);
v___x_5488_ = 1;
v___x_5489_ = lean_io_bind_task(v___x_5486_, v___f_5484_, v___x_5487_, v___x_5488_);
v___x_5490_ = lean_io_wait(v___x_5489_);
v___x_5491_ = l_IO_ofExcept___redArg(v___x_5485_, v___x_5490_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5492_, lean_object* v_ch_5493_, lean_object* v_v_5494_, lean_object* v_a_5495_){
_start:
{
lean_object* v_res_5496_; 
v_res_5496_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5492_, v_ch_5493_, v_v_5494_);
return v_res_5496_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5497_){
_start:
{
lean_object* v___x_5499_; 
v___x_5499_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5497_);
return v___x_5499_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5500_, lean_object* v_a_5501_){
_start:
{
lean_object* v_res_5502_; 
v_res_5502_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5500_);
return v_res_5502_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5503_, lean_object* v_ch_5504_){
_start:
{
lean_object* v___x_5506_; 
v___x_5506_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5504_);
return v___x_5506_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5507_, lean_object* v_ch_5508_, lean_object* v_a_5509_){
_start:
{
lean_object* v_res_5510_; 
v_res_5510_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5507_, v_ch_5508_);
return v_res_5510_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5511_){
_start:
{
lean_object* v___x_5513_; lean_object* v___x_5514_; 
v___x_5513_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5511_);
v___x_5514_ = lean_io_wait(v___x_5513_);
return v___x_5514_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5515_, lean_object* v_a_5516_){
_start:
{
lean_object* v_res_5517_; 
v_res_5517_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5515_);
return v_res_5517_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5518_, lean_object* v_inst_5519_, lean_object* v_ch_5520_){
_start:
{
lean_object* v___x_5522_; 
v___x_5522_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5520_);
return v___x_5522_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5523_, lean_object* v_inst_5524_, lean_object* v_ch_5525_, lean_object* v_a_5526_){
_start:
{
lean_object* v_res_5527_; 
v_res_5527_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5523_, v_inst_5524_, v_ch_5525_);
lean_dec(v_inst_5524_);
return v_res_5527_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5528_, lean_object* v_b_5529_, lean_object* v_f_5530_, lean_object* v_toBind_5531_, lean_object* v___f_5532_, lean_object* v_a_5533_){
_start:
{
if (lean_obj_tag(v_a_5533_) == 0)
{
lean_object* v___x_5534_; 
lean_dec(v___f_5532_);
lean_dec(v_toBind_5531_);
lean_dec(v_f_5530_);
v___x_5534_ = lean_apply_2(v_toPure_5528_, lean_box(0), v_b_5529_);
return v___x_5534_;
}
else
{
lean_object* v_val_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; 
lean_dec(v_toPure_5528_);
v_val_5535_ = lean_ctor_get(v_a_5533_, 0);
lean_inc(v_val_5535_);
lean_dec_ref_known(v_a_5533_, 1);
v___x_5536_ = lean_apply_2(v_f_5530_, v_val_5535_, v_b_5529_);
v___x_5537_ = lean_apply_4(v_toBind_5531_, lean_box(0), lean_box(0), v___x_5536_, v___f_5532_);
return v___x_5537_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5538_, lean_object* v_inst_5539_, lean_object* v_inst_5540_, lean_object* v_ch_5541_, lean_object* v_f_5542_, lean_object* v_b_5543_){
_start:
{
lean_object* v_toApplicative_5544_; lean_object* v_toBind_5545_; lean_object* v_toPure_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___f_5549_; lean_object* v___f_5550_; lean_object* v___x_5551_; 
v_toApplicative_5544_ = lean_ctor_get(v_inst_5539_, 0);
v_toBind_5545_ = lean_ctor_get(v_inst_5539_, 1);
lean_inc_n(v_toBind_5545_, 2);
v_toPure_5546_ = lean_ctor_get(v_toApplicative_5544_, 1);
lean_inc_n(v_toPure_5546_, 2);
lean_inc_ref(v_ch_5541_);
lean_inc(v_inst_5538_);
v___x_5547_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5547_, 0, lean_box(0));
lean_closure_set(v___x_5547_, 1, v_inst_5538_);
lean_closure_set(v___x_5547_, 2, v_ch_5541_);
lean_inc(v_inst_5540_);
v___x_5548_ = lean_apply_2(v_inst_5540_, lean_box(0), v___x_5547_);
lean_inc(v_f_5542_);
v___f_5549_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5549_, 0, v_toPure_5546_);
lean_closure_set(v___f_5549_, 1, v_inst_5538_);
lean_closure_set(v___f_5549_, 2, v_inst_5539_);
lean_closure_set(v___f_5549_, 3, v_inst_5540_);
lean_closure_set(v___f_5549_, 4, v_ch_5541_);
lean_closure_set(v___f_5549_, 5, v_f_5542_);
v___f_5550_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5550_, 0, v_toPure_5546_);
lean_closure_set(v___f_5550_, 1, v_b_5543_);
lean_closure_set(v___f_5550_, 2, v_f_5542_);
lean_closure_set(v___f_5550_, 3, v_toBind_5545_);
lean_closure_set(v___f_5550_, 4, v___f_5549_);
v___x_5551_ = lean_apply_4(v_toBind_5545_, lean_box(0), lean_box(0), v___x_5548_, v___f_5550_);
return v___x_5551_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5552_, lean_object* v_inst_5553_, lean_object* v_inst_5554_, lean_object* v_inst_5555_, lean_object* v_ch_5556_, lean_object* v_f_5557_, lean_object* v_____do__lift_5558_){
_start:
{
if (lean_obj_tag(v_____do__lift_5558_) == 0)
{
lean_object* v_a_5559_; lean_object* v___x_5560_; 
lean_dec(v_f_5557_);
lean_dec_ref(v_ch_5556_);
lean_dec(v_inst_5555_);
lean_dec_ref(v_inst_5554_);
lean_dec(v_inst_5553_);
v_a_5559_ = lean_ctor_get(v_____do__lift_5558_, 0);
lean_inc(v_a_5559_);
lean_dec_ref_known(v_____do__lift_5558_, 1);
v___x_5560_ = lean_apply_2(v_toPure_5552_, lean_box(0), v_a_5559_);
return v___x_5560_;
}
else
{
lean_object* v_a_5561_; lean_object* v___x_5562_; 
lean_dec(v_toPure_5552_);
v_a_5561_ = lean_ctor_get(v_____do__lift_5558_, 0);
lean_inc(v_a_5561_);
lean_dec_ref_known(v_____do__lift_5558_, 1);
v___x_5562_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5553_, v_inst_5554_, v_inst_5555_, v_ch_5556_, v_f_5557_, v_a_5561_);
return v___x_5562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5563_, lean_object* v_m_5564_, lean_object* v_00_u03b2_5565_, lean_object* v_inst_5566_, lean_object* v_inst_5567_, lean_object* v_inst_5568_, lean_object* v_ch_5569_, lean_object* v_f_5570_, lean_object* v_b_5571_){
_start:
{
lean_object* v___x_5572_; 
v___x_5572_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5566_, v_inst_5567_, v_inst_5568_, v_ch_5569_, v_f_5570_, v_b_5571_);
return v___x_5572_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5573_, lean_object* v_inst_5574_, lean_object* v_inst_5575_, lean_object* v_00_u03b2_5576_, lean_object* v_ch_5577_, lean_object* v_b_5578_, lean_object* v_f_5579_){
_start:
{
lean_object* v___x_5580_; 
v___x_5580_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5573_, v_inst_5574_, v_inst_5575_, v_ch_5577_, v_f_5579_, v_b_5578_);
return v___x_5580_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5581_, lean_object* v_inst_5582_, lean_object* v_inst_5583_){
_start:
{
lean_object* v___f_5584_; 
v___f_5584_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5584_, 0, v_inst_5581_);
lean_closure_set(v___f_5584_, 1, v_inst_5582_);
lean_closure_set(v___f_5584_, 2, v_inst_5583_);
return v___f_5584_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5585_, lean_object* v_m_5586_, lean_object* v_inst_5587_, lean_object* v_inst_5588_, lean_object* v_inst_5589_){
_start:
{
lean_object* v___f_5590_; 
v___f_5590_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5590_, 0, v_inst_5587_);
lean_closure_set(v___f_5590_, 1, v_inst_5588_);
lean_closure_set(v___f_5590_, 2, v_inst_5589_);
return v___f_5590_;
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

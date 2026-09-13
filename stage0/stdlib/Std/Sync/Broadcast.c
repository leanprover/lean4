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
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Option_repr___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
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
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_const___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___closed__0_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__0 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__0_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__0_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Broadcast_send___redArg___closed__0_value),((lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1_value)} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2_value;
static const lean_closure_object l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3 = (const lean_object*)&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3_value;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5;
static lean_once_cell_t l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__6;
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(lean_object* v_mutex_1303_, lean_object* v_k_1304_){
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object* v_mutex_1328_, lean_object* v_k_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_mutex_1328_, v_k_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_mutex_1334_, lean_object* v_k_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_mutex_1334_, v_k_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_mutex_1340_, lean_object* v_k_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(v_00_u03b1_1338_, v_00_u03b2_1339_, v_mutex_1340_, v_k_1341_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(uint8_t v___x_1344_, lean_object* v_as_1345_, size_t v_sz_1346_, size_t v_i_1347_, lean_object* v_b_1348_){
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
lean_object* v___x_1352_; lean_object* v_a_1353_; lean_object* v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; 
v___x_1352_ = lean_box(0);
v_a_1353_ = lean_array_uget_borrowed(v_as_1345_, v_i_1347_);
v___x_1354_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1353_, v___x_1344_);
v___x_1355_ = ((size_t)1ULL);
v___x_1356_ = lean_usize_add(v_i_1347_, v___x_1355_);
v_i_1347_ = v___x_1356_;
v_b_1348_ = v___x_1352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_1358_, lean_object* v_as_1359_, lean_object* v_sz_1360_, lean_object* v_i_1361_, lean_object* v_b_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v___x_1405__boxed_1364_; size_t v_sz_boxed_1365_; size_t v_i_boxed_1366_; lean_object* v_res_1367_; 
v___x_1405__boxed_1364_ = lean_unbox(v___x_1358_);
v_sz_boxed_1365_ = lean_unbox_usize(v_sz_1360_);
lean_dec(v_sz_1360_);
v_i_boxed_1366_ = lean_unbox_usize(v_i_1361_);
lean_dec(v_i_1361_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1405__boxed_1364_, v_as_1359_, v_sz_boxed_1365_, v_i_boxed_1366_, v_b_1362_);
lean_dec_ref(v_as_1359_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; uint8_t v_closed_1371_; 
v___x_1370_ = lean_st_ref_get(v___y_1368_);
v_closed_1371_ = lean_ctor_get_uint8(v___x_1370_, sizeof(void*)*10);
if (v_closed_1371_ == 0)
{
lean_object* v_producers_1372_; lean_object* v_waiters_1373_; lean_object* v_capacity_1374_; lean_object* v_size_1375_; lean_object* v_buffer_1376_; lean_object* v_write_1377_; lean_object* v_read_1378_; lean_object* v_receivers_1379_; lean_object* v_nextId_1380_; lean_object* v_pos_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1404_; 
v_producers_1372_ = lean_ctor_get(v___x_1370_, 0);
v_waiters_1373_ = lean_ctor_get(v___x_1370_, 1);
v_capacity_1374_ = lean_ctor_get(v___x_1370_, 2);
v_size_1375_ = lean_ctor_get(v___x_1370_, 3);
v_buffer_1376_ = lean_ctor_get(v___x_1370_, 4);
v_write_1377_ = lean_ctor_get(v___x_1370_, 5);
v_read_1378_ = lean_ctor_get(v___x_1370_, 6);
v_receivers_1379_ = lean_ctor_get(v___x_1370_, 7);
v_nextId_1380_ = lean_ctor_get(v___x_1370_, 8);
v_pos_1381_ = lean_ctor_get(v___x_1370_, 9);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1383_ = v___x_1370_;
v_isShared_1384_ = v_isSharedCheck_1404_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_pos_1381_);
lean_inc(v_nextId_1380_);
lean_inc(v_receivers_1379_);
lean_inc(v_read_1378_);
lean_inc(v_write_1377_);
lean_inc(v_buffer_1376_);
lean_inc(v_size_1375_);
lean_inc(v_capacity_1374_);
lean_inc(v_waiters_1373_);
lean_inc(v_producers_1372_);
lean_dec(v___x_1370_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1404_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v___x_1385_ = l_Std_Queue_toArray___redArg(v_waiters_1373_);
v___x_1386_ = lean_box(0);
v_sz_1387_ = lean_array_size(v___x_1385_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v_closed_1371_, v___x_1385_, v_sz_1387_, v___x_1388_, v___x_1386_);
lean_dec_ref(v___x_1385_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1402_; 
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v___x_1389_, 0);
lean_dec(v_unused_1403_);
v___x_1391_ = v___x_1389_;
v_isShared_1392_ = v_isSharedCheck_1402_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v___x_1389_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1402_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; lean_object* v___x_1396_; 
v___x_1393_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_1394_ = 1;
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1393_);
v___x_1396_ = v___x_1383_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_producers_1372_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_capacity_1374_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_size_1375_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_buffer_1376_);
lean_ctor_set(v_reuseFailAlloc_1401_, 5, v_write_1377_);
lean_ctor_set(v_reuseFailAlloc_1401_, 6, v_read_1378_);
lean_ctor_set(v_reuseFailAlloc_1401_, 7, v_receivers_1379_);
lean_ctor_set(v_reuseFailAlloc_1401_, 8, v_nextId_1380_);
lean_ctor_set(v_reuseFailAlloc_1401_, 9, v_pos_1381_);
v___x_1396_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*10, v___x_1394_);
v___x_1397_ = lean_st_ref_swap(v___y_1368_, v___x_1396_);
lean_dec(v___x_1397_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1386_);
v___x_1399_ = v___x_1391_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1386_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_del_object(v___x_1383_);
lean_dec(v_pos_1381_);
lean_dec(v_nextId_1380_);
lean_dec(v_receivers_1379_);
lean_dec(v_read_1378_);
lean_dec(v_write_1377_);
lean_dec_ref(v_buffer_1376_);
lean_dec(v_size_1375_);
lean_dec(v_capacity_1374_);
lean_dec_ref(v_producers_1372_);
return v___x_1389_;
}
}
}
else
{
uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec(v___x_1370_);
v___x_1405_ = 1;
v___x_1406_ = lean_box(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(v___y_1408_);
lean_dec(v___y_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(lean_object* v_ch_1412_){
_start:
{
lean_object* v___f_1414_; lean_object* v___x_1415_; 
v___f_1414_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0));
v___x_1415_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_ch_1412_, v___f_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___boxed(lean_object* v_ch_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_object* v_00_u03b1_1419_, lean_object* v_ch_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___boxed(lean_object* v_00_u03b1_1423_, lean_object* v_ch_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close(v_00_u03b1_1423_, v_ch_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_object* v_00_u03b1_1427_, uint8_t v___x_1428_, lean_object* v_as_1429_, size_t v_sz_1430_, size_t v_i_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1428_, v_as_1429_, v_sz_1430_, v_i_1431_, v_b_1432_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_1436_, lean_object* v___x_1437_, lean_object* v_as_1438_, lean_object* v_sz_1439_, lean_object* v_i_1440_, lean_object* v_b_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
uint8_t v___x_1501__boxed_1444_; size_t v_sz_boxed_1445_; size_t v_i_boxed_1446_; lean_object* v_res_1447_; 
v___x_1501__boxed_1444_ = lean_unbox(v___x_1437_);
v_sz_boxed_1445_ = lean_unbox_usize(v_sz_1439_);
lean_dec(v_sz_1439_);
v_i_boxed_1446_ = lean_unbox_usize(v_i_1440_);
lean_dec(v_i_1440_);
v_res_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1436_, v___x_1501__boxed_1444_, v_as_1438_, v_sz_boxed_1445_, v_i_boxed_1446_, v_b_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v_as_1438_);
return v_res_1447_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; uint8_t v_closed_1451_; 
v___x_1450_ = lean_st_ref_get(v___y_1448_);
v_closed_1451_ = lean_ctor_get_uint8(v___x_1450_, sizeof(void*)*10);
lean_dec(v___x_1450_);
return v_closed_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
uint8_t v_res_1454_; lean_object* v_r_1455_; 
v_res_1454_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(v___y_1452_);
lean_dec(v___y_1452_);
v_r_1455_ = lean_box(v_res_1454_);
return v_r_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object* v_ch_1457_){
_start:
{
lean_object* v___f_1459_; lean_object* v___x_1460_; 
v___f_1459_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0));
v___x_1460_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1457_, v___f_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___boxed(lean_object* v_ch_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_object* v_00_u03b1_1464_, lean_object* v_ch_1465_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1465_);
v___x_1468_ = lean_unbox(v___x_1467_);
lean_dec(v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_ch_1470_, lean_object* v_a_1471_){
_start:
{
uint8_t v_res_1472_; lean_object* v_r_1473_; 
v_res_1472_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(v_00_u03b1_1469_, v_ch_1470_);
v_r_1473_ = lean_box(v_res_1472_);
return v_r_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object* v_next_1474_, lean_object* v_slot_1475_){
_start:
{
lean_object* v_value_1476_; lean_object* v_pos_1477_; lean_object* v_remaining_1478_; uint8_t v___x_1479_; 
v_value_1476_ = lean_ctor_get(v_slot_1475_, 0);
v_pos_1477_ = lean_ctor_get(v_slot_1475_, 1);
v_remaining_1478_ = lean_ctor_get(v_slot_1475_, 2);
v___x_1479_ = lean_nat_dec_eq(v_next_1474_, v_pos_1477_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_box(v___x_1479_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1480_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v_slot_1475_);
return v___x_1483_;
}
else
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1504_; 
lean_inc(v_remaining_1478_);
lean_inc(v_pos_1477_);
lean_inc(v_value_1476_);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_slot_1475_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1505_ = lean_ctor_get(v_slot_1475_, 2);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_slot_1475_, 1);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_slot_1475_, 0);
lean_dec(v_unused_1507_);
v___x_1485_ = v_slot_1475_;
v_isShared_1486_ = v_isSharedCheck_1504_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v_slot_1475_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1504_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_dec_eq(v_remaining_1478_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1489_ = lean_box(v___x_1488_);
lean_inc(v_value_1476_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_value_1476_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = lean_nat_sub(v_remaining_1478_, v___x_1487_);
lean_dec(v_remaining_1478_);
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
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_value_1476_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_pos_1477_);
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
lean_dec(v_remaining_1478_);
v___x_1496_ = lean_box(v___x_1479_);
v___x_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_value_1476_);
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
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_pos_1477_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object* v_next_1508_, lean_object* v_slot_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(v_next_1508_, v_slot_1509_);
lean_dec(v_next_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object* v_inst_1511_, lean_object* v_slot_1512_, lean_object* v_next_1513_){
_start:
{
lean_object* v___f_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___f_1514_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1514_, 0, v_next_1513_);
v___x_1515_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1515_, 0, lean_box(0));
lean_closure_set(v___x_1515_, 1, lean_box(0));
lean_closure_set(v___x_1515_, 2, lean_box(0));
lean_closure_set(v___x_1515_, 3, v_slot_1512_);
lean_closure_set(v___x_1515_, 4, v___f_1514_);
v___x_1516_ = lean_apply_2(v_inst_1511_, lean_box(0), v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object* v_m_1517_, lean_object* v_00_u03b1_1518_, lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_slot_1521_, lean_object* v_next_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1520_, v_slot_1521_, v_next_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object* v_m_1525_, lean_object* v_00_u03b1_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_slot_1529_, lean_object* v_next_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(v_m_1525_, v_00_u03b1_1526_, v_inst_1527_, v_inst_1528_, v_slot_1529_, v_next_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_inst_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object* v_toApplicative_1533_, lean_object* v_fst_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_toPure_1536_; lean_object* v___x_1537_; 
v_toPure_1536_ = lean_ctor_get(v_toApplicative_1533_, 1);
lean_inc(v_toPure_1536_);
lean_dec_ref(v_toApplicative_1533_);
v___x_1537_ = lean_apply_2(v_toPure_1536_, lean_box(0), v_fst_1534_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object* v_inst_1538_, lean_object* v_toBind_1539_, lean_object* v___f_1540_, lean_object* v_____r_1541_, lean_object* v_st_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_inc(v___y_1543_);
v___x_1544_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1544_, 0, lean_box(0));
lean_closure_set(v___x_1544_, 1, lean_box(0));
lean_closure_set(v___x_1544_, 2, v___y_1543_);
lean_closure_set(v___x_1544_, 3, v_st_1542_);
v___x_1545_ = lean_apply_2(v_inst_1538_, lean_box(0), v___x_1544_);
v___x_1546_ = lean_apply_4(v_toBind_1539_, lean_box(0), lean_box(0), v___x_1545_, v___f_1540_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed(lean_object* v_inst_1547_, lean_object* v_toBind_1548_, lean_object* v___f_1549_, lean_object* v_____r_1550_, lean_object* v_st_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1547_, v_toBind_1548_, v___f_1549_, v_____r_1550_, v_st_1551_, v___y_1552_);
lean_dec(v___y_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object* v_snd_1554_, lean_object* v_waiters_1555_, lean_object* v_capacity_1556_, lean_object* v_size_1557_, lean_object* v_buffer_1558_, lean_object* v_write_1559_, lean_object* v_read_1560_, lean_object* v_receivers_1561_, lean_object* v_nextId_1562_, uint8_t v_closed_1563_, lean_object* v_pos_1564_, lean_object* v___f_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1568_, 0, v_snd_1554_);
lean_ctor_set(v___x_1568_, 1, v_waiters_1555_);
lean_ctor_set(v___x_1568_, 2, v_capacity_1556_);
lean_ctor_set(v___x_1568_, 3, v_size_1557_);
lean_ctor_set(v___x_1568_, 4, v_buffer_1558_);
lean_ctor_set(v___x_1568_, 5, v_write_1559_);
lean_ctor_set(v___x_1568_, 6, v_read_1560_);
lean_ctor_set(v___x_1568_, 7, v_receivers_1561_);
lean_ctor_set(v___x_1568_, 8, v_nextId_1562_);
lean_ctor_set(v___x_1568_, 9, v_pos_1564_);
lean_ctor_set_uint8(v___x_1568_, sizeof(void*)*10, v_closed_1563_);
v___x_1569_ = lean_box(0);
lean_inc(v_a_1566_);
v___x_1570_ = lean_apply_3(v___f_1565_, v___x_1569_, v___x_1568_, v_a_1566_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object* v_snd_1571_, lean_object* v_waiters_1572_, lean_object* v_capacity_1573_, lean_object* v_size_1574_, lean_object* v_buffer_1575_, lean_object* v_write_1576_, lean_object* v_read_1577_, lean_object* v_receivers_1578_, lean_object* v_nextId_1579_, lean_object* v_closed_1580_, lean_object* v_pos_1581_, lean_object* v___f_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
uint8_t v_closed_boxed_1585_; lean_object* v_res_1586_; 
v_closed_boxed_1585_ = lean_unbox(v_closed_1580_);
v_res_1586_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1571_, v_waiters_1572_, v_capacity_1573_, v_size_1574_, v_buffer_1575_, v_write_1576_, v_read_1577_, v_receivers_1578_, v_nextId_1579_, v_closed_boxed_1585_, v_pos_1581_, v___f_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1583_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object* v_toApplicative_1587_, lean_object* v_inst_1588_, lean_object* v_toBind_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, uint8_t v___x_1592_, lean_object* v_inst_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_fst_1595_; 
v_fst_1595_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_fst_1595_);
if (lean_obj_tag(v_fst_1595_) == 1)
{
lean_object* v_snd_1596_; lean_object* v___f_1597_; lean_object* v___f_1598_; uint8_t v___x_1599_; 
v_snd_1596_ = lean_ctor_get(v_a_1594_, 1);
lean_inc(v_snd_1596_);
lean_dec_ref(v_a_1594_);
v___f_1597_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1597_, 0, v_toApplicative_1587_);
lean_closure_set(v___f_1597_, 1, v_fst_1595_);
lean_inc_ref(v___f_1597_);
lean_inc(v_toBind_1589_);
lean_inc(v_inst_1588_);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1598_, 0, v_inst_1588_);
lean_closure_set(v___f_1598_, 1, v_toBind_1589_);
lean_closure_set(v___f_1598_, 2, v___f_1597_);
v___x_1599_ = lean_unbox(v_snd_1596_);
lean_dec(v_snd_1596_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec_ref(v___f_1598_);
lean_dec(v_inst_1593_);
v___x_1600_ = lean_box(0);
v___x_1601_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1588_, v_toBind_1589_, v___f_1597_, v___x_1600_, v_a_1590_, v_a_1591_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v_producers_1603_; lean_object* v_waiters_1604_; lean_object* v_capacity_1605_; lean_object* v_size_1606_; lean_object* v_buffer_1607_; lean_object* v_write_1608_; lean_object* v_read_1609_; lean_object* v_receivers_1610_; lean_object* v_nextId_1611_; uint8_t v_closed_1612_; lean_object* v_pos_1613_; lean_object* v___x_1614_; 
v___x_1602_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_1590_);
v_producers_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_ref(v_producers_1603_);
v_waiters_1604_ = lean_ctor_get(v___x_1602_, 1);
lean_inc_ref(v_waiters_1604_);
v_capacity_1605_ = lean_ctor_get(v___x_1602_, 2);
lean_inc(v_capacity_1605_);
v_size_1606_ = lean_ctor_get(v___x_1602_, 3);
lean_inc(v_size_1606_);
v_buffer_1607_ = lean_ctor_get(v___x_1602_, 4);
lean_inc_ref(v_buffer_1607_);
v_write_1608_ = lean_ctor_get(v___x_1602_, 5);
lean_inc(v_write_1608_);
v_read_1609_ = lean_ctor_get(v___x_1602_, 6);
lean_inc(v_read_1609_);
v_receivers_1610_ = lean_ctor_get(v___x_1602_, 7);
lean_inc(v_receivers_1610_);
v_nextId_1611_ = lean_ctor_get(v___x_1602_, 8);
lean_inc(v_nextId_1611_);
v_closed_1612_ = lean_ctor_get_uint8(v___x_1602_, sizeof(void*)*10);
v_pos_1613_ = lean_ctor_get(v___x_1602_, 9);
lean_inc(v_pos_1613_);
v___x_1614_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1603_);
if (lean_obj_tag(v___x_1614_) == 1)
{
lean_object* v_val_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec_ref(v___x_1602_);
lean_dec_ref(v___f_1597_);
lean_dec(v_inst_1588_);
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v_fst_1616_ = lean_ctor_get(v_val_1615_, 0);
lean_inc(v_fst_1616_);
v_snd_1617_ = lean_ctor_get(v_val_1615_, 1);
lean_inc(v_snd_1617_);
lean_dec(v_val_1615_);
v___x_1618_ = lean_box(v_closed_1612_);
lean_inc(v_a_1591_);
v___f_1619_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1619_, 0, v_snd_1617_);
lean_closure_set(v___f_1619_, 1, v_waiters_1604_);
lean_closure_set(v___f_1619_, 2, v_capacity_1605_);
lean_closure_set(v___f_1619_, 3, v_size_1606_);
lean_closure_set(v___f_1619_, 4, v_buffer_1607_);
lean_closure_set(v___f_1619_, 5, v_write_1608_);
lean_closure_set(v___f_1619_, 6, v_read_1609_);
lean_closure_set(v___f_1619_, 7, v_receivers_1610_);
lean_closure_set(v___f_1619_, 8, v_nextId_1611_);
lean_closure_set(v___f_1619_, 9, v___x_1618_);
lean_closure_set(v___f_1619_, 10, v_pos_1613_);
lean_closure_set(v___f_1619_, 11, v___f_1598_);
lean_closure_set(v___f_1619_, 12, v_a_1591_);
v___x_1620_ = lean_box(v___x_1592_);
v___x_1621_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1621_, 0, lean_box(0));
lean_closure_set(v___x_1621_, 1, v___x_1620_);
lean_closure_set(v___x_1621_, 2, v_fst_1616_);
v___x_1622_ = lean_apply_2(v_inst_1593_, lean_box(0), v___x_1621_);
v___x_1623_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1622_, v___f_1619_);
return v___x_1623_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v___x_1614_);
lean_dec(v_pos_1613_);
lean_dec(v_nextId_1611_);
lean_dec(v_receivers_1610_);
lean_dec(v_read_1609_);
lean_dec(v_write_1608_);
lean_dec_ref(v_buffer_1607_);
lean_dec(v_size_1606_);
lean_dec(v_capacity_1605_);
lean_dec_ref(v_waiters_1604_);
lean_dec_ref(v___f_1598_);
lean_dec(v_inst_1593_);
v___x_1624_ = lean_box(0);
v___x_1625_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1588_, v_toBind_1589_, v___f_1597_, v___x_1624_, v___x_1602_, v_a_1591_);
return v___x_1625_;
}
}
}
else
{
lean_object* v_toPure_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec(v_fst_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_inst_1593_);
lean_dec_ref(v_a_1590_);
lean_dec(v_toBind_1589_);
lean_dec(v_inst_1588_);
v_toPure_1626_ = lean_ctor_get(v_toApplicative_1587_, 1);
lean_inc(v_toPure_1626_);
lean_dec_ref(v_toApplicative_1587_);
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_apply_2(v_toPure_1626_, lean_box(0), v___x_1627_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object* v_toApplicative_1629_, lean_object* v_inst_1630_, lean_object* v_toBind_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v___x_1634_, lean_object* v_inst_1635_, lean_object* v_a_1636_){
_start:
{
uint8_t v___x_789__boxed_1637_; lean_object* v_res_1638_; 
v___x_789__boxed_1637_ = lean_unbox(v___x_1634_);
v_res_1638_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1629_, v_inst_1630_, v_toBind_1631_, v_a_1632_, v_a_1633_, v___x_789__boxed_1637_, v_inst_1635_, v_a_1636_);
lean_dec(v_a_1633_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object* v_inst_1639_, lean_object* v_next_1640_, lean_object* v_toBind_1641_, lean_object* v___f_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1639_, v_a_1643_, v_next_1640_);
v___x_1645_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1644_, v___f_1642_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object* v_a_1646_, lean_object* v_toApplicative_1647_, lean_object* v_inst_1648_, lean_object* v_toBind_1649_, lean_object* v_a_1650_, lean_object* v_inst_1651_, lean_object* v_next_1652_, lean_object* v_inst_1653_, uint8_t v_a_1654_){
_start:
{
if (v_a_1654_ == 0)
{
lean_object* v_capacity_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___f_1658_; lean_object* v___f_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_capacity_1655_ = lean_ctor_get(v_a_1646_, 2);
lean_inc(v_capacity_1655_);
v___x_1656_ = 1;
v___x_1657_ = lean_box(v___x_1656_);
lean_inc(v_a_1650_);
lean_inc_n(v_toBind_1649_, 2);
lean_inc_n(v_inst_1648_, 2);
v___f_1658_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1658_, 0, v_toApplicative_1647_);
lean_closure_set(v___f_1658_, 1, v_inst_1648_);
lean_closure_set(v___f_1658_, 2, v_toBind_1649_);
lean_closure_set(v___f_1658_, 3, v_a_1646_);
lean_closure_set(v___f_1658_, 4, v_a_1650_);
lean_closure_set(v___f_1658_, 5, v___x_1657_);
lean_closure_set(v___f_1658_, 6, v_inst_1651_);
lean_inc(v_next_1652_);
v___f_1659_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1659_, 0, v_inst_1648_);
lean_closure_set(v___f_1659_, 1, v_next_1652_);
lean_closure_set(v___f_1659_, 2, v_toBind_1649_);
lean_closure_set(v___f_1659_, 3, v___f_1658_);
v___x_1660_ = lean_nat_mod(v_next_1652_, v_capacity_1655_);
lean_dec(v_capacity_1655_);
lean_dec(v_next_1652_);
v___x_1661_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1653_, v_inst_1648_, v___x_1660_, v_a_1650_);
v___x_1662_ = lean_apply_4(v_toBind_1649_, lean_box(0), lean_box(0), v___x_1661_, v___f_1659_);
return v___x_1662_;
}
else
{
lean_object* v_toPure_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec_ref(v_inst_1653_);
lean_dec(v_next_1652_);
lean_dec(v_inst_1651_);
lean_dec(v_toBind_1649_);
lean_dec(v_inst_1648_);
lean_dec_ref(v_a_1646_);
v_toPure_1663_ = lean_ctor_get(v_toApplicative_1647_, 1);
lean_inc(v_toPure_1663_);
lean_dec_ref(v_toApplicative_1647_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_apply_2(v_toPure_1663_, lean_box(0), v___x_1664_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object* v_a_1666_, lean_object* v_toApplicative_1667_, lean_object* v_inst_1668_, lean_object* v_toBind_1669_, lean_object* v_a_1670_, lean_object* v_inst_1671_, lean_object* v_next_1672_, lean_object* v_inst_1673_, lean_object* v_a_1674_){
_start:
{
uint8_t v_a_boxed_1675_; lean_object* v_res_1676_; 
v_a_boxed_1675_ = lean_unbox(v_a_1674_);
v_res_1676_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1666_, v_toApplicative_1667_, v_inst_1668_, v_toBind_1669_, v_a_1670_, v_inst_1671_, v_next_1672_, v_inst_1673_, v_a_boxed_1675_);
lean_dec(v_a_1670_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object* v_toApplicative_1677_, lean_object* v_inst_1678_, lean_object* v_toBind_1679_, lean_object* v_a_1680_, lean_object* v_inst_1681_, lean_object* v_next_1682_, lean_object* v_inst_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___f_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_inc_ref(v_inst_1683_);
lean_inc(v_a_1680_);
lean_inc(v_toBind_1679_);
lean_inc(v_inst_1678_);
v___f_1685_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_1685_, 0, v_a_1684_);
lean_closure_set(v___f_1685_, 1, v_toApplicative_1677_);
lean_closure_set(v___f_1685_, 2, v_inst_1678_);
lean_closure_set(v___f_1685_, 3, v_toBind_1679_);
lean_closure_set(v___f_1685_, 4, v_a_1680_);
lean_closure_set(v___f_1685_, 5, v_inst_1681_);
lean_closure_set(v___f_1685_, 6, v_next_1682_);
lean_closure_set(v___f_1685_, 7, v_inst_1683_);
v___x_1686_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_1683_, v_inst_1678_, v_a_1680_);
v___x_1687_ = lean_apply_4(v_toBind_1679_, lean_box(0), lean_box(0), v___x_1686_, v___f_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed(lean_object* v_toApplicative_1688_, lean_object* v_inst_1689_, lean_object* v_toBind_1690_, lean_object* v_a_1691_, lean_object* v_inst_1692_, lean_object* v_next_1693_, lean_object* v_inst_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(v_toApplicative_1688_, v_inst_1689_, v_toBind_1690_, v_a_1691_, v_inst_1692_, v_next_1693_, v_inst_1694_, v_a_1695_);
lean_dec(v_a_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_next_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v_toApplicative_1702_; lean_object* v_toBind_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_toApplicative_1702_ = lean_ctor_get(v_inst_1697_, 0);
lean_inc_ref(v_toApplicative_1702_);
v_toBind_1703_ = lean_ctor_get(v_inst_1697_, 1);
lean_inc_n(v_toBind_1703_, 2);
lean_inc_n(v_a_1701_, 2);
lean_inc(v_inst_1698_);
v___f_1704_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_1704_, 0, v_toApplicative_1702_);
lean_closure_set(v___f_1704_, 1, v_inst_1698_);
lean_closure_set(v___f_1704_, 2, v_toBind_1703_);
lean_closure_set(v___f_1704_, 3, v_a_1701_);
lean_closure_set(v___f_1704_, 4, v_inst_1699_);
lean_closure_set(v___f_1704_, 5, v_next_1700_);
lean_closure_set(v___f_1704_, 6, v_inst_1697_);
v___x_1705_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1705_, 0, lean_box(0));
lean_closure_set(v___x_1705_, 1, lean_box(0));
lean_closure_set(v___x_1705_, 2, v_a_1701_);
v___x_1706_ = lean_apply_2(v_inst_1698_, lean_box(0), v___x_1705_);
v___x_1707_ = lean_apply_4(v_toBind_1703_, lean_box(0), lean_box(0), v___x_1706_, v___f_1704_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___boxed(lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_next_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1708_, v_inst_1709_, v_inst_1710_, v_next_1711_, v_a_1712_);
lean_dec(v_a_1712_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object* v_m_1714_, lean_object* v_00_u03b1_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_next_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1716_, v_inst_1717_, v_inst_1718_, v_next_1719_, v_a_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___boxed(lean_object* v_m_1722_, lean_object* v_00_u03b1_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_next_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(v_m_1722_, v_00_u03b1_1723_, v_inst_1724_, v_inst_1725_, v_inst_1726_, v_next_1727_, v_a_1728_);
lean_dec(v_a_1728_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_capacity_1734_; lean_object* v_buffer_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1733_ = lean_st_ref_get(v_a_1731_);
v_capacity_1734_ = lean_ctor_get(v___x_1733_, 2);
lean_inc(v_capacity_1734_);
v_buffer_1735_ = lean_ctor_get(v___x_1733_, 4);
lean_inc_ref(v_buffer_1735_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_nat_mod(v_place_1730_, v_capacity_1734_);
lean_dec(v_capacity_1734_);
v___x_1737_ = lean_array_fget(v_buffer_1735_, v___x_1736_);
lean_dec(v___x_1736_);
lean_dec_ref(v_buffer_1735_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_1739_, lean_object* v_a_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_1739_, v_a_1740_);
lean_dec(v_a_1740_);
lean_dec(v_place_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_1743_){
_start:
{
lean_object* v___x_1745_; lean_object* v_size_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1745_ = lean_st_ref_get(v_a_1743_);
v_size_1746_ = lean_ctor_get(v___x_1745_, 3);
lean_inc(v_size_1746_);
lean_dec(v___x_1745_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_nat_dec_eq(v_size_1746_, v___x_1747_);
lean_dec(v_size_1746_);
v___x_1749_ = lean_box(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1751_);
lean_dec(v_a_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_1754_, lean_object* v_next_1755_){
_start:
{
lean_object* v___x_1757_; lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v_value_1763_; lean_object* v_pos_1764_; lean_object* v_remaining_1765_; uint8_t v___x_1766_; 
v___x_1757_ = lean_st_ref_take(v_slot_1754_);
v_value_1763_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_value_1763_);
v_pos_1764_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_pos_1764_);
v_remaining_1765_ = lean_ctor_get(v___x_1757_, 2);
lean_inc(v_remaining_1765_);
v___x_1766_ = lean_nat_dec_eq(v_next_1755_, v_pos_1764_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v_remaining_1765_);
lean_dec(v_pos_1764_);
lean_dec(v_value_1763_);
v___x_1767_ = lean_box(0);
v___x_1768_ = lean_box(v___x_1766_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v_fst_1759_ = v___x_1769_;
v_snd_1760_ = v___x_1757_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1788_; 
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; 
v_unused_1789_ = lean_ctor_get(v___x_1757_, 2);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v___x_1757_, 1);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v___x_1757_, 0);
lean_dec(v_unused_1791_);
v___x_1771_ = v___x_1757_;
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
else
{
lean_dec(v___x_1757_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = lean_unsigned_to_nat(1u);
v___x_1774_ = lean_nat_dec_eq(v_remaining_1765_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1775_ = lean_box(v___x_1774_);
lean_inc(v_value_1763_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_value_1763_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_nat_sub(v_remaining_1765_, v___x_1773_);
lean_dec(v_remaining_1765_);
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
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_value_1763_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_pos_1764_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
v_fst_1759_ = v___x_1776_;
v_snd_1760_ = v___x_1779_;
goto v___jp_1758_;
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec(v_remaining_1765_);
v___x_1781_ = lean_box(v___x_1766_);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v_value_1763_);
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
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_pos_1764_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
v_fst_1759_ = v___x_1782_;
v_snd_1760_ = v___x_1786_;
goto v___jp_1758_;
}
}
}
}
v___jp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_st_ref_put(v_slot_1754_, v_snd_1760_);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v_fst_1759_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_1792_, lean_object* v_next_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_1792_, v_next_1793_);
lean_dec(v_next_1793_);
lean_dec(v_slot_1792_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1874_; 
v___x_1799_ = lean_st_ref_get(v_a_1797_);
v___x_1800_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1797_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1874_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1874_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_unbox(v_a_1801_);
lean_dec(v_a_1801_);
if (v___x_1805_ == 0)
{
lean_object* v_capacity_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1869_; 
lean_del_object(v___x_1803_);
v_capacity_1806_ = lean_ctor_get(v___x_1799_, 2);
lean_inc(v_capacity_1806_);
v___x_1807_ = 1;
v___x_1808_ = lean_nat_mod(v_next_1796_, v_capacity_1806_);
lean_dec(v_capacity_1806_);
v___x_1809_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_1808_, v_a_1797_);
lean_dec(v___x_1808_);
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1869_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1869_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1868_; 
v___x_1814_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_1810_, v_next_1796_);
lean_dec(v_a_1810_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1868_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1868_;
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
lean_dec(v_snd_1820_);
if (v___x_1828_ == 0)
{
v_st_1822_ = v___x_1799_;
v___y_1823_ = v_a_1797_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1829_; lean_object* v_producers_1830_; lean_object* v_waiters_1831_; lean_object* v_capacity_1832_; lean_object* v_size_1833_; lean_object* v_buffer_1834_; lean_object* v_write_1835_; lean_object* v_read_1836_; lean_object* v_receivers_1837_; lean_object* v_nextId_1838_; uint8_t v_closed_1839_; lean_object* v_pos_1840_; lean_object* v___x_1841_; 
v___x_1829_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_1799_);
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
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1853_; 
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; 
v_unused_1854_ = lean_ctor_get(v___x_1829_, 9);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v___x_1829_, 8);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v___x_1829_, 7);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v___x_1829_, 6);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v___x_1829_, 5);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v___x_1829_, 4);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v___x_1829_, 3);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v___x_1829_, 2);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v___x_1829_, 1);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1863_);
v___x_1843_ = v___x_1829_;
v_isShared_1844_ = v_isSharedCheck_1853_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v___x_1829_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1853_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_val_1845_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v_val_1845_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_val_1845_);
lean_dec_ref_known(v___x_1841_, 1);
v_fst_1846_ = lean_ctor_get(v_val_1845_, 0);
lean_inc(v_fst_1846_);
v_snd_1847_ = lean_ctor_get(v_val_1845_, 1);
lean_inc(v_snd_1847_);
lean_dec(v_val_1845_);
v___x_1848_ = lean_box(v___x_1807_);
v___x_1849_ = lean_io_promise_resolve(v___x_1848_, v_fst_1846_);
lean_dec(v_fst_1846_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v_snd_1847_);
v___x_1851_ = v___x_1843_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_snd_1847_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_waiters_1831_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_capacity_1832_);
lean_ctor_set(v_reuseFailAlloc_1852_, 3, v_size_1833_);
lean_ctor_set(v_reuseFailAlloc_1852_, 4, v_buffer_1834_);
lean_ctor_set(v_reuseFailAlloc_1852_, 5, v_write_1835_);
lean_ctor_set(v_reuseFailAlloc_1852_, 6, v_read_1836_);
lean_ctor_set(v_reuseFailAlloc_1852_, 7, v_receivers_1837_);
lean_ctor_set(v_reuseFailAlloc_1852_, 8, v_nextId_1838_);
lean_ctor_set(v_reuseFailAlloc_1852_, 9, v_pos_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1852_, sizeof(void*)*10, v_closed_1839_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
v_st_1822_ = v___x_1851_;
v___y_1823_ = v_a_1797_;
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
v_st_1822_ = v___x_1829_;
v___y_1823_ = v_a_1797_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec(v_snd_1820_);
lean_dec(v_fst_1819_);
lean_del_object(v___x_1817_);
lean_dec(v___x_1799_);
v___x_1864_ = lean_box(0);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1864_);
v___x_1866_ = v___x_1812_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
v___jp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_st_ref_swap(v___y_1823_, v_st_1822_);
lean_dec(v___x_1824_);
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
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec(v___x_1799_);
v___x_1870_ = lean_box(0);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1870_);
v___x_1872_ = v___x_1803_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_1875_, lean_object* v_a_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_1875_, v_a_1876_);
lean_dec(v_a_1876_);
lean_dec(v_next_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_a_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_fst_1882_; lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1925_; 
v_fst_1882_ = lean_ctor_get(v_a_1879_, 0);
v_snd_1883_ = lean_ctor_get(v_a_1879_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_a_1879_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1885_ = v_a_1879_;
v_isShared_1886_ = v_isSharedCheck_1925_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_inc(v_fst_1882_);
lean_dec(v_a_1879_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1925_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
uint8_t v___y_1888_; lean_object* v_size_1920_; lean_object* v_pos_1921_; uint8_t v___x_1922_; 
v_size_1920_ = lean_ctor_get(v_fst_1882_, 3);
v_pos_1921_ = lean_ctor_get(v_fst_1882_, 9);
v___x_1922_ = lean_nat_dec_lt(v_snd_1883_, v_pos_1921_);
if (v___x_1922_ == 0)
{
v___y_1888_ = v___x_1922_;
goto v___jp_1887_;
}
else
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_nat_dec_lt(v___x_1923_, v_size_1920_);
v___y_1888_ = v___x_1924_;
goto v___jp_1887_;
}
v___jp_1887_:
{
if (v___y_1888_ == 0)
{
lean_object* v___x_1890_; 
if (v_isShared_1886_ == 0)
{
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_fst_1882_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_snd_1883_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
else
{
lean_object* v___x_1893_; 
v___x_1893_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_1883_, v___y_1880_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1911_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1911_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1911_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
if (lean_obj_tag(v_a_1894_) == 1)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
lean_dec_ref_known(v_a_1894_, 1);
lean_del_object(v___x_1896_);
lean_dec(v_fst_1882_);
v___x_1898_ = lean_st_ref_get(v___y_1880_);
v___x_1899_ = lean_unsigned_to_nat(1u);
v___x_1900_ = lean_nat_add(v_snd_1883_, v___x_1899_);
lean_dec(v_snd_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___x_1900_);
lean_ctor_set(v___x_1885_, 0, v___x_1898_);
v___x_1902_ = v___x_1885_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
v_a_1879_ = v___x_1902_;
goto _start;
}
}
else
{
lean_object* v___x_1906_; 
lean_dec(v_a_1894_);
if (v_isShared_1886_ == 0)
{
v___x_1906_ = v___x_1885_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_fst_1882_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_snd_1883_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1906_);
v___x_1908_ = v___x_1896_;
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
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_del_object(v___x_1885_);
lean_dec(v_snd_1883_);
lean_dec(v_fst_1882_);
v_a_1912_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1893_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1893_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_a_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_1926_, v___y_1927_);
lean_dec(v___y_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_1930_, lean_object* v_k_1931_){
_start:
{
if (lean_obj_tag(v_t_1930_) == 0)
{
lean_object* v_k_1932_; lean_object* v_v_1933_; lean_object* v_l_1934_; lean_object* v_r_1935_; uint8_t v___x_1936_; 
v_k_1932_ = lean_ctor_get(v_t_1930_, 1);
v_v_1933_ = lean_ctor_get(v_t_1930_, 2);
v_l_1934_ = lean_ctor_get(v_t_1930_, 3);
v_r_1935_ = lean_ctor_get(v_t_1930_, 4);
v___x_1936_ = lean_nat_dec_lt(v_k_1931_, v_k_1932_);
if (v___x_1936_ == 0)
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_nat_dec_eq(v_k_1931_, v_k_1932_);
if (v___x_1937_ == 0)
{
v_t_1930_ = v_r_1935_;
goto _start;
}
else
{
lean_object* v___x_1939_; 
lean_inc(v_v_1933_);
v___x_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_v_1933_);
return v___x_1939_;
}
}
else
{
v_t_1930_ = v_l_1934_;
goto _start;
}
}
else
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_box(0);
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_1942_, lean_object* v_k_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_1942_, v_k_1943_);
lean_dec(v_k_1943_);
lean_dec(v_t_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_1945_, lean_object* v_t_1946_){
_start:
{
if (lean_obj_tag(v_t_1946_) == 0)
{
lean_object* v_k_1947_; lean_object* v_v_1948_; lean_object* v_l_1949_; lean_object* v_r_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_2605_; 
v_k_1947_ = lean_ctor_get(v_t_1946_, 1);
v_v_1948_ = lean_ctor_get(v_t_1946_, 2);
v_l_1949_ = lean_ctor_get(v_t_1946_, 3);
v_r_1950_ = lean_ctor_get(v_t_1946_, 4);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_t_1946_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v_t_1946_, 0);
lean_dec(v_unused_2606_);
v___x_1952_ = v_t_1946_;
v_isShared_1953_ = v_isSharedCheck_2605_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_r_1950_);
lean_inc(v_l_1949_);
lean_inc(v_v_1948_);
lean_inc(v_k_1947_);
lean_dec(v_t_1946_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_2605_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_nat_dec_lt(v_k_1945_, v_k_1947_);
if (v___x_1954_ == 0)
{
uint8_t v___x_1955_; 
v___x_1955_ = lean_nat_dec_eq(v_k_1945_, v_k_1947_);
if (v___x_1955_ == 0)
{
lean_object* v_impl_1956_; lean_object* v___x_1957_; 
v_impl_1956_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1945_, v_r_1950_);
v___x_1957_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1956_) == 0)
{
if (lean_obj_tag(v_l_1949_) == 0)
{
lean_object* v_size_1958_; lean_object* v_size_1959_; lean_object* v_k_1960_; lean_object* v_v_1961_; lean_object* v_l_1962_; lean_object* v_r_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v_size_1958_ = lean_ctor_get(v_impl_1956_, 0);
lean_inc(v_size_1958_);
v_size_1959_ = lean_ctor_get(v_l_1949_, 0);
v_k_1960_ = lean_ctor_get(v_l_1949_, 1);
v_v_1961_ = lean_ctor_get(v_l_1949_, 2);
v_l_1962_ = lean_ctor_get(v_l_1949_, 3);
v_r_1963_ = lean_ctor_get(v_l_1949_, 4);
lean_inc(v_r_1963_);
v___x_1964_ = lean_unsigned_to_nat(3u);
v___x_1965_ = lean_nat_mul(v___x_1964_, v_size_1958_);
v___x_1966_ = lean_nat_dec_lt(v___x_1965_, v_size_1959_);
lean_dec(v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
lean_dec(v_r_1963_);
v___x_1967_ = lean_nat_add(v___x_1957_, v_size_1959_);
v___x_1968_ = lean_nat_add(v___x_1967_, v_size_1958_);
lean_dec(v_size_1958_);
lean_dec(v___x_1967_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v_impl_1956_);
lean_ctor_set(v___x_1952_, 0, v___x_1968_);
v___x_1970_ = v___x_1952_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_l_1949_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v_impl_1956_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
else
{
lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2037_; 
lean_inc(v_l_1962_);
lean_inc(v_v_1961_);
lean_inc(v_k_1960_);
lean_inc(v_size_1959_);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_l_1949_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; lean_object* v_unused_2039_; lean_object* v_unused_2040_; lean_object* v_unused_2041_; lean_object* v_unused_2042_; 
v_unused_2038_ = lean_ctor_get(v_l_1949_, 4);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_l_1949_, 3);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_l_1949_, 2);
lean_dec(v_unused_2040_);
v_unused_2041_ = lean_ctor_get(v_l_1949_, 1);
lean_dec(v_unused_2041_);
v_unused_2042_ = lean_ctor_get(v_l_1949_, 0);
lean_dec(v_unused_2042_);
v___x_1973_ = v_l_1949_;
v_isShared_1974_ = v_isSharedCheck_2037_;
goto v_resetjp_1972_;
}
else
{
lean_dec(v_l_1949_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2037_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_size_1975_; lean_object* v_size_1976_; lean_object* v_k_1977_; lean_object* v_v_1978_; lean_object* v_l_1979_; lean_object* v_r_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v_size_1975_ = lean_ctor_get(v_l_1962_, 0);
v_size_1976_ = lean_ctor_get(v_r_1963_, 0);
v_k_1977_ = lean_ctor_get(v_r_1963_, 1);
v_v_1978_ = lean_ctor_get(v_r_1963_, 2);
v_l_1979_ = lean_ctor_get(v_r_1963_, 3);
v_r_1980_ = lean_ctor_get(v_r_1963_, 4);
v___x_1981_ = lean_unsigned_to_nat(2u);
v___x_1982_ = lean_nat_mul(v___x_1981_, v_size_1975_);
v___x_1983_ = lean_nat_dec_lt(v_size_1976_, v___x_1982_);
lean_dec(v___x_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2012_; 
lean_inc(v_r_1980_);
lean_inc(v_l_1979_);
lean_inc(v_v_1978_);
lean_inc(v_k_1977_);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_r_1963_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; lean_object* v_unused_2014_; lean_object* v_unused_2015_; lean_object* v_unused_2016_; lean_object* v_unused_2017_; 
v_unused_2013_ = lean_ctor_get(v_r_1963_, 4);
lean_dec(v_unused_2013_);
v_unused_2014_ = lean_ctor_get(v_r_1963_, 3);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_r_1963_, 2);
lean_dec(v_unused_2015_);
v_unused_2016_ = lean_ctor_get(v_r_1963_, 1);
lean_dec(v_unused_2016_);
v_unused_2017_ = lean_ctor_get(v_r_1963_, 0);
lean_dec(v_unused_2017_);
v___x_1985_ = v_r_1963_;
v_isShared_1986_ = v_isSharedCheck_2012_;
goto v_resetjp_1984_;
}
else
{
lean_dec(v_r_1963_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2012_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___x_2000_; lean_object* v___y_2002_; 
v___x_1987_ = lean_nat_add(v___x_1957_, v_size_1959_);
lean_dec(v_size_1959_);
v___x_1988_ = lean_nat_add(v___x_1987_, v_size_1958_);
lean_dec(v___x_1987_);
v___x_2000_ = lean_nat_add(v___x_1957_, v_size_1975_);
if (lean_obj_tag(v_l_1979_) == 0)
{
lean_object* v_size_2010_; 
v_size_2010_ = lean_ctor_get(v_l_1979_, 0);
lean_inc(v_size_2010_);
v___y_2002_ = v_size_2010_;
goto v___jp_2001_;
}
else
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_unsigned_to_nat(0u);
v___y_2002_ = v___x_2011_;
goto v___jp_2001_;
}
v___jp_1989_:
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_nat_add(v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec(v___y_1991_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 4, v_impl_1956_);
lean_ctor_set(v___x_1985_, 3, v_r_1980_);
lean_ctor_set(v___x_1985_, 2, v_v_1948_);
lean_ctor_set(v___x_1985_, 1, v_k_1947_);
lean_ctor_set(v___x_1985_, 0, v___x_1993_);
v___x_1995_ = v___x_1985_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_r_1980_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_impl_1956_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 4, v___x_1995_);
lean_ctor_set(v___x_1973_, 3, v___y_1990_);
lean_ctor_set(v___x_1973_, 2, v_v_1978_);
lean_ctor_set(v___x_1973_, 1, v_k_1977_);
lean_ctor_set(v___x_1973_, 0, v___x_1988_);
v___x_1997_ = v___x_1973_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_k_1977_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_v_1978_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v___y_1990_);
lean_ctor_set(v_reuseFailAlloc_1998_, 4, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
v___jp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = lean_nat_add(v___x_2000_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec(v___x_2000_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v_l_1979_);
lean_ctor_set(v___x_1952_, 3, v_l_1962_);
lean_ctor_set(v___x_1952_, 2, v_v_1961_);
lean_ctor_set(v___x_1952_, 1, v_k_1960_);
lean_ctor_set(v___x_1952_, 0, v___x_2003_);
v___x_2005_ = v___x_1952_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_k_1960_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_v_1961_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_l_1962_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_l_1979_);
v___x_2005_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_nat_add(v___x_1957_, v_size_1958_);
lean_dec(v_size_1958_);
if (lean_obj_tag(v_r_1980_) == 0)
{
lean_object* v_size_2007_; 
v_size_2007_ = lean_ctor_get(v_r_1980_, 0);
lean_inc(v_size_2007_);
v___y_1990_ = v___x_2005_;
v___y_1991_ = v___x_2006_;
v___y_1992_ = v_size_2007_;
goto v___jp_1989_;
}
else
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_unsigned_to_nat(0u);
v___y_1990_ = v___x_2005_;
v___y_1991_ = v___x_2006_;
v___y_1992_ = v___x_2008_;
goto v___jp_1989_;
}
}
}
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_del_object(v___x_1952_);
v___x_2018_ = lean_nat_add(v___x_1957_, v_size_1959_);
lean_dec(v_size_1959_);
v___x_2019_ = lean_nat_add(v___x_2018_, v_size_1958_);
lean_dec(v___x_2018_);
v___x_2020_ = lean_nat_add(v___x_1957_, v_size_1958_);
lean_dec(v_size_1958_);
v___x_2021_ = lean_nat_add(v___x_2020_, v_size_1976_);
lean_dec(v___x_2020_);
lean_inc_ref(v_impl_1956_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 4, v_impl_1956_);
lean_ctor_set(v___x_1973_, 3, v_r_1963_);
lean_ctor_set(v___x_1973_, 2, v_v_1948_);
lean_ctor_set(v___x_1973_, 1, v_k_1947_);
lean_ctor_set(v___x_1973_, 0, v___x_2021_);
v___x_2023_ = v___x_1973_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_r_1963_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_impl_1956_);
v___x_2023_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_isSharedCheck_2030_ = !lean_is_exclusive(v_impl_1956_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; lean_object* v_unused_2034_; lean_object* v_unused_2035_; 
v_unused_2031_ = lean_ctor_get(v_impl_1956_, 4);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_impl_1956_, 3);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_impl_1956_, 2);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_impl_1956_, 1);
lean_dec(v_unused_2034_);
v_unused_2035_ = lean_ctor_get(v_impl_1956_, 0);
lean_dec(v_unused_2035_);
v___x_2025_ = v_impl_1956_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v_impl_1956_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 4, v___x_2023_);
lean_ctor_set(v___x_2025_, 3, v_l_1962_);
lean_ctor_set(v___x_2025_, 2, v_v_1961_);
lean_ctor_set(v___x_2025_, 1, v_k_1960_);
lean_ctor_set(v___x_2025_, 0, v___x_2019_);
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_k_1960_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_v_1961_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_l_1962_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v___x_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v_size_2043_ = lean_ctor_get(v_impl_1956_, 0);
lean_inc(v_size_2043_);
v___x_2044_ = lean_nat_add(v___x_1957_, v_size_2043_);
lean_dec(v_size_2043_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v_impl_1956_);
lean_ctor_set(v___x_1952_, 0, v___x_2044_);
v___x_2046_ = v___x_1952_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_l_1949_);
lean_ctor_set(v_reuseFailAlloc_2047_, 4, v_impl_1956_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
else
{
if (lean_obj_tag(v_l_1949_) == 0)
{
lean_object* v_l_2048_; 
v_l_2048_ = lean_ctor_get(v_l_1949_, 3);
if (lean_obj_tag(v_l_2048_) == 0)
{
lean_object* v_r_2049_; 
lean_inc_ref(v_l_2048_);
v_r_2049_ = lean_ctor_get(v_l_1949_, 4);
lean_inc(v_r_2049_);
if (lean_obj_tag(v_r_2049_) == 0)
{
lean_object* v_size_2050_; lean_object* v_k_2051_; lean_object* v_v_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2065_; 
v_size_2050_ = lean_ctor_get(v_l_1949_, 0);
v_k_2051_ = lean_ctor_get(v_l_1949_, 1);
v_v_2052_ = lean_ctor_get(v_l_1949_, 2);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_l_1949_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; lean_object* v_unused_2067_; 
v_unused_2066_ = lean_ctor_get(v_l_1949_, 4);
lean_dec(v_unused_2066_);
v_unused_2067_ = lean_ctor_get(v_l_1949_, 3);
lean_dec(v_unused_2067_);
v___x_2054_ = v_l_1949_;
v_isShared_2055_ = v_isSharedCheck_2065_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_v_2052_);
lean_inc(v_k_2051_);
lean_inc(v_size_2050_);
lean_dec(v_l_1949_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2065_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_size_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v_size_2056_ = lean_ctor_get(v_r_2049_, 0);
v___x_2057_ = lean_nat_add(v___x_1957_, v_size_2050_);
lean_dec(v_size_2050_);
v___x_2058_ = lean_nat_add(v___x_1957_, v_size_2056_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 4, v_impl_1956_);
lean_ctor_set(v___x_2054_, 3, v_r_2049_);
lean_ctor_set(v___x_2054_, 2, v_v_1948_);
lean_ctor_set(v___x_2054_, 1, v_k_1947_);
lean_ctor_set(v___x_2054_, 0, v___x_2058_);
v___x_2060_ = v___x_2054_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2064_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2064_, 3, v_r_2049_);
lean_ctor_set(v_reuseFailAlloc_2064_, 4, v_impl_1956_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2062_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v___x_2060_);
lean_ctor_set(v___x_1952_, 3, v_l_2048_);
lean_ctor_set(v___x_1952_, 2, v_v_2052_);
lean_ctor_set(v___x_1952_, 1, v_k_2051_);
lean_ctor_set(v___x_1952_, 0, v___x_2057_);
v___x_2062_ = v___x_1952_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_k_2051_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v_v_2052_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v_l_2048_);
lean_ctor_set(v_reuseFailAlloc_2063_, 4, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_k_2068_; lean_object* v_v_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2080_; 
v_k_2068_ = lean_ctor_get(v_l_1949_, 1);
v_v_2069_ = lean_ctor_get(v_l_1949_, 2);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_l_1949_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; lean_object* v_unused_2082_; lean_object* v_unused_2083_; 
v_unused_2081_ = lean_ctor_get(v_l_1949_, 4);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_l_1949_, 3);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_l_1949_, 0);
lean_dec(v_unused_2083_);
v___x_2071_ = v_l_1949_;
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_v_2069_);
lean_inc(v_k_2068_);
lean_dec(v_l_1949_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_unsigned_to_nat(3u);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 3, v_r_2049_);
lean_ctor_set(v___x_2071_, 2, v_v_1948_);
lean_ctor_set(v___x_2071_, 1, v_k_1947_);
lean_ctor_set(v___x_2071_, 0, v___x_1957_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_r_2049_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_r_2049_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2077_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v___x_2075_);
lean_ctor_set(v___x_1952_, 3, v_l_2048_);
lean_ctor_set(v___x_1952_, 2, v_v_2069_);
lean_ctor_set(v___x_1952_, 1, v_k_2068_);
lean_ctor_set(v___x_1952_, 0, v___x_2073_);
v___x_2077_ = v___x_1952_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_2068_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_2069_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_l_2048_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v___x_2075_);
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
else
{
lean_object* v_r_2084_; 
v_r_2084_ = lean_ctor_get(v_l_1949_, 4);
lean_inc(v_r_2084_);
if (lean_obj_tag(v_r_2084_) == 0)
{
lean_object* v_k_2085_; lean_object* v_v_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2109_; 
lean_inc(v_l_2048_);
v_k_2085_ = lean_ctor_get(v_l_1949_, 1);
v_v_2086_ = lean_ctor_get(v_l_1949_, 2);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_l_1949_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; lean_object* v_unused_2111_; lean_object* v_unused_2112_; 
v_unused_2110_ = lean_ctor_get(v_l_1949_, 4);
lean_dec(v_unused_2110_);
v_unused_2111_ = lean_ctor_get(v_l_1949_, 3);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_l_1949_, 0);
lean_dec(v_unused_2112_);
v___x_2088_ = v_l_1949_;
v_isShared_2089_ = v_isSharedCheck_2109_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_v_2086_);
lean_inc(v_k_2085_);
lean_dec(v_l_1949_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2109_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_k_2090_; lean_object* v_v_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2105_; 
v_k_2090_ = lean_ctor_get(v_r_2084_, 1);
v_v_2091_ = lean_ctor_get(v_r_2084_, 2);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_r_2084_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; lean_object* v_unused_2107_; lean_object* v_unused_2108_; 
v_unused_2106_ = lean_ctor_get(v_r_2084_, 4);
lean_dec(v_unused_2106_);
v_unused_2107_ = lean_ctor_get(v_r_2084_, 3);
lean_dec(v_unused_2107_);
v_unused_2108_ = lean_ctor_get(v_r_2084_, 0);
lean_dec(v_unused_2108_);
v___x_2093_ = v_r_2084_;
v_isShared_2094_ = v_isSharedCheck_2105_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_v_2091_);
lean_inc(v_k_2090_);
lean_dec(v_r_2084_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2105_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(3u);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 4, v_l_2048_);
lean_ctor_set(v___x_2093_, 3, v_l_2048_);
lean_ctor_set(v___x_2093_, 2, v_v_2086_);
lean_ctor_set(v___x_2093_, 1, v_k_2085_);
lean_ctor_set(v___x_2093_, 0, v___x_1957_);
v___x_2097_ = v___x_2093_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_k_2085_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_v_2086_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v_l_2048_);
lean_ctor_set(v_reuseFailAlloc_2104_, 4, v_l_2048_);
v___x_2097_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 4, v_l_2048_);
lean_ctor_set(v___x_2088_, 2, v_v_1948_);
lean_ctor_set(v___x_2088_, 1, v_k_1947_);
lean_ctor_set(v___x_2088_, 0, v___x_1957_);
v___x_2099_ = v___x_2088_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_l_2048_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_l_2048_);
v___x_2099_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2101_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v___x_2099_);
lean_ctor_set(v___x_1952_, 3, v___x_2097_);
lean_ctor_set(v___x_1952_, 2, v_v_2091_);
lean_ctor_set(v___x_1952_, 1, v_k_2090_);
lean_ctor_set(v___x_1952_, 0, v___x_2095_);
v___x_2101_ = v___x_1952_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_k_2090_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_v_2091_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
else
{
lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2113_ = lean_unsigned_to_nat(2u);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v_r_2084_);
lean_ctor_set(v___x_1952_, 0, v___x_2113_);
v___x_2115_ = v___x_1952_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_1949_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_r_2084_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v___x_2118_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v_l_1949_);
lean_ctor_set(v___x_1952_, 0, v___x_1957_);
v___x_2118_ = v___x_1952_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_l_1949_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v_l_1949_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_del_object(v___x_1952_);
lean_dec(v_v_1948_);
lean_dec(v_k_1947_);
if (lean_obj_tag(v_l_1949_) == 0)
{
if (lean_obj_tag(v_r_1950_) == 0)
{
lean_object* v_size_2120_; lean_object* v_k_2121_; lean_object* v_v_2122_; lean_object* v_l_2123_; lean_object* v_r_2124_; lean_object* v_size_2125_; lean_object* v_k_2126_; lean_object* v_v_2127_; lean_object* v_l_2128_; lean_object* v_r_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_size_2120_ = lean_ctor_get(v_l_1949_, 0);
v_k_2121_ = lean_ctor_get(v_l_1949_, 1);
v_v_2122_ = lean_ctor_get(v_l_1949_, 2);
v_l_2123_ = lean_ctor_get(v_l_1949_, 3);
v_r_2124_ = lean_ctor_get(v_l_1949_, 4);
lean_inc(v_r_2124_);
v_size_2125_ = lean_ctor_get(v_r_1950_, 0);
v_k_2126_ = lean_ctor_get(v_r_1950_, 1);
v_v_2127_ = lean_ctor_get(v_r_1950_, 2);
v_l_2128_ = lean_ctor_get(v_r_1950_, 3);
lean_inc(v_l_2128_);
v_r_2129_ = lean_ctor_get(v_r_1950_, 4);
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = lean_nat_dec_lt(v_size_2120_, v_size_2125_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2267_; 
lean_inc(v_l_2123_);
lean_inc(v_v_2122_);
lean_inc(v_k_2121_);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_l_1949_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; lean_object* v_unused_2269_; lean_object* v_unused_2270_; lean_object* v_unused_2271_; lean_object* v_unused_2272_; 
v_unused_2268_ = lean_ctor_get(v_l_1949_, 4);
lean_dec(v_unused_2268_);
v_unused_2269_ = lean_ctor_get(v_l_1949_, 3);
lean_dec(v_unused_2269_);
v_unused_2270_ = lean_ctor_get(v_l_1949_, 2);
lean_dec(v_unused_2270_);
v_unused_2271_ = lean_ctor_get(v_l_1949_, 1);
lean_dec(v_unused_2271_);
v_unused_2272_ = lean_ctor_get(v_l_1949_, 0);
lean_dec(v_unused_2272_);
v___x_2133_ = v_l_1949_;
v_isShared_2134_ = v_isSharedCheck_2267_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v_l_1949_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2267_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v_tree_2136_; 
v___x_2135_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2121_, v_v_2122_, v_l_2123_, v_r_2124_);
v_tree_2136_ = lean_ctor_get(v___x_2135_, 2);
lean_inc(v_tree_2136_);
if (lean_obj_tag(v_tree_2136_) == 0)
{
lean_object* v_k_2137_; lean_object* v_v_2138_; lean_object* v_size_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_k_2137_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_k_2137_);
v_v_2138_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_v_2138_);
lean_dec_ref(v___x_2135_);
v_size_2139_ = lean_ctor_get(v_tree_2136_, 0);
v___x_2140_ = lean_unsigned_to_nat(3u);
v___x_2141_ = lean_nat_mul(v___x_2140_, v_size_2139_);
v___x_2142_ = lean_nat_dec_lt(v___x_2141_, v_size_2125_);
lean_dec(v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
lean_dec(v_l_2128_);
v___x_2143_ = lean_nat_add(v___x_2130_, v_size_2139_);
v___x_2144_ = lean_nat_add(v___x_2143_, v_size_2125_);
lean_dec(v___x_2143_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_r_1950_);
lean_ctor_set(v___x_2133_, 3, v_tree_2136_);
lean_ctor_set(v___x_2133_, 2, v_v_2138_);
lean_ctor_set(v___x_2133_, 1, v_k_2137_);
lean_ctor_set(v___x_2133_, 0, v___x_2144_);
v___x_2146_ = v___x_2133_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_k_2137_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_v_2138_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v_tree_2136_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v_r_1950_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
else
{
lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2202_; 
lean_inc(v_r_2129_);
lean_inc(v_v_2127_);
lean_inc(v_k_2126_);
lean_inc(v_size_2125_);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; lean_object* v_unused_2204_; lean_object* v_unused_2205_; lean_object* v_unused_2206_; lean_object* v_unused_2207_; 
v_unused_2203_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2203_);
v_unused_2204_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_r_1950_, 2);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_r_1950_, 1);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_r_1950_, 0);
lean_dec(v_unused_2207_);
v___x_2149_ = v_r_1950_;
v_isShared_2150_ = v_isSharedCheck_2202_;
goto v_resetjp_2148_;
}
else
{
lean_dec(v_r_1950_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2202_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_size_2151_; lean_object* v_k_2152_; lean_object* v_v_2153_; lean_object* v_l_2154_; lean_object* v_r_2155_; lean_object* v_size_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v_size_2151_ = lean_ctor_get(v_l_2128_, 0);
v_k_2152_ = lean_ctor_get(v_l_2128_, 1);
v_v_2153_ = lean_ctor_get(v_l_2128_, 2);
v_l_2154_ = lean_ctor_get(v_l_2128_, 3);
v_r_2155_ = lean_ctor_get(v_l_2128_, 4);
v_size_2156_ = lean_ctor_get(v_r_2129_, 0);
v___x_2157_ = lean_unsigned_to_nat(2u);
v___x_2158_ = lean_nat_mul(v___x_2157_, v_size_2156_);
v___x_2159_ = lean_nat_dec_lt(v_size_2151_, v___x_2158_);
lean_dec(v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2187_; 
lean_inc(v_r_2155_);
lean_inc(v_l_2154_);
lean_inc(v_v_2153_);
lean_inc(v_k_2152_);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_l_2128_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; lean_object* v_unused_2191_; lean_object* v_unused_2192_; 
v_unused_2188_ = lean_ctor_get(v_l_2128_, 4);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_l_2128_, 3);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_l_2128_, 2);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_l_2128_, 1);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_l_2128_, 0);
lean_dec(v_unused_2192_);
v___x_2161_ = v_l_2128_;
v_isShared_2162_ = v_isSharedCheck_2187_;
goto v_resetjp_2160_;
}
else
{
lean_dec(v_l_2128_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2187_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2177_; 
v___x_2163_ = lean_nat_add(v___x_2130_, v_size_2139_);
v___x_2164_ = lean_nat_add(v___x_2163_, v_size_2125_);
lean_dec(v_size_2125_);
if (lean_obj_tag(v_l_2154_) == 0)
{
lean_object* v_size_2185_; 
v_size_2185_ = lean_ctor_get(v_l_2154_, 0);
lean_inc(v_size_2185_);
v___y_2177_ = v_size_2185_;
goto v___jp_2176_;
}
else
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___y_2177_ = v___x_2186_;
goto v___jp_2176_;
}
v___jp_2165_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_nat_add(v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 4, v_r_2129_);
lean_ctor_set(v___x_2161_, 3, v_r_2155_);
lean_ctor_set(v___x_2161_, 2, v_v_2127_);
lean_ctor_set(v___x_2161_, 1, v_k_2126_);
lean_ctor_set(v___x_2161_, 0, v___x_2169_);
v___x_2171_ = v___x_2161_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_k_2126_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_v_2127_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_r_2155_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_r_2129_);
v___x_2171_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
lean_object* v___x_2173_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 4, v___x_2171_);
lean_ctor_set(v___x_2149_, 3, v___y_2166_);
lean_ctor_set(v___x_2149_, 2, v_v_2153_);
lean_ctor_set(v___x_2149_, 1, v_k_2152_);
lean_ctor_set(v___x_2149_, 0, v___x_2164_);
v___x_2173_ = v___x_2149_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_k_2152_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_v_2153_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v___y_2166_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
v___jp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2178_ = lean_nat_add(v___x_2163_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec(v___x_2163_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_l_2154_);
lean_ctor_set(v___x_2133_, 3, v_tree_2136_);
lean_ctor_set(v___x_2133_, 2, v_v_2138_);
lean_ctor_set(v___x_2133_, 1, v_k_2137_);
lean_ctor_set(v___x_2133_, 0, v___x_2178_);
v___x_2180_ = v___x_2133_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_k_2137_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_v_2138_);
lean_ctor_set(v_reuseFailAlloc_2184_, 3, v_tree_2136_);
lean_ctor_set(v_reuseFailAlloc_2184_, 4, v_l_2154_);
v___x_2180_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_nat_add(v___x_2130_, v_size_2156_);
if (lean_obj_tag(v_r_2155_) == 0)
{
lean_object* v_size_2182_; 
v_size_2182_ = lean_ctor_get(v_r_2155_, 0);
lean_inc(v_size_2182_);
v___y_2166_ = v___x_2180_;
v___y_2167_ = v___x_2181_;
v___y_2168_ = v_size_2182_;
goto v___jp_2165_;
}
else
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_unsigned_to_nat(0u);
v___y_2166_ = v___x_2180_;
v___y_2167_ = v___x_2181_;
v___y_2168_ = v___x_2183_;
goto v___jp_2165_;
}
}
}
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2193_ = lean_nat_add(v___x_2130_, v_size_2139_);
v___x_2194_ = lean_nat_add(v___x_2193_, v_size_2125_);
lean_dec(v_size_2125_);
v___x_2195_ = lean_nat_add(v___x_2193_, v_size_2151_);
lean_dec(v___x_2193_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 4, v_l_2128_);
lean_ctor_set(v___x_2149_, 3, v_tree_2136_);
lean_ctor_set(v___x_2149_, 2, v_v_2138_);
lean_ctor_set(v___x_2149_, 1, v_k_2137_);
lean_ctor_set(v___x_2149_, 0, v___x_2195_);
v___x_2197_ = v___x_2149_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_k_2137_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_v_2138_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_tree_2136_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_l_2128_);
v___x_2197_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2199_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_r_2129_);
lean_ctor_set(v___x_2133_, 3, v___x_2197_);
lean_ctor_set(v___x_2133_, 2, v_v_2127_);
lean_ctor_set(v___x_2133_, 1, v_k_2126_);
lean_ctor_set(v___x_2133_, 0, v___x_2194_);
v___x_2199_ = v___x_2133_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_2126_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_2127_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_r_2129_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
}
}
else
{
lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2261_; 
lean_inc(v_r_2129_);
lean_inc(v_v_2127_);
lean_inc(v_k_2126_);
lean_inc(v_size_2125_);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; lean_object* v_unused_2263_; lean_object* v_unused_2264_; lean_object* v_unused_2265_; lean_object* v_unused_2266_; 
v_unused_2262_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2263_);
v_unused_2264_ = lean_ctor_get(v_r_1950_, 2);
lean_dec(v_unused_2264_);
v_unused_2265_ = lean_ctor_get(v_r_1950_, 1);
lean_dec(v_unused_2265_);
v_unused_2266_ = lean_ctor_get(v_r_1950_, 0);
lean_dec(v_unused_2266_);
v___x_2209_ = v_r_1950_;
v_isShared_2210_ = v_isSharedCheck_2261_;
goto v_resetjp_2208_;
}
else
{
lean_dec(v_r_1950_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2261_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
if (lean_obj_tag(v_l_2128_) == 0)
{
if (lean_obj_tag(v_r_2129_) == 0)
{
lean_object* v_k_2211_; lean_object* v_v_2212_; lean_object* v_size_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v_k_2211_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_k_2211_);
v_v_2212_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_v_2212_);
lean_dec_ref(v___x_2135_);
v_size_2213_ = lean_ctor_get(v_l_2128_, 0);
v___x_2214_ = lean_nat_add(v___x_2130_, v_size_2125_);
lean_dec(v_size_2125_);
v___x_2215_ = lean_nat_add(v___x_2130_, v_size_2213_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 4, v_l_2128_);
lean_ctor_set(v___x_2209_, 3, v_tree_2136_);
lean_ctor_set(v___x_2209_, 2, v_v_2212_);
lean_ctor_set(v___x_2209_, 1, v_k_2211_);
lean_ctor_set(v___x_2209_, 0, v___x_2215_);
v___x_2217_ = v___x_2209_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_k_2211_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_v_2212_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_tree_2136_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_l_2128_);
v___x_2217_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_r_2129_);
lean_ctor_set(v___x_2133_, 3, v___x_2217_);
lean_ctor_set(v___x_2133_, 2, v_v_2127_);
lean_ctor_set(v___x_2133_, 1, v_k_2126_);
lean_ctor_set(v___x_2133_, 0, v___x_2214_);
v___x_2219_ = v___x_2133_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_k_2126_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_v_2127_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v_r_2129_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
else
{
lean_object* v_k_2222_; lean_object* v_v_2223_; lean_object* v_k_2224_; lean_object* v_v_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_size_2125_);
v_k_2222_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_k_2222_);
v_v_2223_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_v_2223_);
lean_dec_ref(v___x_2135_);
v_k_2224_ = lean_ctor_get(v_l_2128_, 1);
v_v_2225_ = lean_ctor_get(v_l_2128_, 2);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_l_2128_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; lean_object* v_unused_2241_; lean_object* v_unused_2242_; 
v_unused_2240_ = lean_ctor_get(v_l_2128_, 4);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_l_2128_, 3);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v_l_2128_, 0);
lean_dec(v_unused_2242_);
v___x_2227_ = v_l_2128_;
v_isShared_2228_ = v_isSharedCheck_2239_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_v_2225_);
lean_inc(v_k_2224_);
lean_dec(v_l_2128_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2239_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_unsigned_to_nat(3u);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 4, v_r_2129_);
lean_ctor_set(v___x_2227_, 3, v_r_2129_);
lean_ctor_set(v___x_2227_, 2, v_v_2223_);
lean_ctor_set(v___x_2227_, 1, v_k_2222_);
lean_ctor_set(v___x_2227_, 0, v___x_2130_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_k_2222_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_v_2223_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_r_2129_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_r_2129_);
v___x_2231_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 3, v_r_2129_);
lean_ctor_set(v___x_2209_, 0, v___x_2130_);
v___x_2233_ = v___x_2209_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_k_2126_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_v_2127_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v_r_2129_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_r_2129_);
v___x_2233_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v___x_2233_);
lean_ctor_set(v___x_2133_, 3, v___x_2231_);
lean_ctor_set(v___x_2133_, 2, v_v_2225_);
lean_ctor_set(v___x_2133_, 1, v_k_2224_);
lean_ctor_set(v___x_2133_, 0, v___x_2229_);
v___x_2235_ = v___x_2133_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_k_2224_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_v_2225_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2129_) == 0)
{
lean_object* v_k_2243_; lean_object* v_v_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
lean_dec(v_size_2125_);
v_k_2243_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_k_2243_);
v_v_2244_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_v_2244_);
lean_dec_ref(v___x_2135_);
v___x_2245_ = lean_unsigned_to_nat(3u);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 4, v_l_2128_);
lean_ctor_set(v___x_2209_, 2, v_v_2244_);
lean_ctor_set(v___x_2209_, 1, v_k_2243_);
lean_ctor_set(v___x_2209_, 0, v___x_2130_);
v___x_2247_ = v___x_2209_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_k_2243_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_v_2244_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v_l_2128_);
lean_ctor_set(v_reuseFailAlloc_2251_, 4, v_l_2128_);
v___x_2247_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_r_2129_);
lean_ctor_set(v___x_2133_, 3, v___x_2247_);
lean_ctor_set(v___x_2133_, 2, v_v_2127_);
lean_ctor_set(v___x_2133_, 1, v_k_2126_);
lean_ctor_set(v___x_2133_, 0, v___x_2245_);
v___x_2249_ = v___x_2133_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_k_2126_);
lean_ctor_set(v_reuseFailAlloc_2250_, 2, v_v_2127_);
lean_ctor_set(v_reuseFailAlloc_2250_, 3, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2250_, 4, v_r_2129_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
else
{
lean_object* v_k_2252_; lean_object* v_v_2253_; lean_object* v___x_2255_; 
v_k_2252_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_k_2252_);
v_v_2253_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_v_2253_);
lean_dec_ref(v___x_2135_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 3, v_r_2129_);
v___x_2255_ = v___x_2209_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_size_2125_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_k_2126_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_v_2127_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v_r_2129_);
lean_ctor_set(v_reuseFailAlloc_2260_, 4, v_r_2129_);
v___x_2255_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = lean_unsigned_to_nat(2u);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v___x_2255_);
lean_ctor_set(v___x_2133_, 3, v_r_2129_);
lean_ctor_set(v___x_2133_, 2, v_v_2253_);
lean_ctor_set(v___x_2133_, 1, v_k_2252_);
lean_ctor_set(v___x_2133_, 0, v___x_2256_);
v___x_2258_ = v___x_2133_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_k_2252_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v_v_2253_);
lean_ctor_set(v_reuseFailAlloc_2259_, 3, v_r_2129_);
lean_ctor_set(v_reuseFailAlloc_2259_, 4, v___x_2255_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
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
lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2425_; 
lean_inc(v_r_2129_);
lean_inc(v_v_2127_);
lean_inc(v_k_2126_);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; lean_object* v_unused_2427_; lean_object* v_unused_2428_; lean_object* v_unused_2429_; lean_object* v_unused_2430_; 
v_unused_2426_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2426_);
v_unused_2427_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2427_);
v_unused_2428_ = lean_ctor_get(v_r_1950_, 2);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_r_1950_, 1);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_r_1950_, 0);
lean_dec(v_unused_2430_);
v___x_2274_ = v_r_1950_;
v_isShared_2275_ = v_isSharedCheck_2425_;
goto v_resetjp_2273_;
}
else
{
lean_dec(v_r_1950_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2425_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v_tree_2277_; 
v___x_2276_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2126_, v_v_2127_, v_l_2128_, v_r_2129_);
v_tree_2277_ = lean_ctor_get(v___x_2276_, 2);
lean_inc(v_tree_2277_);
if (lean_obj_tag(v_tree_2277_) == 0)
{
lean_object* v_k_2278_; lean_object* v_v_2279_; lean_object* v_size_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_k_2278_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_k_2278_);
v_v_2279_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_v_2279_);
lean_dec_ref(v___x_2276_);
v_size_2280_ = lean_ctor_get(v_tree_2277_, 0);
v___x_2281_ = lean_unsigned_to_nat(3u);
v___x_2282_ = lean_nat_mul(v___x_2281_, v_size_2280_);
v___x_2283_ = lean_nat_dec_lt(v___x_2282_, v_size_2120_);
lean_dec(v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec(v_r_2124_);
v___x_2284_ = lean_nat_add(v___x_2130_, v_size_2120_);
v___x_2285_ = lean_nat_add(v___x_2284_, v_size_2280_);
lean_dec(v___x_2284_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_tree_2277_);
lean_ctor_set(v___x_2274_, 3, v_l_1949_);
lean_ctor_set(v___x_2274_, 2, v_v_2279_);
lean_ctor_set(v___x_2274_, 1, v_k_2278_);
lean_ctor_set(v___x_2274_, 0, v___x_2285_);
v___x_2287_ = v___x_2274_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_k_2278_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_v_2279_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v_l_1949_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_tree_2277_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
else
{
lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2354_; 
lean_inc(v_l_2123_);
lean_inc(v_v_2122_);
lean_inc(v_k_2121_);
lean_inc(v_size_2120_);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_l_1949_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; lean_object* v_unused_2356_; lean_object* v_unused_2357_; lean_object* v_unused_2358_; lean_object* v_unused_2359_; 
v_unused_2355_ = lean_ctor_get(v_l_1949_, 4);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_l_1949_, 3);
lean_dec(v_unused_2356_);
v_unused_2357_ = lean_ctor_get(v_l_1949_, 2);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v_l_1949_, 1);
lean_dec(v_unused_2358_);
v_unused_2359_ = lean_ctor_get(v_l_1949_, 0);
lean_dec(v_unused_2359_);
v___x_2290_ = v_l_1949_;
v_isShared_2291_ = v_isSharedCheck_2354_;
goto v_resetjp_2289_;
}
else
{
lean_dec(v_l_1949_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2354_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_size_2292_; lean_object* v_size_2293_; lean_object* v_k_2294_; lean_object* v_v_2295_; lean_object* v_l_2296_; lean_object* v_r_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_size_2292_ = lean_ctor_get(v_l_2123_, 0);
v_size_2293_ = lean_ctor_get(v_r_2124_, 0);
v_k_2294_ = lean_ctor_get(v_r_2124_, 1);
v_v_2295_ = lean_ctor_get(v_r_2124_, 2);
v_l_2296_ = lean_ctor_get(v_r_2124_, 3);
v_r_2297_ = lean_ctor_get(v_r_2124_, 4);
v___x_2298_ = lean_unsigned_to_nat(2u);
v___x_2299_ = lean_nat_mul(v___x_2298_, v_size_2292_);
v___x_2300_ = lean_nat_dec_lt(v_size_2293_, v___x_2299_);
lean_dec(v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2338_; 
lean_inc(v_r_2297_);
lean_inc(v_l_2296_);
lean_inc(v_v_2295_);
lean_inc(v_k_2294_);
lean_del_object(v___x_2290_);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_r_2124_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; lean_object* v_unused_2340_; lean_object* v_unused_2341_; lean_object* v_unused_2342_; lean_object* v_unused_2343_; 
v_unused_2339_ = lean_ctor_get(v_r_2124_, 4);
lean_dec(v_unused_2339_);
v_unused_2340_ = lean_ctor_get(v_r_2124_, 3);
lean_dec(v_unused_2340_);
v_unused_2341_ = lean_ctor_get(v_r_2124_, 2);
lean_dec(v_unused_2341_);
v_unused_2342_ = lean_ctor_get(v_r_2124_, 1);
lean_dec(v_unused_2342_);
v_unused_2343_ = lean_ctor_get(v_r_2124_, 0);
lean_dec(v_unused_2343_);
v___x_2302_ = v_r_2124_;
v_isShared_2303_ = v_isSharedCheck_2338_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v_r_2124_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2338_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___x_2326_; lean_object* v___y_2328_; 
v___x_2304_ = lean_nat_add(v___x_2130_, v_size_2120_);
lean_dec(v_size_2120_);
v___x_2305_ = lean_nat_add(v___x_2304_, v_size_2280_);
lean_dec(v___x_2304_);
v___x_2326_ = lean_nat_add(v___x_2130_, v_size_2292_);
if (lean_obj_tag(v_l_2296_) == 0)
{
lean_object* v_size_2336_; 
v_size_2336_ = lean_ctor_get(v_l_2296_, 0);
lean_inc(v_size_2336_);
v___y_2328_ = v_size_2336_;
goto v___jp_2327_;
}
else
{
lean_object* v___x_2337_; 
v___x_2337_ = lean_unsigned_to_nat(0u);
v___y_2328_ = v___x_2337_;
goto v___jp_2327_;
}
v___jp_2306_:
{
lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2310_ = lean_nat_add(v___y_2307_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec(v___y_2307_);
lean_inc_ref(v_tree_2277_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 4, v_tree_2277_);
lean_ctor_set(v___x_2302_, 3, v_r_2297_);
lean_ctor_set(v___x_2302_, 2, v_v_2279_);
lean_ctor_set(v___x_2302_, 1, v_k_2278_);
lean_ctor_set(v___x_2302_, 0, v___x_2310_);
v___x_2312_ = v___x_2302_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_k_2278_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_v_2279_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_r_2297_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v_tree_2277_);
v___x_2312_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
v_isSharedCheck_2319_ = !lean_is_exclusive(v_tree_2277_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2320_ = lean_ctor_get(v_tree_2277_, 4);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_tree_2277_, 3);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_tree_2277_, 2);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_tree_2277_, 1);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_tree_2277_, 0);
lean_dec(v_unused_2324_);
v___x_2314_ = v_tree_2277_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_dec(v_tree_2277_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 4, v___x_2312_);
lean_ctor_set(v___x_2314_, 3, v___y_2308_);
lean_ctor_set(v___x_2314_, 2, v_v_2295_);
lean_ctor_set(v___x_2314_, 1, v_k_2294_);
lean_ctor_set(v___x_2314_, 0, v___x_2305_);
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_k_2294_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_v_2295_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v___y_2308_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v___x_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
v___jp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_nat_add(v___x_2326_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec(v___x_2326_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_l_2296_);
lean_ctor_set(v___x_2274_, 3, v_l_2123_);
lean_ctor_set(v___x_2274_, 2, v_v_2122_);
lean_ctor_set(v___x_2274_, 1, v_k_2121_);
lean_ctor_set(v___x_2274_, 0, v___x_2329_);
v___x_2331_ = v___x_2274_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2335_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2335_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2335_, 4, v_l_2296_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_nat_add(v___x_2130_, v_size_2280_);
if (lean_obj_tag(v_r_2297_) == 0)
{
lean_object* v_size_2333_; 
v_size_2333_ = lean_ctor_get(v_r_2297_, 0);
lean_inc(v_size_2333_);
v___y_2307_ = v___x_2332_;
v___y_2308_ = v___x_2331_;
v___y_2309_ = v_size_2333_;
goto v___jp_2306_;
}
else
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_unsigned_to_nat(0u);
v___y_2307_ = v___x_2332_;
v___y_2308_ = v___x_2331_;
v___y_2309_ = v___x_2334_;
goto v___jp_2306_;
}
}
}
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2344_ = lean_nat_add(v___x_2130_, v_size_2120_);
lean_dec(v_size_2120_);
v___x_2345_ = lean_nat_add(v___x_2344_, v_size_2280_);
lean_dec(v___x_2344_);
v___x_2346_ = lean_nat_add(v___x_2130_, v_size_2280_);
v___x_2347_ = lean_nat_add(v___x_2346_, v_size_2293_);
lean_dec(v___x_2346_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_tree_2277_);
lean_ctor_set(v___x_2274_, 3, v_r_2124_);
lean_ctor_set(v___x_2274_, 2, v_v_2279_);
lean_ctor_set(v___x_2274_, 1, v_k_2278_);
lean_ctor_set(v___x_2274_, 0, v___x_2347_);
v___x_2349_ = v___x_2274_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_k_2278_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_v_2279_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v_r_2124_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v_tree_2277_);
v___x_2349_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 4, v___x_2349_);
lean_ctor_set(v___x_2290_, 0, v___x_2345_);
v___x_2351_ = v___x_2290_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2352_, 4, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2123_) == 0)
{
lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2383_; 
lean_inc_ref(v_l_2123_);
lean_inc(v_v_2122_);
lean_inc(v_k_2121_);
lean_inc(v_size_2120_);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_l_1949_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; lean_object* v_unused_2385_; lean_object* v_unused_2386_; lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2384_ = lean_ctor_get(v_l_1949_, 4);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_l_1949_, 3);
lean_dec(v_unused_2385_);
v_unused_2386_ = lean_ctor_get(v_l_1949_, 2);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_l_1949_, 1);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_l_1949_, 0);
lean_dec(v_unused_2388_);
v___x_2361_ = v_l_1949_;
v_isShared_2362_ = v_isSharedCheck_2383_;
goto v_resetjp_2360_;
}
else
{
lean_dec(v_l_1949_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2383_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
if (lean_obj_tag(v_r_2124_) == 0)
{
lean_object* v_k_2363_; lean_object* v_v_2364_; lean_object* v_size_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v_k_2363_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_k_2363_);
v_v_2364_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_v_2364_);
lean_dec_ref(v___x_2276_);
v_size_2365_ = lean_ctor_get(v_r_2124_, 0);
v___x_2366_ = lean_nat_add(v___x_2130_, v_size_2120_);
lean_dec(v_size_2120_);
v___x_2367_ = lean_nat_add(v___x_2130_, v_size_2365_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_tree_2277_);
lean_ctor_set(v___x_2274_, 3, v_r_2124_);
lean_ctor_set(v___x_2274_, 2, v_v_2364_);
lean_ctor_set(v___x_2274_, 1, v_k_2363_);
lean_ctor_set(v___x_2274_, 0, v___x_2367_);
v___x_2369_ = v___x_2274_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_k_2363_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v_v_2364_);
lean_ctor_set(v_reuseFailAlloc_2373_, 3, v_r_2124_);
lean_ctor_set(v_reuseFailAlloc_2373_, 4, v_tree_2277_);
v___x_2369_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 4, v___x_2369_);
lean_ctor_set(v___x_2361_, 0, v___x_2366_);
v___x_2371_ = v___x_2361_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2372_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2372_, 4, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
else
{
lean_object* v_k_2374_; lean_object* v_v_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
lean_dec(v_size_2120_);
v_k_2374_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_k_2374_);
v_v_2375_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_v_2375_);
lean_dec_ref(v___x_2276_);
v___x_2376_ = lean_unsigned_to_nat(3u);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_r_2124_);
lean_ctor_set(v___x_2274_, 3, v_r_2124_);
lean_ctor_set(v___x_2274_, 2, v_v_2375_);
lean_ctor_set(v___x_2274_, 1, v_k_2374_);
lean_ctor_set(v___x_2274_, 0, v___x_2130_);
v___x_2378_ = v___x_2274_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_k_2374_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_v_2375_);
lean_ctor_set(v_reuseFailAlloc_2382_, 3, v_r_2124_);
lean_ctor_set(v_reuseFailAlloc_2382_, 4, v_r_2124_);
v___x_2378_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2380_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 4, v___x_2378_);
lean_ctor_set(v___x_2361_, 0, v___x_2376_);
v___x_2380_ = v___x_2361_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2381_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2381_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2381_, 4, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2124_) == 0)
{
lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2413_; 
lean_inc(v_l_2123_);
lean_inc(v_v_2122_);
lean_inc(v_k_2121_);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_l_1949_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2414_ = lean_ctor_get(v_l_1949_, 4);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_l_1949_, 3);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_l_1949_, 2);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_l_1949_, 1);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_l_1949_, 0);
lean_dec(v_unused_2418_);
v___x_2390_ = v_l_1949_;
v_isShared_2391_ = v_isSharedCheck_2413_;
goto v_resetjp_2389_;
}
else
{
lean_dec(v_l_1949_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2413_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v_k_2392_; lean_object* v_v_2393_; lean_object* v_k_2394_; lean_object* v_v_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2409_; 
v_k_2392_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_k_2392_);
v_v_2393_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_v_2393_);
lean_dec_ref(v___x_2276_);
v_k_2394_ = lean_ctor_get(v_r_2124_, 1);
v_v_2395_ = lean_ctor_get(v_r_2124_, 2);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_r_2124_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; lean_object* v_unused_2411_; lean_object* v_unused_2412_; 
v_unused_2410_ = lean_ctor_get(v_r_2124_, 4);
lean_dec(v_unused_2410_);
v_unused_2411_ = lean_ctor_get(v_r_2124_, 3);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_r_2124_, 0);
lean_dec(v_unused_2412_);
v___x_2397_ = v_r_2124_;
v_isShared_2398_ = v_isSharedCheck_2409_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_v_2395_);
lean_inc(v_k_2394_);
lean_dec(v_r_2124_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2409_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2399_ = lean_unsigned_to_nat(3u);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 4, v_l_2123_);
lean_ctor_set(v___x_2397_, 3, v_l_2123_);
lean_ctor_set(v___x_2397_, 2, v_v_2122_);
lean_ctor_set(v___x_2397_, 1, v_k_2121_);
lean_ctor_set(v___x_2397_, 0, v___x_2130_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2408_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2408_, 4, v_l_2123_);
v___x_2401_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_l_2123_);
lean_ctor_set(v___x_2274_, 3, v_l_2123_);
lean_ctor_set(v___x_2274_, 2, v_v_2393_);
lean_ctor_set(v___x_2274_, 1, v_k_2392_);
lean_ctor_set(v___x_2274_, 0, v___x_2130_);
v___x_2403_ = v___x_2274_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_k_2392_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_v_2393_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v_l_2123_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 4, v___x_2403_);
lean_ctor_set(v___x_2390_, 3, v___x_2401_);
lean_ctor_set(v___x_2390_, 2, v_v_2395_);
lean_ctor_set(v___x_2390_, 1, v_k_2394_);
lean_ctor_set(v___x_2390_, 0, v___x_2399_);
v___x_2405_ = v___x_2390_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v_k_2394_);
lean_ctor_set(v_reuseFailAlloc_2406_, 2, v_v_2395_);
lean_ctor_set(v_reuseFailAlloc_2406_, 3, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2406_, 4, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
else
{
lean_object* v_k_2419_; lean_object* v_v_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v_k_2419_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_k_2419_);
v_v_2420_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_v_2420_);
lean_dec_ref(v___x_2276_);
v___x_2421_ = lean_unsigned_to_nat(2u);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v_r_2124_);
lean_ctor_set(v___x_2274_, 3, v_l_1949_);
lean_ctor_set(v___x_2274_, 2, v_v_2420_);
lean_ctor_set(v___x_2274_, 1, v_k_2419_);
lean_ctor_set(v___x_2274_, 0, v___x_2421_);
v___x_2423_ = v___x_2274_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_k_2419_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_v_2420_);
lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_l_1949_);
lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_r_2124_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
}
}
else
{
return v_l_1949_;
}
}
else
{
return v_r_1950_;
}
}
}
else
{
lean_object* v_impl_2431_; lean_object* v___x_2432_; 
v_impl_2431_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1945_, v_l_1949_);
v___x_2432_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2431_) == 0)
{
if (lean_obj_tag(v_r_1950_) == 0)
{
lean_object* v_size_2433_; lean_object* v_size_2434_; lean_object* v_k_2435_; lean_object* v_v_2436_; lean_object* v_l_2437_; lean_object* v_r_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v_size_2433_ = lean_ctor_get(v_impl_2431_, 0);
lean_inc(v_size_2433_);
v_size_2434_ = lean_ctor_get(v_r_1950_, 0);
v_k_2435_ = lean_ctor_get(v_r_1950_, 1);
v_v_2436_ = lean_ctor_get(v_r_1950_, 2);
v_l_2437_ = lean_ctor_get(v_r_1950_, 3);
lean_inc(v_l_2437_);
v_r_2438_ = lean_ctor_get(v_r_1950_, 4);
v___x_2439_ = lean_unsigned_to_nat(3u);
v___x_2440_ = lean_nat_mul(v___x_2439_, v_size_2433_);
v___x_2441_ = lean_nat_dec_lt(v___x_2440_, v_size_2434_);
lean_dec(v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
lean_dec(v_l_2437_);
v___x_2442_ = lean_nat_add(v___x_2432_, v_size_2433_);
lean_dec(v_size_2433_);
v___x_2443_ = lean_nat_add(v___x_2442_, v_size_2434_);
lean_dec(v___x_2442_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 3, v_impl_2431_);
lean_ctor_set(v___x_1952_, 0, v___x_2443_);
v___x_2445_ = v___x_1952_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_impl_2431_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_r_1950_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
else
{
lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2510_; 
lean_inc(v_r_2438_);
lean_inc(v_v_2436_);
lean_inc(v_k_2435_);
lean_inc(v_size_2434_);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; lean_object* v_unused_2512_; lean_object* v_unused_2513_; lean_object* v_unused_2514_; lean_object* v_unused_2515_; 
v_unused_2511_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2511_);
v_unused_2512_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2512_);
v_unused_2513_ = lean_ctor_get(v_r_1950_, 2);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v_r_1950_, 1);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_r_1950_, 0);
lean_dec(v_unused_2515_);
v___x_2448_ = v_r_1950_;
v_isShared_2449_ = v_isSharedCheck_2510_;
goto v_resetjp_2447_;
}
else
{
lean_dec(v_r_1950_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2510_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v_size_2450_; lean_object* v_k_2451_; lean_object* v_v_2452_; lean_object* v_l_2453_; lean_object* v_r_2454_; lean_object* v_size_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_size_2450_ = lean_ctor_get(v_l_2437_, 0);
v_k_2451_ = lean_ctor_get(v_l_2437_, 1);
v_v_2452_ = lean_ctor_get(v_l_2437_, 2);
v_l_2453_ = lean_ctor_get(v_l_2437_, 3);
v_r_2454_ = lean_ctor_get(v_l_2437_, 4);
v_size_2455_ = lean_ctor_get(v_r_2438_, 0);
v___x_2456_ = lean_unsigned_to_nat(2u);
v___x_2457_ = lean_nat_mul(v___x_2456_, v_size_2455_);
v___x_2458_ = lean_nat_dec_lt(v_size_2450_, v___x_2457_);
lean_dec(v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2486_; 
lean_inc(v_r_2454_);
lean_inc(v_l_2453_);
lean_inc(v_v_2452_);
lean_inc(v_k_2451_);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_l_2437_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; lean_object* v_unused_2488_; lean_object* v_unused_2489_; lean_object* v_unused_2490_; lean_object* v_unused_2491_; 
v_unused_2487_ = lean_ctor_get(v_l_2437_, 4);
lean_dec(v_unused_2487_);
v_unused_2488_ = lean_ctor_get(v_l_2437_, 3);
lean_dec(v_unused_2488_);
v_unused_2489_ = lean_ctor_get(v_l_2437_, 2);
lean_dec(v_unused_2489_);
v_unused_2490_ = lean_ctor_get(v_l_2437_, 1);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_l_2437_, 0);
lean_dec(v_unused_2491_);
v___x_2460_ = v_l_2437_;
v_isShared_2461_ = v_isSharedCheck_2486_;
goto v_resetjp_2459_;
}
else
{
lean_dec(v_l_2437_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2486_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2476_; 
v___x_2462_ = lean_nat_add(v___x_2432_, v_size_2433_);
lean_dec(v_size_2433_);
v___x_2463_ = lean_nat_add(v___x_2462_, v_size_2434_);
lean_dec(v_size_2434_);
if (lean_obj_tag(v_l_2453_) == 0)
{
lean_object* v_size_2484_; 
v_size_2484_ = lean_ctor_get(v_l_2453_, 0);
lean_inc(v_size_2484_);
v___y_2476_ = v_size_2484_;
goto v___jp_2475_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_unsigned_to_nat(0u);
v___y_2476_ = v___x_2485_;
goto v___jp_2475_;
}
v___jp_2464_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = lean_nat_add(v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec(v___y_2466_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 4, v_r_2438_);
lean_ctor_set(v___x_2460_, 3, v_r_2454_);
lean_ctor_set(v___x_2460_, 2, v_v_2436_);
lean_ctor_set(v___x_2460_, 1, v_k_2435_);
lean_ctor_set(v___x_2460_, 0, v___x_2468_);
v___x_2470_ = v___x_2460_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_k_2435_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_v_2436_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_r_2454_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_r_2438_);
v___x_2470_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2472_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 4, v___x_2470_);
lean_ctor_set(v___x_2448_, 3, v___y_2465_);
lean_ctor_set(v___x_2448_, 2, v_v_2452_);
lean_ctor_set(v___x_2448_, 1, v_k_2451_);
lean_ctor_set(v___x_2448_, 0, v___x_2463_);
v___x_2472_ = v___x_2448_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_k_2451_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_v_2452_);
lean_ctor_set(v_reuseFailAlloc_2473_, 3, v___y_2465_);
lean_ctor_set(v_reuseFailAlloc_2473_, 4, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
v___jp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2477_ = lean_nat_add(v___x_2462_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec(v___x_2462_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v_l_2453_);
lean_ctor_set(v___x_1952_, 3, v_impl_2431_);
lean_ctor_set(v___x_1952_, 0, v___x_2477_);
v___x_2479_ = v___x_1952_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_impl_2431_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_l_2453_);
v___x_2479_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_nat_add(v___x_2432_, v_size_2455_);
if (lean_obj_tag(v_r_2454_) == 0)
{
lean_object* v_size_2481_; 
v_size_2481_ = lean_ctor_get(v_r_2454_, 0);
lean_inc(v_size_2481_);
v___y_2465_ = v___x_2479_;
v___y_2466_ = v___x_2480_;
v___y_2467_ = v_size_2481_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_unsigned_to_nat(0u);
v___y_2465_ = v___x_2479_;
v___y_2466_ = v___x_2480_;
v___y_2467_ = v___x_2482_;
goto v___jp_2464_;
}
}
}
}
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_del_object(v___x_1952_);
v___x_2492_ = lean_nat_add(v___x_2432_, v_size_2433_);
lean_dec(v_size_2433_);
v___x_2493_ = lean_nat_add(v___x_2492_, v_size_2434_);
lean_dec(v_size_2434_);
v___x_2494_ = lean_nat_add(v___x_2492_, v_size_2450_);
lean_dec(v___x_2492_);
lean_inc_ref(v_impl_2431_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 4, v_l_2437_);
lean_ctor_set(v___x_2448_, 3, v_impl_2431_);
lean_ctor_set(v___x_2448_, 2, v_v_1948_);
lean_ctor_set(v___x_2448_, 1, v_k_1947_);
lean_ctor_set(v___x_2448_, 0, v___x_2494_);
v___x_2496_ = v___x_2448_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_impl_2431_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_l_2437_);
v___x_2496_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
v_isSharedCheck_2503_ = !lean_is_exclusive(v_impl_2431_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; lean_object* v_unused_2505_; lean_object* v_unused_2506_; lean_object* v_unused_2507_; lean_object* v_unused_2508_; 
v_unused_2504_ = lean_ctor_get(v_impl_2431_, 4);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_impl_2431_, 3);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_impl_2431_, 2);
lean_dec(v_unused_2506_);
v_unused_2507_ = lean_ctor_get(v_impl_2431_, 1);
lean_dec(v_unused_2507_);
v_unused_2508_ = lean_ctor_get(v_impl_2431_, 0);
lean_dec(v_unused_2508_);
v___x_2498_ = v_impl_2431_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_dec(v_impl_2431_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 4, v_r_2438_);
lean_ctor_set(v___x_2498_, 3, v___x_2496_);
lean_ctor_set(v___x_2498_, 2, v_v_2436_);
lean_ctor_set(v___x_2498_, 1, v_k_2435_);
lean_ctor_set(v___x_2498_, 0, v___x_2493_);
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_k_2435_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_v_2436_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_r_2438_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v_size_2516_ = lean_ctor_get(v_impl_2431_, 0);
lean_inc(v_size_2516_);
v___x_2517_ = lean_nat_add(v___x_2432_, v_size_2516_);
lean_dec(v_size_2516_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 3, v_impl_2431_);
lean_ctor_set(v___x_1952_, 0, v___x_2517_);
v___x_2519_ = v___x_1952_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2520_, 3, v_impl_2431_);
lean_ctor_set(v_reuseFailAlloc_2520_, 4, v_r_1950_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
if (lean_obj_tag(v_r_1950_) == 0)
{
lean_object* v_l_2521_; 
v_l_2521_ = lean_ctor_get(v_r_1950_, 3);
lean_inc(v_l_2521_);
if (lean_obj_tag(v_l_2521_) == 0)
{
lean_object* v_r_2522_; 
v_r_2522_ = lean_ctor_get(v_r_1950_, 4);
lean_inc(v_r_2522_);
if (lean_obj_tag(v_r_2522_) == 0)
{
lean_object* v_size_2523_; lean_object* v_k_2524_; lean_object* v_v_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2538_; 
v_size_2523_ = lean_ctor_get(v_r_1950_, 0);
v_k_2524_ = lean_ctor_get(v_r_1950_, 1);
v_v_2525_ = lean_ctor_get(v_r_1950_, 2);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2539_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2540_);
v___x_2527_ = v_r_1950_;
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_v_2525_);
lean_inc(v_k_2524_);
lean_inc(v_size_2523_);
lean_dec(v_r_1950_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_size_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v_size_2529_ = lean_ctor_get(v_l_2521_, 0);
v___x_2530_ = lean_nat_add(v___x_2432_, v_size_2523_);
lean_dec(v_size_2523_);
v___x_2531_ = lean_nat_add(v___x_2432_, v_size_2529_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 4, v_l_2521_);
lean_ctor_set(v___x_2527_, 3, v_impl_2431_);
lean_ctor_set(v___x_2527_, 2, v_v_1948_);
lean_ctor_set(v___x_2527_, 1, v_k_1947_);
lean_ctor_set(v___x_2527_, 0, v___x_2531_);
v___x_2533_ = v___x_2527_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_impl_2431_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v_l_2521_);
v___x_2533_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2535_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v_r_2522_);
lean_ctor_set(v___x_1952_, 3, v___x_2533_);
lean_ctor_set(v___x_1952_, 2, v_v_2525_);
lean_ctor_set(v___x_1952_, 1, v_k_2524_);
lean_ctor_set(v___x_1952_, 0, v___x_2530_);
v___x_2535_ = v___x_1952_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_k_2524_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_v_2525_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_r_2522_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_k_2541_; lean_object* v_v_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2565_; 
v_k_2541_ = lean_ctor_get(v_r_1950_, 1);
v_v_2542_ = lean_ctor_get(v_r_1950_, 2);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; lean_object* v_unused_2567_; lean_object* v_unused_2568_; 
v_unused_2566_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2567_);
v_unused_2568_ = lean_ctor_get(v_r_1950_, 0);
lean_dec(v_unused_2568_);
v___x_2544_ = v_r_1950_;
v_isShared_2545_ = v_isSharedCheck_2565_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_v_2542_);
lean_inc(v_k_2541_);
lean_dec(v_r_1950_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2565_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v_k_2546_; lean_object* v_v_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2561_; 
v_k_2546_ = lean_ctor_get(v_l_2521_, 1);
v_v_2547_ = lean_ctor_get(v_l_2521_, 2);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_l_2521_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; lean_object* v_unused_2563_; lean_object* v_unused_2564_; 
v_unused_2562_ = lean_ctor_get(v_l_2521_, 4);
lean_dec(v_unused_2562_);
v_unused_2563_ = lean_ctor_get(v_l_2521_, 3);
lean_dec(v_unused_2563_);
v_unused_2564_ = lean_ctor_get(v_l_2521_, 0);
lean_dec(v_unused_2564_);
v___x_2549_ = v_l_2521_;
v_isShared_2550_ = v_isSharedCheck_2561_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_v_2547_);
lean_inc(v_k_2546_);
lean_dec(v_l_2521_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2561_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_unsigned_to_nat(3u);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 4, v_r_2522_);
lean_ctor_set(v___x_2549_, 3, v_r_2522_);
lean_ctor_set(v___x_2549_, 2, v_v_1948_);
lean_ctor_set(v___x_2549_, 1, v_k_1947_);
lean_ctor_set(v___x_2549_, 0, v___x_2432_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v_r_2522_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v_r_2522_);
v___x_2553_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2555_; 
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 3, v_r_2522_);
lean_ctor_set(v___x_2544_, 0, v___x_2432_);
v___x_2555_ = v___x_2544_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_k_2541_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_v_2542_);
lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_r_2522_);
lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_r_2522_);
v___x_2555_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v___x_2555_);
lean_ctor_set(v___x_1952_, 3, v___x_2553_);
lean_ctor_set(v___x_1952_, 2, v_v_2547_);
lean_ctor_set(v___x_1952_, 1, v_k_2546_);
lean_ctor_set(v___x_1952_, 0, v___x_2551_);
v___x_2557_ = v___x_1952_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_k_2546_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_v_2547_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2569_; 
v_r_2569_ = lean_ctor_get(v_r_1950_, 4);
lean_inc(v_r_2569_);
if (lean_obj_tag(v_r_2569_) == 0)
{
lean_object* v_k_2570_; lean_object* v_v_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2582_; 
v_k_2570_ = lean_ctor_get(v_r_1950_, 1);
v_v_2571_ = lean_ctor_get(v_r_1950_, 2);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; 
v_unused_2583_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_r_1950_, 0);
lean_dec(v_unused_2585_);
v___x_2573_ = v_r_1950_;
v_isShared_2574_ = v_isSharedCheck_2582_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_v_2571_);
lean_inc(v_k_2570_);
lean_dec(v_r_1950_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2582_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_unsigned_to_nat(3u);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 4, v_l_2521_);
lean_ctor_set(v___x_2573_, 2, v_v_1948_);
lean_ctor_set(v___x_2573_, 1, v_k_1947_);
lean_ctor_set(v___x_2573_, 0, v___x_2432_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_l_2521_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_l_2521_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v_r_2569_);
lean_ctor_set(v___x_1952_, 3, v___x_2577_);
lean_ctor_set(v___x_1952_, 2, v_v_2571_);
lean_ctor_set(v___x_1952_, 1, v_k_2570_);
lean_ctor_set(v___x_1952_, 0, v___x_2575_);
v___x_2579_ = v___x_1952_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_k_2570_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_v_2571_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v_r_2569_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_size_2586_; lean_object* v_k_2587_; lean_object* v_v_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2599_; 
v_size_2586_ = lean_ctor_get(v_r_1950_, 0);
v_k_2587_ = lean_ctor_get(v_r_1950_, 1);
v_v_2588_ = lean_ctor_get(v_r_1950_, 2);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_r_1950_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; lean_object* v_unused_2601_; 
v_unused_2600_ = lean_ctor_get(v_r_1950_, 4);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v_r_1950_, 3);
lean_dec(v_unused_2601_);
v___x_2590_ = v_r_1950_;
v_isShared_2591_ = v_isSharedCheck_2599_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_v_2588_);
lean_inc(v_k_2587_);
lean_inc(v_size_2586_);
lean_dec(v_r_1950_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2599_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 3, v_r_2569_);
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_size_2586_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_k_2587_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_v_2588_);
lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_r_2569_);
lean_ctor_set(v_reuseFailAlloc_2598_, 4, v_r_2569_);
v___x_2593_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_unsigned_to_nat(2u);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 4, v___x_2593_);
lean_ctor_set(v___x_1952_, 3, v_r_2569_);
lean_ctor_set(v___x_1952_, 0, v___x_2594_);
v___x_2596_ = v___x_1952_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_r_2569_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v___x_2593_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
else
{
lean_object* v___x_2603_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 3, v_r_1950_);
lean_ctor_set(v___x_1952_, 0, v___x_2432_);
v___x_2603_ = v___x_1952_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_k_1947_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_v_1948_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_r_1950_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_r_1950_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
else
{
return v_t_1946_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2607_, lean_object* v_t_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2607_, v_t_2608_);
lean_dec(v_k_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object* v_id_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; lean_object* v_receivers_2619_; lean_object* v___x_2620_; 
v___x_2618_ = lean_st_ref_get(v___y_2616_);
v_receivers_2619_ = lean_ctor_get(v___x_2618_, 7);
lean_inc(v_receivers_2619_);
v___x_2620_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2619_, v_id_2615_);
lean_dec(v_receivers_2619_);
if (lean_obj_tag(v___x_2620_) == 1)
{
lean_object* v_val_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_val_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_val_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2618_);
lean_ctor_set(v___x_2622_, 1, v_val_2621_);
v___x_2623_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2622_, v___y_2616_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2653_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2653_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2653_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_fst_2628_; lean_object* v_producers_2629_; lean_object* v_waiters_2630_; lean_object* v_capacity_2631_; lean_object* v_size_2632_; lean_object* v_buffer_2633_; lean_object* v_write_2634_; lean_object* v_read_2635_; lean_object* v_receivers_2636_; lean_object* v_nextId_2637_; uint8_t v_closed_2638_; lean_object* v_pos_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2652_; 
v_fst_2628_ = lean_ctor_get(v_a_2624_, 0);
lean_inc(v_fst_2628_);
lean_dec(v_a_2624_);
v_producers_2629_ = lean_ctor_get(v_fst_2628_, 0);
v_waiters_2630_ = lean_ctor_get(v_fst_2628_, 1);
v_capacity_2631_ = lean_ctor_get(v_fst_2628_, 2);
v_size_2632_ = lean_ctor_get(v_fst_2628_, 3);
v_buffer_2633_ = lean_ctor_get(v_fst_2628_, 4);
v_write_2634_ = lean_ctor_get(v_fst_2628_, 5);
v_read_2635_ = lean_ctor_get(v_fst_2628_, 6);
v_receivers_2636_ = lean_ctor_get(v_fst_2628_, 7);
v_nextId_2637_ = lean_ctor_get(v_fst_2628_, 8);
v_closed_2638_ = lean_ctor_get_uint8(v_fst_2628_, sizeof(void*)*10);
v_pos_2639_ = lean_ctor_get(v_fst_2628_, 9);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_fst_2628_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2641_ = v_fst_2628_;
v_isShared_2642_ = v_isSharedCheck_2652_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_pos_2639_);
lean_inc(v_nextId_2637_);
lean_inc(v_receivers_2636_);
lean_inc(v_read_2635_);
lean_inc(v_write_2634_);
lean_inc(v_buffer_2633_);
lean_inc(v_size_2632_);
lean_inc(v_capacity_2631_);
lean_inc(v_waiters_2630_);
lean_inc(v_producers_2629_);
lean_dec(v_fst_2628_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2652_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_id_2615_, v_receivers_2636_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 7, v___x_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_producers_2629_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_waiters_2630_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v_capacity_2631_);
lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_size_2632_);
lean_ctor_set(v_reuseFailAlloc_2651_, 4, v_buffer_2633_);
lean_ctor_set(v_reuseFailAlloc_2651_, 5, v_write_2634_);
lean_ctor_set(v_reuseFailAlloc_2651_, 6, v_read_2635_);
lean_ctor_set(v_reuseFailAlloc_2651_, 7, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2651_, 8, v_nextId_2637_);
lean_ctor_set(v_reuseFailAlloc_2651_, 9, v_pos_2639_);
lean_ctor_set_uint8(v_reuseFailAlloc_2651_, sizeof(void*)*10, v_closed_2638_);
v___x_2645_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2649_; 
v___x_2646_ = lean_st_ref_swap(v___y_2616_, v___x_2645_);
lean_dec(v___x_2646_);
v___x_2647_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0));
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2647_);
v___x_2649_ = v___x_2626_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2623_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2623_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec(v___x_2620_);
lean_dec(v___x_2618_);
v___x_2662_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1));
v___x_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object* v_id_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec(v_id_2664_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object* v_bd_2668_){
_start:
{
lean_object* v_state_2670_; lean_object* v_id_2671_; lean_object* v___f_2672_; lean_object* v___x_2673_; 
v_state_2670_ = lean_ctor_get(v_bd_2668_, 0);
lean_inc_ref(v_state_2670_);
v_id_2671_ = lean_ctor_get(v_bd_2668_, 1);
lean_inc(v_id_2671_);
lean_dec_ref(v_bd_2668_);
v___f_2672_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2672_, 0, v_id_2671_);
v___x_2673_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_2670_, v___f_2672_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2698_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2698_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2698_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___y_2679_; 
if (lean_obj_tag(v_a_2674_) == 0)
{
lean_object* v_a_2684_; uint8_t v___x_2685_; 
v_a_2684_ = lean_ctor_get(v_a_2674_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v_a_2674_, 1);
v___x_2685_ = lean_unbox(v_a_2684_);
lean_dec(v_a_2684_);
switch(v___x_2685_)
{
case 0:
{
lean_object* v___x_2686_; 
v___x_2686_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_2679_ = v___x_2686_;
goto v___jp_2678_;
}
case 1:
{
lean_object* v___x_2687_; 
v___x_2687_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_2679_ = v___x_2687_;
goto v___jp_2678_;
}
default: 
{
lean_object* v___x_2688_; 
v___x_2688_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_2679_ = v___x_2688_;
goto v___jp_2678_;
}
}
}
else
{
lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2696_; 
lean_del_object(v___x_2676_);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_a_2674_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v_a_2674_, 0);
lean_dec(v_unused_2697_);
v___x_2690_ = v_a_2674_;
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
else
{
lean_dec(v_a_2674_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2696_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = lean_box(0);
if (v_isShared_2691_ == 0)
{
lean_ctor_set_tag(v___x_2690_, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
v___jp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_inc_ref(v___y_2679_);
v___x_2680_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___y_2679_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set_tag(v___x_2676_, 1);
lean_ctor_set(v___x_2676_, 0, v___x_2680_);
v___x_2682_ = v___x_2676_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
v_a_2699_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2673_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2673_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object* v_bd_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object* v_00_u03b1_2710_, lean_object* v_bd_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_bd_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(v_00_u03b1_2714_, v_bd_2715_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object* v_00_u03b1_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_a_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(v_00_u03b1_2722_, v_a_2723_);
lean_dec(v_a_2723_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object* v_00_u03b1_2726_, lean_object* v_place_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2727_, v_a_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2731_, lean_object* v_place_2732_, lean_object* v_a_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(v_00_u03b1_2731_, v_place_2732_, v_a_2733_);
lean_dec(v_a_2733_);
lean_dec(v_place_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object* v_00_u03b1_2736_, lean_object* v_slot_2737_, lean_object* v_next_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2737_, v_next_2738_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_slot_2743_, lean_object* v_next_2744_, lean_object* v_a_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(v_00_u03b1_2742_, v_slot_2743_, v_next_2744_, v_a_2745_);
lean_dec(v_a_2745_);
lean_dec(v_next_2744_);
lean_dec(v_slot_2743_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object* v_00_u03b1_2748_, lean_object* v_next_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2749_, v_a_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object* v_00_u03b1_2753_, lean_object* v_next_2754_, lean_object* v_a_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(v_00_u03b1_2753_, v_next_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec(v_next_2754_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object* v_00_u03b4_2758_, lean_object* v_t_2759_, lean_object* v_k_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2759_, v_k_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object* v_00_u03b4_2762_, lean_object* v_t_2763_, lean_object* v_k_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(v_00_u03b4_2762_, v_t_2763_, v_k_2764_);
lean_dec(v_k_2764_);
lean_dec(v_t_2763_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2766_, lean_object* v_inst_2767_, lean_object* v_a_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_2768_, v___y_2769_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2772_, lean_object* v_inst_2773_, lean_object* v_a_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2772_, v_inst_2773_, v_a_2774_, v___y_2775_);
lean_dec(v___y_2775_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2778_, lean_object* v_k_2779_, lean_object* v_t_2780_, lean_object* v_h_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2779_, v_t_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2783_, lean_object* v_k_2784_, lean_object* v_t_2785_, lean_object* v_h_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2783_, v_k_2784_, v_t_2785_, v_h_2786_);
lean_dec(v_k_2784_);
return v_res_2787_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2788_, lean_object* v_y_2789_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_nat_dec_lt(v_x_2788_, v_y_2789_);
if (v___x_2790_ == 0)
{
uint8_t v___x_2791_; 
v___x_2791_ = lean_nat_dec_eq(v_x_2788_, v_y_2789_);
if (v___x_2791_ == 0)
{
uint8_t v___x_2792_; 
v___x_2792_ = 2;
return v___x_2792_;
}
else
{
uint8_t v___x_2793_; 
v___x_2793_ = 1;
return v___x_2793_;
}
}
else
{
uint8_t v___x_2794_; 
v___x_2794_ = 0;
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2795_, lean_object* v_y_2796_){
_start:
{
uint8_t v_res_2797_; lean_object* v_r_2798_; 
v_res_2797_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2795_, v_y_2796_);
lean_dec(v_y_2796_);
lean_dec(v_x_2795_);
v_r_2798_ = lean_box(v_res_2797_);
return v_r_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_unsigned_to_nat(1u);
v___x_2801_ = lean_nat_add(v_x_2799_, v___x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2802_);
lean_dec(v_x_2802_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2804_, lean_object* v_receiverId_2805_, lean_object* v___f_2806_, lean_object* v_receivers_2807_, lean_object* v_s_2808_){
_start:
{
lean_object* v_producers_2809_; lean_object* v_waiters_2810_; lean_object* v_capacity_2811_; lean_object* v_size_2812_; lean_object* v_buffer_2813_; lean_object* v_write_2814_; lean_object* v_read_2815_; lean_object* v_nextId_2816_; uint8_t v_closed_2817_; lean_object* v_pos_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2828_; 
v_producers_2809_ = lean_ctor_get(v_s_2808_, 0);
v_waiters_2810_ = lean_ctor_get(v_s_2808_, 1);
v_capacity_2811_ = lean_ctor_get(v_s_2808_, 2);
v_size_2812_ = lean_ctor_get(v_s_2808_, 3);
v_buffer_2813_ = lean_ctor_get(v_s_2808_, 4);
v_write_2814_ = lean_ctor_get(v_s_2808_, 5);
v_read_2815_ = lean_ctor_get(v_s_2808_, 6);
v_nextId_2816_ = lean_ctor_get(v_s_2808_, 8);
v_closed_2817_ = lean_ctor_get_uint8(v_s_2808_, sizeof(void*)*10);
v_pos_2818_ = lean_ctor_get(v_s_2808_, 9);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_s_2808_);
if (v_isSharedCheck_2828_ == 0)
{
lean_object* v_unused_2829_; 
v_unused_2829_ = lean_ctor_get(v_s_2808_, 7);
lean_dec(v_unused_2829_);
v___x_2820_ = v_s_2808_;
v_isShared_2821_ = v_isSharedCheck_2828_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_pos_2818_);
lean_inc(v_nextId_2816_);
lean_inc(v_read_2815_);
lean_inc(v_write_2814_);
lean_inc(v_buffer_2813_);
lean_inc(v_size_2812_);
lean_inc(v_capacity_2811_);
lean_inc(v_waiters_2810_);
lean_inc(v_producers_2809_);
lean_dec(v_s_2808_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2828_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2822_ = lean_box(0);
v___x_2823_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2804_, v_receiverId_2805_, v___f_2806_, v_receivers_2807_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 7, v___x_2823_);
v___x_2825_ = v___x_2820_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_producers_2809_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_waiters_2810_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_capacity_2811_);
lean_ctor_set(v_reuseFailAlloc_2827_, 3, v_size_2812_);
lean_ctor_set(v_reuseFailAlloc_2827_, 4, v_buffer_2813_);
lean_ctor_set(v_reuseFailAlloc_2827_, 5, v_write_2814_);
lean_ctor_set(v_reuseFailAlloc_2827_, 6, v_read_2815_);
lean_ctor_set(v_reuseFailAlloc_2827_, 7, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2827_, 8, v_nextId_2816_);
lean_ctor_set(v_reuseFailAlloc_2827_, 9, v_pos_2818_);
lean_ctor_set_uint8(v_reuseFailAlloc_2827_, sizeof(void*)*10, v_closed_2817_);
v___x_2825_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2822_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
return v___x_2826_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_toPure_2833_; lean_object* v___x_2834_; 
v_toPure_2833_ = lean_ctor_get(v_toApplicative_2830_, 1);
lean_inc(v_toPure_2833_);
lean_dec_ref(v_toApplicative_2830_);
v___x_2834_ = lean_apply_2(v_toPure_2833_, lean_box(0), v_a_2831_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2835_, lean_object* v_a_2836_, lean_object* v___f_2837_, lean_object* v_inst_2838_, lean_object* v_toBind_2839_, lean_object* v_a_2840_){
_start:
{
if (lean_obj_tag(v_a_2840_) == 1)
{
lean_object* v___f_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___f_2841_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2841_, 0, v_toApplicative_2835_);
lean_closure_set(v___f_2841_, 1, v_a_2840_);
lean_inc(v_a_2836_);
v___x_2842_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2842_, 0, lean_box(0));
lean_closure_set(v___x_2842_, 1, lean_box(0));
lean_closure_set(v___x_2842_, 2, lean_box(0));
lean_closure_set(v___x_2842_, 3, v_a_2836_);
lean_closure_set(v___x_2842_, 4, v___f_2837_);
v___x_2843_ = lean_apply_2(v_inst_2838_, lean_box(0), v___x_2842_);
v___x_2844_ = lean_apply_4(v_toBind_2839_, lean_box(0), lean_box(0), v___x_2843_, v___f_2841_);
return v___x_2844_;
}
else
{
lean_object* v_toPure_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec(v_a_2840_);
lean_dec(v_toBind_2839_);
lean_dec(v_inst_2838_);
lean_dec_ref(v___f_2837_);
v_toPure_2845_ = lean_ctor_get(v_toApplicative_2835_, 1);
lean_inc(v_toPure_2845_);
lean_dec_ref(v_toApplicative_2835_);
v___x_2846_ = lean_box(0);
v___x_2847_ = lean_apply_2(v_toPure_2845_, lean_box(0), v___x_2846_);
return v___x_2847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_2848_, lean_object* v_a_2849_, lean_object* v___f_2850_, lean_object* v_inst_2851_, lean_object* v_toBind_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(v_toApplicative_2848_, v_a_2849_, v___f_2850_, v_inst_2851_, v_toBind_2852_, v_a_2853_);
lean_dec(v_a_2849_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2855_, lean_object* v_receiverId_2856_, lean_object* v___f_2857_, lean_object* v___f_2858_, lean_object* v_toApplicative_2859_, lean_object* v_a_2860_, lean_object* v_inst_2861_, lean_object* v_toBind_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_receivers_2866_; lean_object* v___x_2867_; 
v_receivers_2866_ = lean_ctor_get(v_a_2865_, 7);
lean_inc_n(v_receivers_2866_, 2);
lean_dec_ref(v_a_2865_);
lean_inc(v_receiverId_2856_);
v___x_2867_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2855_, v_receivers_2866_, v_receiverId_2856_);
if (lean_obj_tag(v___x_2867_) == 1)
{
lean_object* v_val_2868_; lean_object* v___f_2869_; lean_object* v___f_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_val_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_val_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___f_2869_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2869_, 0, v___f_2857_);
lean_closure_set(v___f_2869_, 1, v_receiverId_2856_);
lean_closure_set(v___f_2869_, 2, v___f_2858_);
lean_closure_set(v___f_2869_, 3, v_receivers_2866_);
lean_inc(v_toBind_2862_);
lean_inc(v_inst_2861_);
lean_inc(v_a_2860_);
v___f_2870_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2870_, 0, v_toApplicative_2859_);
lean_closure_set(v___f_2870_, 1, v_a_2860_);
lean_closure_set(v___f_2870_, 2, v___f_2869_);
lean_closure_set(v___f_2870_, 3, v_inst_2861_);
lean_closure_set(v___f_2870_, 4, v_toBind_2862_);
v___x_2871_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2863_, v_inst_2861_, v_inst_2864_, v_val_2868_, v_a_2860_);
v___x_2872_ = lean_apply_4(v_toBind_2862_, lean_box(0), lean_box(0), v___x_2871_, v___f_2870_);
return v___x_2872_;
}
else
{
lean_object* v_toPure_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
lean_dec(v___x_2867_);
lean_dec(v_receivers_2866_);
lean_dec(v_inst_2864_);
lean_dec_ref(v_inst_2863_);
lean_dec(v_toBind_2862_);
lean_dec(v_inst_2861_);
lean_dec_ref(v___f_2858_);
lean_dec_ref(v___f_2857_);
lean_dec(v_receiverId_2856_);
v_toPure_2873_ = lean_ctor_get(v_toApplicative_2859_, 1);
lean_inc(v_toPure_2873_);
lean_dec_ref(v_toApplicative_2859_);
v___x_2874_ = lean_box(0);
v___x_2875_ = lean_apply_2(v_toPure_2873_, lean_box(0), v___x_2874_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object* v___f_2876_, lean_object* v_receiverId_2877_, lean_object* v___f_2878_, lean_object* v___f_2879_, lean_object* v_toApplicative_2880_, lean_object* v_a_2881_, lean_object* v_inst_2882_, lean_object* v_toBind_2883_, lean_object* v_inst_2884_, lean_object* v_inst_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(v___f_2876_, v_receiverId_2877_, v___f_2878_, v___f_2879_, v_toApplicative_2880_, v_a_2881_, v_inst_2882_, v_toBind_2883_, v_inst_2884_, v_inst_2885_, v_a_2886_);
lean_dec(v_a_2881_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_receiverId_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_toApplicative_2895_; lean_object* v_toBind_2896_; lean_object* v___f_2897_; lean_object* v___f_2898_; lean_object* v___f_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_toApplicative_2895_ = lean_ctor_get(v_inst_2890_, 0);
lean_inc_ref(v_toApplicative_2895_);
v_toBind_2896_ = lean_ctor_get(v_inst_2890_, 1);
lean_inc_n(v_toBind_2896_, 2);
v___f_2897_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_2898_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_inst_2891_);
lean_inc_n(v_a_2894_, 2);
v___f_2899_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_2899_, 0, v___f_2897_);
lean_closure_set(v___f_2899_, 1, v_receiverId_2893_);
lean_closure_set(v___f_2899_, 2, v___f_2897_);
lean_closure_set(v___f_2899_, 3, v___f_2898_);
lean_closure_set(v___f_2899_, 4, v_toApplicative_2895_);
lean_closure_set(v___f_2899_, 5, v_a_2894_);
lean_closure_set(v___f_2899_, 6, v_inst_2891_);
lean_closure_set(v___f_2899_, 7, v_toBind_2896_);
lean_closure_set(v___f_2899_, 8, v_inst_2890_);
lean_closure_set(v___f_2899_, 9, v_inst_2892_);
v___x_2900_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2900_, 0, lean_box(0));
lean_closure_set(v___x_2900_, 1, lean_box(0));
lean_closure_set(v___x_2900_, 2, v_a_2894_);
v___x_2901_ = lean_apply_2(v_inst_2891_, lean_box(0), v___x_2900_);
v___x_2902_ = lean_apply_4(v_toBind_2896_, lean_box(0), lean_box(0), v___x_2901_, v___f_2899_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_receiverId_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2903_, v_inst_2904_, v_inst_2905_, v_receiverId_2906_, v_a_2907_);
lean_dec(v_a_2907_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_2909_, lean_object* v_00_u03b1_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_receiverId_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2911_, v_inst_2912_, v_inst_2913_, v_receiverId_2914_, v_a_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object* v_m_2917_, lean_object* v_00_u03b1_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_receiverId_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(v_m_2917_, v_00_u03b1_2918_, v_inst_2919_, v_inst_2920_, v_inst_2921_, v_receiverId_2922_, v_a_2923_);
lean_dec(v_a_2923_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_2925_, lean_object* v_t_2926_){
_start:
{
if (lean_obj_tag(v_t_2926_) == 0)
{
lean_object* v_size_2927_; lean_object* v_k_2928_; lean_object* v_v_2929_; lean_object* v_l_2930_; lean_object* v_r_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2950_; 
v_size_2927_ = lean_ctor_get(v_t_2926_, 0);
v_k_2928_ = lean_ctor_get(v_t_2926_, 1);
v_v_2929_ = lean_ctor_get(v_t_2926_, 2);
v_l_2930_ = lean_ctor_get(v_t_2926_, 3);
v_r_2931_ = lean_ctor_get(v_t_2926_, 4);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_t_2926_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2933_ = v_t_2926_;
v_isShared_2934_ = v_isSharedCheck_2950_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_r_2931_);
lean_inc(v_l_2930_);
lean_inc(v_v_2929_);
lean_inc(v_k_2928_);
lean_inc(v_size_2927_);
lean_dec(v_t_2926_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2950_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
uint8_t v___x_2935_; 
v___x_2935_ = lean_nat_dec_lt(v_k_2925_, v_k_2928_);
if (v___x_2935_ == 0)
{
uint8_t v___x_2936_; 
v___x_2936_ = lean_nat_dec_eq(v_k_2925_, v_k_2928_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2925_, v_r_2931_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 4, v___x_2937_);
v___x_2939_ = v___x_2933_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_size_2927_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_l_2930_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
else
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2944_; 
lean_dec(v_k_2928_);
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = lean_nat_add(v_v_2929_, v___x_2941_);
lean_dec(v_v_2929_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 2, v___x_2942_);
lean_ctor_set(v___x_2933_, 1, v_k_2925_);
v___x_2944_ = v___x_2933_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_size_2927_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_k_2925_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_l_2930_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_r_2931_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2946_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2925_, v_l_2930_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 3, v___x_2946_);
v___x_2948_ = v___x_2933_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_size_2927_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_2949_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_2949_, 3, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2949_, 4, v_r_2931_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_dec(v_k_2925_);
return v_t_2926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_2951_, lean_object* v_next_2952_){
_start:
{
lean_object* v___x_2954_; lean_object* v_fst_2956_; lean_object* v_snd_2957_; lean_object* v_value_2959_; lean_object* v_pos_2960_; lean_object* v_remaining_2961_; uint8_t v___x_2962_; 
v___x_2954_ = lean_st_ref_take(v_slot_2951_);
v_value_2959_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_value_2959_);
v_pos_2960_ = lean_ctor_get(v___x_2954_, 1);
lean_inc(v_pos_2960_);
v_remaining_2961_ = lean_ctor_get(v___x_2954_, 2);
lean_inc(v_remaining_2961_);
v___x_2962_ = lean_nat_dec_eq(v_next_2952_, v_pos_2960_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v_remaining_2961_);
lean_dec(v_pos_2960_);
lean_dec(v_value_2959_);
v___x_2963_ = lean_box(0);
v___x_2964_ = lean_box(v___x_2962_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
v_fst_2956_ = v___x_2965_;
v_snd_2957_ = v___x_2954_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2984_; 
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; lean_object* v_unused_2986_; lean_object* v_unused_2987_; 
v_unused_2985_ = lean_ctor_get(v___x_2954_, 2);
lean_dec(v_unused_2985_);
v_unused_2986_ = lean_ctor_get(v___x_2954_, 1);
lean_dec(v_unused_2986_);
v_unused_2987_ = lean_ctor_get(v___x_2954_, 0);
lean_dec(v_unused_2987_);
v___x_2967_ = v___x_2954_;
v_isShared_2968_ = v_isSharedCheck_2984_;
goto v_resetjp_2966_;
}
else
{
lean_dec(v___x_2954_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2984_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2969_ = lean_unsigned_to_nat(1u);
v___x_2970_ = lean_nat_dec_eq(v_remaining_2961_, v___x_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2971_ = lean_box(v___x_2970_);
lean_inc(v_value_2959_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v_value_2959_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_nat_sub(v_remaining_2961_, v___x_2969_);
lean_dec(v_remaining_2961_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 2, v___x_2973_);
v___x_2975_ = v___x_2967_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_value_2959_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_pos_2960_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v_fst_2956_ = v___x_2972_;
v_snd_2957_ = v___x_2975_;
goto v___jp_2955_;
}
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
lean_dec(v_remaining_2961_);
v___x_2977_ = lean_box(v___x_2962_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_value_2959_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_unsigned_to_nat(0u);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 2, v___x_2980_);
lean_ctor_set(v___x_2967_, 0, v___x_2979_);
v___x_2982_ = v___x_2967_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_pos_2960_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
v_fst_2956_ = v___x_2978_;
v_snd_2957_ = v___x_2982_;
goto v___jp_2955_;
}
}
}
}
v___jp_2955_:
{
lean_object* v___x_2958_; 
v___x_2958_ = lean_st_ref_put(v_slot_2951_, v_snd_2957_);
return v_fst_2956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_2988_, lean_object* v_next_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_2988_, v_next_2989_);
lean_dec(v_next_2989_);
lean_dec(v_slot_2988_);
return v_res_2991_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_2992_){
_start:
{
lean_object* v___x_2994_; lean_object* v_size_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2994_ = lean_st_ref_get(v_a_2992_);
v_size_2995_ = lean_ctor_get(v___x_2994_, 3);
lean_inc(v_size_2995_);
lean_dec(v___x_2994_);
v___x_2996_ = lean_unsigned_to_nat(0u);
v___x_2997_ = lean_nat_dec_eq(v_size_2995_, v___x_2996_);
lean_dec(v_size_2995_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_2998_, lean_object* v___y_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_2998_);
lean_dec(v_a_2998_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_3002_, lean_object* v_a_3003_){
_start:
{
lean_object* v___x_3005_; lean_object* v_capacity_3006_; lean_object* v_buffer_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3005_ = lean_st_ref_get(v_a_3003_);
v_capacity_3006_ = lean_ctor_get(v___x_3005_, 2);
lean_inc(v_capacity_3006_);
v_buffer_3007_ = lean_ctor_get(v___x_3005_, 4);
lean_inc_ref(v_buffer_3007_);
lean_dec(v___x_3005_);
v___x_3008_ = lean_nat_mod(v_place_3002_, v_capacity_3006_);
lean_dec(v_capacity_3006_);
v___x_3009_ = lean_array_fget(v_buffer_3007_, v___x_3008_);
lean_dec(v___x_3008_);
lean_dec_ref(v_buffer_3007_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_3010_, lean_object* v_a_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3010_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec(v_place_3010_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3017_ = lean_st_ref_get(v_a_3015_);
v___x_3018_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3015_);
if (v___x_3018_ == 0)
{
lean_object* v_capacity_3019_; uint8_t v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v_fst_3024_; lean_object* v_snd_3025_; lean_object* v_st_3027_; lean_object* v___y_3028_; 
v_capacity_3019_ = lean_ctor_get(v___x_3017_, 2);
lean_inc(v_capacity_3019_);
v___x_3020_ = 1;
v___x_3021_ = lean_nat_mod(v_next_3014_, v_capacity_3019_);
lean_dec(v_capacity_3019_);
v___x_3022_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_3021_, v_a_3015_);
lean_dec(v___x_3021_);
v___x_3023_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_3022_, v_next_3014_);
lean_dec(v___x_3022_);
v_fst_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_fst_3024_);
v_snd_3025_ = lean_ctor_get(v___x_3023_, 1);
lean_inc(v_snd_3025_);
lean_dec_ref(v___x_3023_);
if (lean_obj_tag(v_fst_3024_) == 1)
{
uint8_t v___x_3030_; 
v___x_3030_ = lean_unbox(v_snd_3025_);
lean_dec(v_snd_3025_);
if (v___x_3030_ == 0)
{
v_st_3027_ = v___x_3017_;
v___y_3028_ = v_a_3015_;
goto v___jp_3026_;
}
else
{
lean_object* v___x_3031_; lean_object* v_producers_3032_; lean_object* v_waiters_3033_; lean_object* v_capacity_3034_; lean_object* v_size_3035_; lean_object* v_buffer_3036_; lean_object* v_write_3037_; lean_object* v_read_3038_; lean_object* v_receivers_3039_; lean_object* v_nextId_3040_; uint8_t v_closed_3041_; lean_object* v_pos_3042_; lean_object* v___x_3043_; 
v___x_3031_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_3017_);
v_producers_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc_ref(v_producers_3032_);
v_waiters_3033_ = lean_ctor_get(v___x_3031_, 1);
lean_inc_ref(v_waiters_3033_);
v_capacity_3034_ = lean_ctor_get(v___x_3031_, 2);
lean_inc(v_capacity_3034_);
v_size_3035_ = lean_ctor_get(v___x_3031_, 3);
lean_inc(v_size_3035_);
v_buffer_3036_ = lean_ctor_get(v___x_3031_, 4);
lean_inc_ref(v_buffer_3036_);
v_write_3037_ = lean_ctor_get(v___x_3031_, 5);
lean_inc(v_write_3037_);
v_read_3038_ = lean_ctor_get(v___x_3031_, 6);
lean_inc(v_read_3038_);
v_receivers_3039_ = lean_ctor_get(v___x_3031_, 7);
lean_inc(v_receivers_3039_);
v_nextId_3040_ = lean_ctor_get(v___x_3031_, 8);
lean_inc(v_nextId_3040_);
v_closed_3041_ = lean_ctor_get_uint8(v___x_3031_, sizeof(void*)*10);
v_pos_3042_ = lean_ctor_get(v___x_3031_, 9);
lean_inc(v_pos_3042_);
v___x_3043_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3032_);
if (lean_obj_tag(v___x_3043_) == 1)
{
lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3055_; 
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3055_ == 0)
{
lean_object* v_unused_3056_; lean_object* v_unused_3057_; lean_object* v_unused_3058_; lean_object* v_unused_3059_; lean_object* v_unused_3060_; lean_object* v_unused_3061_; lean_object* v_unused_3062_; lean_object* v_unused_3063_; lean_object* v_unused_3064_; lean_object* v_unused_3065_; 
v_unused_3056_ = lean_ctor_get(v___x_3031_, 9);
lean_dec(v_unused_3056_);
v_unused_3057_ = lean_ctor_get(v___x_3031_, 8);
lean_dec(v_unused_3057_);
v_unused_3058_ = lean_ctor_get(v___x_3031_, 7);
lean_dec(v_unused_3058_);
v_unused_3059_ = lean_ctor_get(v___x_3031_, 6);
lean_dec(v_unused_3059_);
v_unused_3060_ = lean_ctor_get(v___x_3031_, 5);
lean_dec(v_unused_3060_);
v_unused_3061_ = lean_ctor_get(v___x_3031_, 4);
lean_dec(v_unused_3061_);
v_unused_3062_ = lean_ctor_get(v___x_3031_, 3);
lean_dec(v_unused_3062_);
v_unused_3063_ = lean_ctor_get(v___x_3031_, 2);
lean_dec(v_unused_3063_);
v_unused_3064_ = lean_ctor_get(v___x_3031_, 1);
lean_dec(v_unused_3064_);
v_unused_3065_ = lean_ctor_get(v___x_3031_, 0);
lean_dec(v_unused_3065_);
v___x_3045_ = v___x_3031_;
v_isShared_3046_ = v_isSharedCheck_3055_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v___x_3031_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3055_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_val_3047_; lean_object* v_fst_3048_; lean_object* v_snd_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v_val_3047_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_val_3047_);
lean_dec_ref_known(v___x_3043_, 1);
v_fst_3048_ = lean_ctor_get(v_val_3047_, 0);
lean_inc(v_fst_3048_);
v_snd_3049_ = lean_ctor_get(v_val_3047_, 1);
lean_inc(v_snd_3049_);
lean_dec(v_val_3047_);
v___x_3050_ = lean_box(v___x_3020_);
v___x_3051_ = lean_io_promise_resolve(v___x_3050_, v_fst_3048_);
lean_dec(v_fst_3048_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v_snd_3049_);
v___x_3053_ = v___x_3045_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_snd_3049_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_waiters_3033_);
lean_ctor_set(v_reuseFailAlloc_3054_, 2, v_capacity_3034_);
lean_ctor_set(v_reuseFailAlloc_3054_, 3, v_size_3035_);
lean_ctor_set(v_reuseFailAlloc_3054_, 4, v_buffer_3036_);
lean_ctor_set(v_reuseFailAlloc_3054_, 5, v_write_3037_);
lean_ctor_set(v_reuseFailAlloc_3054_, 6, v_read_3038_);
lean_ctor_set(v_reuseFailAlloc_3054_, 7, v_receivers_3039_);
lean_ctor_set(v_reuseFailAlloc_3054_, 8, v_nextId_3040_);
lean_ctor_set(v_reuseFailAlloc_3054_, 9, v_pos_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3054_, sizeof(void*)*10, v_closed_3041_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
v_st_3027_ = v___x_3053_;
v___y_3028_ = v_a_3015_;
goto v___jp_3026_;
}
}
}
else
{
lean_dec(v___x_3043_);
lean_dec(v_pos_3042_);
lean_dec(v_nextId_3040_);
lean_dec(v_receivers_3039_);
lean_dec(v_read_3038_);
lean_dec(v_write_3037_);
lean_dec_ref(v_buffer_3036_);
lean_dec(v_size_3035_);
lean_dec(v_capacity_3034_);
lean_dec_ref(v_waiters_3033_);
v_st_3027_ = v___x_3031_;
v___y_3028_ = v_a_3015_;
goto v___jp_3026_;
}
}
}
else
{
lean_object* v___x_3066_; 
lean_dec(v_snd_3025_);
lean_dec(v_fst_3024_);
lean_dec(v___x_3017_);
v___x_3066_ = lean_box(0);
return v___x_3066_;
}
v___jp_3026_:
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_st_ref_swap(v___y_3028_, v_st_3027_);
lean_dec(v___x_3029_);
return v_fst_3024_;
}
}
else
{
lean_object* v___x_3067_; 
lean_dec(v___x_3017_);
v___x_3067_ = lean_box(0);
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_3068_, lean_object* v_a_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec(v_next_3068_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v___x_3075_; lean_object* v_receivers_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_st_ref_get(v_a_3073_);
v_receivers_3076_ = lean_ctor_get(v___x_3075_, 7);
lean_inc(v_receivers_3076_);
lean_dec(v___x_3075_);
v___x_3077_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3076_, v_receiverId_3072_);
if (lean_obj_tag(v___x_3077_) == 1)
{
lean_object* v_val_3078_; lean_object* v___x_3079_; 
v_val_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_3078_, v_a_3073_);
lean_dec(v_val_3078_);
if (lean_obj_tag(v___x_3079_) == 1)
{
lean_object* v___x_3080_; lean_object* v_producers_3081_; lean_object* v_waiters_3082_; lean_object* v_capacity_3083_; lean_object* v_size_3084_; lean_object* v_buffer_3085_; lean_object* v_write_3086_; lean_object* v_read_3087_; lean_object* v_nextId_3088_; uint8_t v_closed_3089_; lean_object* v_pos_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3099_; 
v___x_3080_ = lean_st_ref_take(v_a_3073_);
v_producers_3081_ = lean_ctor_get(v___x_3080_, 0);
v_waiters_3082_ = lean_ctor_get(v___x_3080_, 1);
v_capacity_3083_ = lean_ctor_get(v___x_3080_, 2);
v_size_3084_ = lean_ctor_get(v___x_3080_, 3);
v_buffer_3085_ = lean_ctor_get(v___x_3080_, 4);
v_write_3086_ = lean_ctor_get(v___x_3080_, 5);
v_read_3087_ = lean_ctor_get(v___x_3080_, 6);
v_nextId_3088_ = lean_ctor_get(v___x_3080_, 8);
v_closed_3089_ = lean_ctor_get_uint8(v___x_3080_, sizeof(void*)*10);
v_pos_3090_ = lean_ctor_get(v___x_3080_, 9);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3080_, 7);
lean_dec(v_unused_3100_);
v___x_3092_ = v___x_3080_;
v_isShared_3093_ = v_isSharedCheck_3099_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_pos_3090_);
lean_inc(v_nextId_3088_);
lean_inc(v_read_3087_);
lean_inc(v_write_3086_);
lean_inc(v_buffer_3085_);
lean_inc(v_size_3084_);
lean_inc(v_capacity_3083_);
lean_inc(v_waiters_3082_);
lean_inc(v_producers_3081_);
lean_dec(v___x_3080_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3099_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3072_, v_receivers_3076_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 7, v___x_3094_);
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_producers_3081_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_waiters_3082_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_capacity_3083_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_size_3084_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_buffer_3085_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v_write_3086_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_read_3087_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_nextId_3088_);
lean_ctor_set(v_reuseFailAlloc_3098_, 9, v_pos_3090_);
lean_ctor_set_uint8(v_reuseFailAlloc_3098_, sizeof(void*)*10, v_closed_3089_);
v___x_3096_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_st_ref_put(v_a_3073_, v___x_3096_);
return v___x_3079_;
}
}
}
else
{
lean_object* v___x_3101_; 
lean_dec(v___x_3079_);
lean_dec(v_receivers_3076_);
lean_dec(v_receiverId_3072_);
v___x_3101_ = lean_box(0);
return v___x_3101_;
}
}
else
{
lean_object* v___x_3102_; 
lean_dec(v___x_3077_);
lean_dec(v_receivers_3076_);
lean_dec(v_receiverId_3072_);
v___x_3102_ = lean_box(0);
return v___x_3102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3103_, lean_object* v_a_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3103_, v_a_3104_);
lean_dec(v_a_3104_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3107_, v___y_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3111_, v___y_3112_);
lean_dec(v___y_3112_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3115_){
_start:
{
lean_object* v_state_3117_; lean_object* v_id_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; 
v_state_3117_ = lean_ctor_get(v_ch_3115_, 0);
lean_inc_ref(v_state_3117_);
v_id_3118_ = lean_ctor_get(v_ch_3115_, 1);
lean_inc(v_id_3118_);
lean_dec_ref(v_ch_3115_);
v___f_3119_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3119_, 0, v_id_3118_);
v___x_3120_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3117_, v___f_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3121_, lean_object* v_a_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3121_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3124_, lean_object* v_ch_3125_){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3128_, lean_object* v_ch_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3128_, v_ch_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3132_, lean_object* v_receiverId_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3133_, v_a_3134_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3137_, lean_object* v_receiverId_3138_, lean_object* v_a_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3137_, v_receiverId_3138_, v_a_3139_);
lean_dec(v_a_3139_);
return v_res_3141_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3142_, lean_object* v_a_3143_){
_start:
{
uint8_t v___x_3145_; 
v___x_3145_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3143_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3146_, lean_object* v_a_3147_, lean_object* v___y_3148_){
_start:
{
uint8_t v_res_3149_; lean_object* v_r_3150_; 
v_res_3149_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3146_, v_a_3147_);
lean_dec(v_a_3147_);
v_r_3150_ = lean_box(v_res_3149_);
return v_r_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3151_, lean_object* v_place_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3152_, v_a_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3156_, lean_object* v_place_3157_, lean_object* v_a_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3156_, v_place_3157_, v_a_3158_);
lean_dec(v_a_3158_);
lean_dec(v_place_3157_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3161_, lean_object* v_slot_3162_, lean_object* v_next_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3162_, v_next_3163_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3167_, lean_object* v_slot_3168_, lean_object* v_next_3169_, lean_object* v_a_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3167_, v_slot_3168_, v_next_3169_, v_a_3170_);
lean_dec(v_a_3170_);
lean_dec(v_next_3169_);
lean_dec(v_slot_3168_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3173_, lean_object* v_next_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3174_, v_a_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3178_, lean_object* v_next_3179_, lean_object* v_a_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3178_, v_next_3179_, v_a_3180_);
lean_dec(v_a_3180_);
lean_dec(v_next_3179_);
return v_res_3182_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3183_, lean_object* v_t_3184_){
_start:
{
if (lean_obj_tag(v_t_3184_) == 0)
{
lean_object* v_k_3185_; lean_object* v_l_3186_; lean_object* v_r_3187_; uint8_t v___x_3188_; 
v_k_3185_ = lean_ctor_get(v_t_3184_, 1);
v_l_3186_ = lean_ctor_get(v_t_3184_, 3);
v_r_3187_ = lean_ctor_get(v_t_3184_, 4);
v___x_3188_ = lean_nat_dec_lt(v_k_3183_, v_k_3185_);
if (v___x_3188_ == 0)
{
uint8_t v___x_3189_; 
v___x_3189_ = lean_nat_dec_eq(v_k_3183_, v_k_3185_);
if (v___x_3189_ == 0)
{
v_t_3184_ = v_r_3187_;
goto _start;
}
else
{
return v___x_3189_;
}
}
else
{
v_t_3184_ = v_l_3186_;
goto _start;
}
}
else
{
uint8_t v___x_3192_; 
v___x_3192_ = 0;
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3193_, lean_object* v_t_3194_){
_start:
{
uint8_t v_res_3195_; lean_object* v_r_3196_; 
v_res_3195_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3193_, v_t_3194_);
lean_dec(v_t_3194_);
lean_dec(v_k_3193_);
v_r_3196_ = lean_box(v_res_3195_);
return v_r_3196_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = lean_box(0);
v___x_3198_ = lean_task_pure(v___x_3197_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3199_, lean_object* v___f_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v___x_3203_; lean_object* v_receivers_3204_; uint8_t v___x_3205_; 
v___x_3203_ = lean_st_ref_get(v___y_3201_);
v_receivers_3204_ = lean_ctor_get(v___x_3203_, 7);
lean_inc(v_receivers_3204_);
lean_dec(v___x_3203_);
v___x_3205_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3199_, v_receivers_3204_);
lean_dec(v_receivers_3204_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref(v___f_3200_);
lean_dec(v_id_3199_);
v___x_3206_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3206_;
}
else
{
lean_object* v___x_3207_; 
v___x_3207_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3199_, v___y_3201_);
if (lean_obj_tag(v___x_3207_) == 1)
{
lean_object* v___x_3208_; 
lean_dec_ref(v___f_3200_);
v___x_3208_ = lean_task_pure(v___x_3207_);
return v___x_3208_;
}
else
{
lean_object* v___x_3209_; uint8_t v_closed_3210_; 
lean_dec(v___x_3207_);
v___x_3209_ = lean_st_ref_get(v___y_3201_);
v_closed_3210_ = lean_ctor_get_uint8(v___x_3209_, sizeof(void*)*10);
lean_dec(v___x_3209_);
if (v_closed_3210_ == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_producers_3213_; lean_object* v_waiters_3214_; lean_object* v_capacity_3215_; lean_object* v_size_3216_; lean_object* v_buffer_3217_; lean_object* v_write_3218_; lean_object* v_read_3219_; lean_object* v_receivers_3220_; lean_object* v_nextId_3221_; uint8_t v_closed_3222_; lean_object* v_pos_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3237_; 
v___x_3211_ = lean_io_promise_new();
v___x_3212_ = lean_st_ref_take(v___y_3201_);
v_producers_3213_ = lean_ctor_get(v___x_3212_, 0);
v_waiters_3214_ = lean_ctor_get(v___x_3212_, 1);
v_capacity_3215_ = lean_ctor_get(v___x_3212_, 2);
v_size_3216_ = lean_ctor_get(v___x_3212_, 3);
v_buffer_3217_ = lean_ctor_get(v___x_3212_, 4);
v_write_3218_ = lean_ctor_get(v___x_3212_, 5);
v_read_3219_ = lean_ctor_get(v___x_3212_, 6);
v_receivers_3220_ = lean_ctor_get(v___x_3212_, 7);
v_nextId_3221_ = lean_ctor_get(v___x_3212_, 8);
v_closed_3222_ = lean_ctor_get_uint8(v___x_3212_, sizeof(void*)*10);
v_pos_3223_ = lean_ctor_get(v___x_3212_, 9);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3225_ = v___x_3212_;
v_isShared_3226_ = v_isSharedCheck_3237_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_pos_3223_);
lean_inc(v_nextId_3221_);
lean_inc(v_receivers_3220_);
lean_inc(v_read_3219_);
lean_inc(v_write_3218_);
lean_inc(v_buffer_3217_);
lean_inc(v_size_3216_);
lean_inc(v_capacity_3215_);
lean_inc(v_waiters_3214_);
lean_inc(v_producers_3213_);
lean_dec(v___x_3212_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3237_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3227_ = lean_box(0);
lean_inc(v___x_3211_);
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3211_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = l_Std_Queue_enqueue___redArg(v___x_3228_, v_waiters_3214_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 1, v___x_3229_);
v___x_3231_ = v___x_3225_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_producers_3213_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_capacity_3215_);
lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_size_3216_);
lean_ctor_set(v_reuseFailAlloc_3236_, 4, v_buffer_3217_);
lean_ctor_set(v_reuseFailAlloc_3236_, 5, v_write_3218_);
lean_ctor_set(v_reuseFailAlloc_3236_, 6, v_read_3219_);
lean_ctor_set(v_reuseFailAlloc_3236_, 7, v_receivers_3220_);
lean_ctor_set(v_reuseFailAlloc_3236_, 8, v_nextId_3221_);
lean_ctor_set(v_reuseFailAlloc_3236_, 9, v_pos_3223_);
lean_ctor_set_uint8(v_reuseFailAlloc_3236_, sizeof(void*)*10, v_closed_3222_);
v___x_3231_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3232_ = lean_st_ref_put(v___y_3201_, v___x_3231_);
v___x_3233_ = lean_io_promise_result_opt(v___x_3211_);
lean_dec(v___x_3211_);
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = lean_io_bind_task(v___x_3233_, v___f_3200_, v___x_3234_, v_closed_3210_);
return v___x_3235_;
}
}
}
else
{
lean_object* v___x_3238_; 
lean_dec_ref(v___f_3200_);
v___x_3238_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3239_, lean_object* v___f_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3239_, v___f_3240_, v___y_3241_);
lean_dec(v___y_3241_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3244_, lean_object* v_res_3245_){
_start:
{
if (lean_obj_tag(v_res_3245_) == 0)
{
lean_dec_ref(v_ch_3244_);
goto v___jp_3247_;
}
else
{
lean_object* v_val_3249_; uint8_t v___x_3250_; 
v_val_3249_ = lean_ctor_get(v_res_3245_, 0);
v___x_3250_ = lean_unbox(v_val_3249_);
if (v___x_3250_ == 0)
{
lean_dec_ref(v_ch_3244_);
goto v___jp_3247_;
}
else
{
lean_object* v___x_3251_; 
v___x_3251_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3244_);
return v___x_3251_;
}
}
v___jp_3247_:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3252_, lean_object* v_res_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3252_, v_res_3253_);
lean_dec(v_res_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3256_){
_start:
{
lean_object* v_state_3258_; lean_object* v_id_3259_; lean_object* v___f_3260_; lean_object* v___f_3261_; lean_object* v___x_3262_; 
v_state_3258_ = lean_ctor_get(v_ch_3256_, 0);
lean_inc_ref(v_state_3258_);
v_id_3259_ = lean_ctor_get(v_ch_3256_, 1);
lean_inc(v_id_3259_);
v___f_3260_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3260_, 0, v_ch_3256_);
v___f_3261_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3261_, 0, v_id_3259_);
lean_closure_set(v___f_3261_, 1, v___f_3260_);
v___x_3262_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3258_, v___f_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v_res_3265_; 
v_res_3265_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3263_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3266_, lean_object* v_ch_3267_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3267_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3270_, lean_object* v_ch_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3270_, v_ch_3271_);
return v_res_3273_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3274_, lean_object* v_k_3275_, lean_object* v_t_3276_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3275_, v_t_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3278_, lean_object* v_k_3279_, lean_object* v_t_3280_){
_start:
{
uint8_t v_res_3281_; lean_object* v_r_3282_; 
v_res_3281_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3278_, v_k_3279_, v_t_3280_);
lean_dec(v_t_3280_);
lean_dec(v_k_3279_);
v_r_3282_ = lean_box(v_res_3281_);
return v_r_3282_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_box(0);
v___x_3284_ = lean_task_pure(v___x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3285_, lean_object* v_ch_3286_, lean_object* v_prio_3287_, lean_object* v_x_3288_){
_start:
{
if (lean_obj_tag(v_x_3288_) == 0)
{
lean_object* v___x_3290_; 
lean_dec(v_prio_3287_);
lean_dec_ref(v_ch_3286_);
lean_dec_ref(v_f_3285_);
v___x_3290_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3290_;
}
else
{
lean_object* v_val_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_val_3291_ = lean_ctor_get(v_x_3288_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v_x_3288_, 1);
lean_inc_ref(v_f_3285_);
v___x_3292_ = lean_apply_2(v_f_3285_, v_val_3291_, lean_box(0));
v___x_3293_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3285_, v_ch_3286_, v_prio_3287_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3294_, lean_object* v_ch_3295_, lean_object* v_prio_3296_, lean_object* v_x_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3294_, v_ch_3295_, v_prio_3296_, v_x_3297_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3300_, lean_object* v_ch_3301_, lean_object* v_prio_3302_){
_start:
{
lean_object* v___f_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; 
lean_inc(v_prio_3302_);
lean_inc_ref(v_ch_3301_);
v___f_3304_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3304_, 0, v_f_3300_);
lean_closure_set(v___f_3304_, 1, v_ch_3301_);
lean_closure_set(v___f_3304_, 2, v_prio_3302_);
v___x_3305_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3301_);
v___x_3306_ = 0;
v___x_3307_ = lean_io_bind_task(v___x_3305_, v___f_3304_, v_prio_3302_, v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3308_, lean_object* v_ch_3309_, lean_object* v_prio_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3308_, v_ch_3309_, v_prio_3310_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3313_, lean_object* v_f_3314_, lean_object* v_ch_3315_, lean_object* v_prio_3316_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3314_, v_ch_3315_, v_prio_3316_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3319_, lean_object* v_f_3320_, lean_object* v_ch_3321_, lean_object* v_prio_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3319_, v_f_3320_, v_ch_3321_, v_prio_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3325_, lean_object* v_val_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v_pos_3328_; lean_object* v_toPure_3329_; uint8_t v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_pos_3328_ = lean_ctor_get(v_a_3327_, 1);
v_toPure_3329_ = lean_ctor_get(v_toApplicative_3325_, 1);
lean_inc(v_toPure_3329_);
lean_dec_ref(v_toApplicative_3325_);
v___x_3330_ = lean_nat_dec_eq(v_pos_3328_, v_val_3326_);
v___x_3331_ = lean_box(v___x_3330_);
v___x_3332_ = lean_apply_2(v_toPure_3329_, lean_box(0), v___x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3333_, lean_object* v_val_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3333_, v_val_3334_, v_a_3335_);
lean_dec_ref(v_a_3335_);
lean_dec(v_val_3334_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3337_, lean_object* v_toBind_3338_, lean_object* v___f_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3341_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3341_, 0, lean_box(0));
lean_closure_set(v___x_3341_, 1, lean_box(0));
lean_closure_set(v___x_3341_, 2, v_a_3340_);
v___x_3342_ = lean_apply_2(v_inst_3337_, lean_box(0), v___x_3341_);
v___x_3343_ = lean_apply_4(v_toBind_3338_, lean_box(0), lean_box(0), v___x_3342_, v___f_3339_);
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3344_, lean_object* v_receiverId_3345_, lean_object* v_toApplicative_3346_, lean_object* v_inst_3347_, lean_object* v_toBind_3348_, lean_object* v_inst_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
uint8_t v_closed_3352_; 
v_closed_3352_ = lean_ctor_get_uint8(v_a_3351_, sizeof(void*)*10);
if (v_closed_3352_ == 0)
{
lean_object* v_capacity_3353_; lean_object* v_size_3354_; lean_object* v_receivers_3355_; lean_object* v___x_3356_; 
v_capacity_3353_ = lean_ctor_get(v_a_3351_, 2);
lean_inc(v_capacity_3353_);
v_size_3354_ = lean_ctor_get(v_a_3351_, 3);
lean_inc(v_size_3354_);
v_receivers_3355_ = lean_ctor_get(v_a_3351_, 7);
lean_inc(v_receivers_3355_);
lean_dec_ref(v_a_3351_);
v___x_3356_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3344_, v_receivers_3355_, v_receiverId_3345_);
if (lean_obj_tag(v___x_3356_) == 1)
{
lean_object* v_val_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
v_val_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___x_3358_ = lean_unsigned_to_nat(0u);
v___x_3359_ = lean_nat_dec_eq(v_size_3354_, v___x_3358_);
lean_dec(v_size_3354_);
if (v___x_3359_ == 0)
{
lean_object* v___f_3360_; lean_object* v___f_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_inc(v_val_3357_);
v___f_3360_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3360_, 0, v_toApplicative_3346_);
lean_closure_set(v___f_3360_, 1, v_val_3357_);
lean_inc(v_toBind_3348_);
lean_inc(v_inst_3347_);
v___f_3361_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3361_, 0, v_inst_3347_);
lean_closure_set(v___f_3361_, 1, v_toBind_3348_);
lean_closure_set(v___f_3361_, 2, v___f_3360_);
v___x_3362_ = lean_nat_mod(v_val_3357_, v_capacity_3353_);
lean_dec(v_capacity_3353_);
lean_dec(v_val_3357_);
v___x_3363_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3349_, v_inst_3347_, v___x_3362_, v_a_3350_);
v___x_3364_ = lean_apply_4(v_toBind_3348_, lean_box(0), lean_box(0), v___x_3363_, v___f_3361_);
return v___x_3364_;
}
else
{
lean_object* v_toPure_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec(v_val_3357_);
lean_dec(v_capacity_3353_);
lean_dec_ref(v_inst_3349_);
lean_dec(v_toBind_3348_);
lean_dec(v_inst_3347_);
v_toPure_3365_ = lean_ctor_get(v_toApplicative_3346_, 1);
lean_inc(v_toPure_3365_);
lean_dec_ref(v_toApplicative_3346_);
v___x_3366_ = lean_box(v_closed_3352_);
v___x_3367_ = lean_apply_2(v_toPure_3365_, lean_box(0), v___x_3366_);
return v___x_3367_;
}
}
else
{
lean_object* v_toPure_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_dec(v___x_3356_);
lean_dec(v_size_3354_);
lean_dec(v_capacity_3353_);
lean_dec_ref(v_inst_3349_);
lean_dec(v_toBind_3348_);
lean_dec(v_inst_3347_);
v_toPure_3368_ = lean_ctor_get(v_toApplicative_3346_, 1);
lean_inc(v_toPure_3368_);
lean_dec_ref(v_toApplicative_3346_);
v___x_3369_ = lean_box(v_closed_3352_);
v___x_3370_ = lean_apply_2(v_toPure_3368_, lean_box(0), v___x_3369_);
return v___x_3370_;
}
}
else
{
lean_object* v_toPure_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
lean_dec_ref(v_a_3351_);
lean_dec_ref(v_inst_3349_);
lean_dec(v_toBind_3348_);
lean_dec(v_inst_3347_);
lean_dec(v_receiverId_3345_);
lean_dec_ref(v___f_3344_);
v_toPure_3371_ = lean_ctor_get(v_toApplicative_3346_, 1);
lean_inc(v_toPure_3371_);
lean_dec_ref(v_toApplicative_3346_);
v___x_3372_ = lean_box(v_closed_3352_);
v___x_3373_ = lean_apply_2(v_toPure_3371_, lean_box(0), v___x_3372_);
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object* v___f_3374_, lean_object* v_receiverId_3375_, lean_object* v_toApplicative_3376_, lean_object* v_inst_3377_, lean_object* v_toBind_3378_, lean_object* v_inst_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(v___f_3374_, v_receiverId_3375_, v_toApplicative_3376_, v_inst_3377_, v_toBind_3378_, v_inst_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3383_, lean_object* v_inst_3384_, lean_object* v_receiverId_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v_toApplicative_3387_; lean_object* v_toBind_3388_; lean_object* v___f_3389_; lean_object* v___f_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v_toApplicative_3387_ = lean_ctor_get(v_inst_3383_, 0);
lean_inc_ref(v_toApplicative_3387_);
v_toBind_3388_ = lean_ctor_get(v_inst_3383_, 1);
lean_inc_n(v_toBind_3388_, 2);
v___f_3389_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3386_, 2);
lean_inc(v_inst_3384_);
v___f_3390_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3390_, 0, v___f_3389_);
lean_closure_set(v___f_3390_, 1, v_receiverId_3385_);
lean_closure_set(v___f_3390_, 2, v_toApplicative_3387_);
lean_closure_set(v___f_3390_, 3, v_inst_3384_);
lean_closure_set(v___f_3390_, 4, v_toBind_3388_);
lean_closure_set(v___f_3390_, 5, v_inst_3383_);
lean_closure_set(v___f_3390_, 6, v_a_3386_);
v___x_3391_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3391_, 0, lean_box(0));
lean_closure_set(v___x_3391_, 1, lean_box(0));
lean_closure_set(v___x_3391_, 2, v_a_3386_);
v___x_3392_ = lean_apply_2(v_inst_3384_, lean_box(0), v___x_3391_);
v___x_3393_ = lean_apply_4(v_toBind_3388_, lean_box(0), lean_box(0), v___x_3392_, v___f_3390_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object* v_inst_3394_, lean_object* v_inst_3395_, lean_object* v_receiverId_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(v_inst_3394_, v_inst_3395_, v_receiverId_3396_, v_a_3397_);
lean_dec(v_a_3397_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3399_, lean_object* v_00_u03b1_3400_, lean_object* v_inst_3401_, lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_receiverId_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_toApplicative_3407_; lean_object* v_toBind_3408_; lean_object* v___f_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v_toApplicative_3407_ = lean_ctor_get(v_inst_3401_, 0);
lean_inc_ref(v_toApplicative_3407_);
v_toBind_3408_ = lean_ctor_get(v_inst_3401_, 1);
lean_inc_n(v_toBind_3408_, 2);
v___f_3409_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3406_, 2);
lean_inc(v_inst_3402_);
v___f_3410_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3410_, 0, v___f_3409_);
lean_closure_set(v___f_3410_, 1, v_receiverId_3405_);
lean_closure_set(v___f_3410_, 2, v_toApplicative_3407_);
lean_closure_set(v___f_3410_, 3, v_inst_3402_);
lean_closure_set(v___f_3410_, 4, v_toBind_3408_);
lean_closure_set(v___f_3410_, 5, v_inst_3401_);
lean_closure_set(v___f_3410_, 6, v_a_3406_);
v___x_3411_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3411_, 0, lean_box(0));
lean_closure_set(v___x_3411_, 1, lean_box(0));
lean_closure_set(v___x_3411_, 2, v_a_3406_);
v___x_3412_ = lean_apply_2(v_inst_3402_, lean_box(0), v___x_3411_);
v___x_3413_ = lean_apply_4(v_toBind_3408_, lean_box(0), lean_box(0), v___x_3412_, v___f_3410_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3414_, lean_object* v_00_u03b1_3415_, lean_object* v_inst_3416_, lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_receiverId_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3414_, v_00_u03b1_3415_, v_inst_3416_, v_inst_3417_, v_inst_3418_, v_inst_3419_, v_receiverId_3420_, v_a_3421_);
lean_dec(v_a_3421_);
lean_dec(v_inst_3419_);
lean_dec(v_inst_3418_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3425_, lean_object* v_lose_3426_){
_start:
{
lean_object* v_finished_3428_; lean_object* v_promise_3429_; lean_object* v___x_3430_; uint8_t v___y_3432_; uint8_t v___x_3440_; 
v_finished_3428_ = lean_ctor_get(v_w_3425_, 0);
v_promise_3429_ = lean_ctor_get(v_w_3425_, 1);
v___x_3430_ = lean_st_ref_take(v_finished_3428_);
v___x_3440_ = lean_unbox(v___x_3430_);
lean_dec(v___x_3430_);
if (v___x_3440_ == 0)
{
uint8_t v___x_3441_; 
v___x_3441_ = 1;
v___y_3432_ = v___x_3441_;
goto v___jp_3431_;
}
else
{
uint8_t v___x_3442_; 
v___x_3442_ = 0;
v___y_3432_ = v___x_3442_;
goto v___jp_3431_;
}
v___jp_3431_:
{
uint8_t v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3433_ = 1;
v___x_3434_ = lean_box(v___x_3433_);
v___x_3435_ = lean_st_ref_put(v_finished_3428_, v___x_3434_);
if (v___y_3432_ == 0)
{
lean_object* v___x_3436_; 
v___x_3436_ = lean_apply_1(v_lose_3426_, lean_box(0));
return v___x_3436_;
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_dec_ref(v_lose_3426_);
v___x_3437_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3438_ = lean_io_promise_resolve(v___x_3437_, v_promise_3429_);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3443_, lean_object* v_lose_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3443_, v_lose_3444_);
lean_dec_ref(v_w_3443_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3447_, lean_object* v_w_3448_, lean_object* v_lose_3449_){
_start:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3448_, v_lose_3449_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3452_, lean_object* v_w_3453_, lean_object* v_lose_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3452_, v_w_3453_, v_lose_3454_);
lean_dec_ref(v_w_3453_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v___x_3460_; lean_object* v_receivers_3461_; lean_object* v___x_3462_; 
v___x_3460_ = lean_st_ref_get(v_a_3458_);
v_receivers_3461_ = lean_ctor_get(v___x_3460_, 7);
lean_inc(v_receivers_3461_);
lean_dec(v___x_3460_);
v___x_3462_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3461_, v_receiverId_3457_);
if (lean_obj_tag(v___x_3462_) == 1)
{
lean_object* v_val_3463_; lean_object* v___x_3464_; 
v_val_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v___x_3462_, 1);
v___x_3464_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3463_, v_a_3458_);
lean_dec(v_val_3463_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3497_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3497_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3497_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
if (lean_obj_tag(v_a_3465_) == 1)
{
lean_object* v___x_3469_; lean_object* v_producers_3470_; lean_object* v_waiters_3471_; lean_object* v_capacity_3472_; lean_object* v_size_3473_; lean_object* v_buffer_3474_; lean_object* v_write_3475_; lean_object* v_read_3476_; lean_object* v_nextId_3477_; uint8_t v_closed_3478_; lean_object* v_pos_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3491_; 
v___x_3469_ = lean_st_ref_take(v_a_3458_);
v_producers_3470_ = lean_ctor_get(v___x_3469_, 0);
v_waiters_3471_ = lean_ctor_get(v___x_3469_, 1);
v_capacity_3472_ = lean_ctor_get(v___x_3469_, 2);
v_size_3473_ = lean_ctor_get(v___x_3469_, 3);
v_buffer_3474_ = lean_ctor_get(v___x_3469_, 4);
v_write_3475_ = lean_ctor_get(v___x_3469_, 5);
v_read_3476_ = lean_ctor_get(v___x_3469_, 6);
v_nextId_3477_ = lean_ctor_get(v___x_3469_, 8);
v_closed_3478_ = lean_ctor_get_uint8(v___x_3469_, sizeof(void*)*10);
v_pos_3479_ = lean_ctor_get(v___x_3469_, 9);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; 
v_unused_3492_ = lean_ctor_get(v___x_3469_, 7);
lean_dec(v_unused_3492_);
v___x_3481_ = v___x_3469_;
v_isShared_3482_ = v_isSharedCheck_3491_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_pos_3479_);
lean_inc(v_nextId_3477_);
lean_inc(v_read_3476_);
lean_inc(v_write_3475_);
lean_inc(v_buffer_3474_);
lean_inc(v_size_3473_);
lean_inc(v_capacity_3472_);
lean_inc(v_waiters_3471_);
lean_inc(v_producers_3470_);
lean_dec(v___x_3469_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3491_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3457_, v_receivers_3461_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 7, v___x_3483_);
v___x_3485_ = v___x_3481_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_producers_3470_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_waiters_3471_);
lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_capacity_3472_);
lean_ctor_set(v_reuseFailAlloc_3490_, 3, v_size_3473_);
lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_buffer_3474_);
lean_ctor_set(v_reuseFailAlloc_3490_, 5, v_write_3475_);
lean_ctor_set(v_reuseFailAlloc_3490_, 6, v_read_3476_);
lean_ctor_set(v_reuseFailAlloc_3490_, 7, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3490_, 8, v_nextId_3477_);
lean_ctor_set(v_reuseFailAlloc_3490_, 9, v_pos_3479_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*10, v_closed_3478_);
v___x_3485_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3486_ = lean_st_ref_put(v_a_3458_, v___x_3485_);
if (v_isShared_3468_ == 0)
{
v___x_3488_ = v___x_3467_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3465_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_dec(v_a_3465_);
lean_dec(v_receivers_3461_);
lean_dec(v_receiverId_3457_);
v___x_3493_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3493_);
v___x_3495_ = v___x_3467_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_dec(v_receivers_3461_);
lean_dec(v_receiverId_3457_);
return v___x_3464_;
}
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v___x_3462_);
lean_dec(v_receivers_3461_);
lean_dec(v_receiverId_3457_);
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3500_, lean_object* v_a_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3500_, v_a_3501_);
lean_dec(v_a_3501_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3504_, lean_object* v_w_3505_, lean_object* v_lose_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_finished_3509_; lean_object* v_promise_3510_; lean_object* v___x_3511_; uint8_t v___y_3513_; uint8_t v___x_3537_; 
v_finished_3509_ = lean_ctor_get(v_w_3505_, 0);
v_promise_3510_ = lean_ctor_get(v_w_3505_, 1);
v___x_3511_ = lean_st_ref_take(v_finished_3509_);
v___x_3537_ = lean_unbox(v___x_3511_);
lean_dec(v___x_3511_);
if (v___x_3537_ == 0)
{
uint8_t v___x_3538_; 
v___x_3538_ = 1;
v___y_3513_ = v___x_3538_;
goto v___jp_3512_;
}
else
{
uint8_t v___x_3539_; 
v___x_3539_ = 0;
v___y_3513_ = v___x_3539_;
goto v___jp_3512_;
}
v___jp_3512_:
{
uint8_t v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = 1;
v___x_3515_ = lean_box(v___x_3514_);
v___x_3516_ = lean_st_ref_put(v_finished_3509_, v___x_3515_);
if (v___y_3513_ == 0)
{
lean_object* v___x_3517_; 
lean_dec(v___x_3504_);
lean_inc(v___y_3507_);
v___x_3517_ = lean_apply_2(v_lose_3506_, v___y_3507_, lean_box(0));
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; 
lean_dec_ref(v_lose_3506_);
v___x_3518_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3504_, v___y_3507_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3528_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3523_, 0, v_a_3519_);
v___x_3524_ = lean_io_promise_resolve(v___x_3523_, v_promise_3510_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3524_);
v___x_3526_ = v___x_3521_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
v_a_3529_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3518_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3518_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3540_, lean_object* v_w_3541_, lean_object* v_lose_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3540_, v_w_3541_, v_lose_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v_w_3541_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3546_, lean_object* v___x_3547_, lean_object* v_w_3548_, lean_object* v_lose_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3547_, v_w_3548_, v_lose_3549_, v___y_3550_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3553_, lean_object* v___x_3554_, lean_object* v_w_3555_, lean_object* v_lose_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3553_, v___x_3554_, v_w_3555_, v_lose_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v_w_3555_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3560_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3563_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3566_, lean_object* v___f_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; uint8_t v_closed_3571_; 
v___x_3570_ = lean_st_ref_get(v___y_3568_);
v_closed_3571_ = lean_ctor_get_uint8(v___x_3570_, sizeof(void*)*10);
if (v_closed_3571_ == 0)
{
lean_object* v_capacity_3572_; lean_object* v_size_3573_; lean_object* v_receivers_3574_; lean_object* v___x_3575_; 
v_capacity_3572_ = lean_ctor_get(v___x_3570_, 2);
lean_inc(v_capacity_3572_);
v_size_3573_ = lean_ctor_get(v___x_3570_, 3);
lean_inc(v_size_3573_);
v_receivers_3574_ = lean_ctor_get(v___x_3570_, 7);
lean_inc(v_receivers_3574_);
lean_dec(v___x_3570_);
v___x_3575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3574_, v_id_3566_);
lean_dec(v_receivers_3574_);
if (lean_obj_tag(v___x_3575_) == 1)
{
lean_object* v_val_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v_val_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_val_3576_);
lean_dec_ref_known(v___x_3575_, 1);
v___x_3577_ = lean_unsigned_to_nat(0u);
v___x_3578_ = lean_nat_dec_eq(v_size_3573_, v___x_3577_);
lean_dec(v_size_3573_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = lean_nat_mod(v_val_3576_, v_capacity_3572_);
lean_dec(v_capacity_3572_);
v___x_3580_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3579_, v___y_3568_);
lean_dec(v___x_3579_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3582_; lean_object* v_pos_3583_; uint8_t v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
v___x_3582_ = lean_st_ref_get(v_a_3581_);
lean_dec(v_a_3581_);
v_pos_3583_ = lean_ctor_get(v___x_3582_, 1);
lean_inc(v_pos_3583_);
lean_dec(v___x_3582_);
v___x_3584_ = lean_nat_dec_eq(v_pos_3583_, v_val_3576_);
lean_dec(v_val_3576_);
lean_dec(v_pos_3583_);
v___x_3585_ = lean_box(v___x_3584_);
lean_inc(v___y_3568_);
v___x_3586_ = lean_apply_3(v___f_3567_, v___x_3585_, v___y_3568_, lean_box(0));
return v___x_3586_;
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec(v_val_3576_);
lean_dec_ref(v___f_3567_);
v_a_3587_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3580_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3580_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
else
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
lean_dec(v_val_3576_);
lean_dec(v_capacity_3572_);
v___x_3595_ = lean_box(v_closed_3571_);
lean_inc(v___y_3568_);
v___x_3596_ = lean_apply_3(v___f_3567_, v___x_3595_, v___y_3568_, lean_box(0));
return v___x_3596_;
}
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec(v___x_3575_);
lean_dec(v_size_3573_);
lean_dec(v_capacity_3572_);
v___x_3597_ = lean_box(v_closed_3571_);
lean_inc(v___y_3568_);
v___x_3598_ = lean_apply_3(v___f_3567_, v___x_3597_, v___y_3568_, lean_box(0));
return v___x_3598_;
}
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_dec(v___x_3570_);
v___x_3599_ = lean_box(v_closed_3571_);
lean_inc(v___y_3568_);
v___x_3600_ = lean_apply_3(v___f_3567_, v___x_3599_, v___y_3568_, lean_box(0));
return v___x_3600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3601_, lean_object* v___f_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3601_, v___f_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec(v_id_3601_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v_producers_3610_; lean_object* v_waiters_3611_; lean_object* v_capacity_3612_; lean_object* v_size_3613_; lean_object* v_buffer_3614_; lean_object* v_write_3615_; lean_object* v_read_3616_; lean_object* v_receivers_3617_; lean_object* v_nextId_3618_; uint8_t v_closed_3619_; lean_object* v_pos_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3643_; 
v___x_3609_ = lean_st_ref_get(v___y_3607_);
v_producers_3610_ = lean_ctor_get(v___x_3609_, 0);
v_waiters_3611_ = lean_ctor_get(v___x_3609_, 1);
v_capacity_3612_ = lean_ctor_get(v___x_3609_, 2);
v_size_3613_ = lean_ctor_get(v___x_3609_, 3);
v_buffer_3614_ = lean_ctor_get(v___x_3609_, 4);
v_write_3615_ = lean_ctor_get(v___x_3609_, 5);
v_read_3616_ = lean_ctor_get(v___x_3609_, 6);
v_receivers_3617_ = lean_ctor_get(v___x_3609_, 7);
v_nextId_3618_ = lean_ctor_get(v___x_3609_, 8);
v_closed_3619_ = lean_ctor_get_uint8(v___x_3609_, sizeof(void*)*10);
v_pos_3620_ = lean_ctor_get(v___x_3609_, 9);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3622_ = v___x_3609_;
v_isShared_3623_ = v_isSharedCheck_3643_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_pos_3620_);
lean_inc(v_nextId_3618_);
lean_inc(v_receivers_3617_);
lean_inc(v_read_3616_);
lean_inc(v_write_3615_);
lean_inc(v_buffer_3614_);
lean_inc(v_size_3613_);
lean_inc(v_capacity_3612_);
lean_inc(v_waiters_3611_);
lean_inc(v_producers_3610_);
lean_dec(v___x_3609_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3643_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3611_);
if (lean_obj_tag(v___x_3624_) == 1)
{
lean_object* v_val_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3640_; 
v_val_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3640_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_val_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3640_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v_fst_3629_; lean_object* v_snd_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
v_fst_3629_ = lean_ctor_get(v_val_3625_, 0);
lean_inc(v_fst_3629_);
v_snd_3630_ = lean_ctor_get(v_val_3625_, 1);
lean_inc(v_snd_3630_);
lean_dec(v_val_3625_);
v___x_3631_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3629_, v_____do__lift_3606_);
lean_dec(v_fst_3629_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 1, v_snd_3630_);
v___x_3633_ = v___x_3622_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_producers_3610_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_snd_3630_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_capacity_3612_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v_size_3613_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_buffer_3614_);
lean_ctor_set(v_reuseFailAlloc_3639_, 5, v_write_3615_);
lean_ctor_set(v_reuseFailAlloc_3639_, 6, v_read_3616_);
lean_ctor_set(v_reuseFailAlloc_3639_, 7, v_receivers_3617_);
lean_ctor_set(v_reuseFailAlloc_3639_, 8, v_nextId_3618_);
lean_ctor_set(v_reuseFailAlloc_3639_, 9, v_pos_3620_);
lean_ctor_set_uint8(v_reuseFailAlloc_3639_, sizeof(void*)*10, v_closed_3619_);
v___x_3633_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_st_ref_swap(v___y_3607_, v___x_3633_);
lean_dec(v___x_3635_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3634_);
v___x_3637_ = v___x_3627_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3634_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
lean_dec(v___x_3624_);
lean_del_object(v___x_3622_);
lean_dec(v_pos_3620_);
lean_dec(v_nextId_3618_);
lean_dec(v_receivers_3617_);
lean_dec(v_read_3616_);
lean_dec(v_write_3615_);
lean_dec_ref(v_buffer_3614_);
lean_dec(v_size_3613_);
lean_dec(v_capacity_3612_);
lean_dec_ref(v_producers_3610_);
v___x_3641_ = lean_box(0);
v___x_3642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
return v___x_3642_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
uint8_t v_____do__lift_3763__boxed_3647_; lean_object* v_res_3648_; 
v_____do__lift_3763__boxed_3647_ = lean_unbox(v_____do__lift_3644_);
v_res_3648_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3763__boxed_3647_, v___y_3645_);
lean_dec(v___y_3645_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3649_, lean_object* v___f_3650_, lean_object* v_id_3651_, uint8_t v_____do__lift_3652_, lean_object* v___y_3653_){
_start:
{
if (v_____do__lift_3652_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v_producers_3657_; lean_object* v_waiters_3658_; lean_object* v_capacity_3659_; lean_object* v_size_3660_; lean_object* v_buffer_3661_; lean_object* v_write_3662_; lean_object* v_read_3663_; lean_object* v_receivers_3664_; lean_object* v_nextId_3665_; uint8_t v_closed_3666_; lean_object* v_pos_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v_id_3651_);
v___x_3655_ = lean_io_promise_new();
v___x_3656_ = lean_st_ref_take(v___y_3653_);
v_producers_3657_ = lean_ctor_get(v___x_3656_, 0);
v_waiters_3658_ = lean_ctor_get(v___x_3656_, 1);
v_capacity_3659_ = lean_ctor_get(v___x_3656_, 2);
v_size_3660_ = lean_ctor_get(v___x_3656_, 3);
v_buffer_3661_ = lean_ctor_get(v___x_3656_, 4);
v_write_3662_ = lean_ctor_get(v___x_3656_, 5);
v_read_3663_ = lean_ctor_get(v___x_3656_, 6);
v_receivers_3664_ = lean_ctor_get(v___x_3656_, 7);
v_nextId_3665_ = lean_ctor_get(v___x_3656_, 8);
v_closed_3666_ = lean_ctor_get_uint8(v___x_3656_, sizeof(void*)*10);
v_pos_3667_ = lean_ctor_get(v___x_3656_, 9);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3669_ = v___x_3656_;
v_isShared_3670_ = v_isSharedCheck_3681_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_pos_3667_);
lean_inc(v_nextId_3665_);
lean_inc(v_receivers_3664_);
lean_inc(v_read_3663_);
lean_inc(v_write_3662_);
lean_inc(v_buffer_3661_);
lean_inc(v_size_3660_);
lean_inc(v_capacity_3659_);
lean_inc(v_waiters_3658_);
lean_inc(v_producers_3657_);
lean_dec(v___x_3656_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3681_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3671_, 0, v_waiter_3649_);
lean_inc(v___x_3655_);
v___x_3672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3655_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v___x_3673_ = l_Std_Queue_enqueue___redArg(v___x_3672_, v_waiters_3658_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3673_);
v___x_3675_ = v___x_3669_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_producers_3657_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_capacity_3659_);
lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_size_3660_);
lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_buffer_3661_);
lean_ctor_set(v_reuseFailAlloc_3680_, 5, v_write_3662_);
lean_ctor_set(v_reuseFailAlloc_3680_, 6, v_read_3663_);
lean_ctor_set(v_reuseFailAlloc_3680_, 7, v_receivers_3664_);
lean_ctor_set(v_reuseFailAlloc_3680_, 8, v_nextId_3665_);
lean_ctor_set(v_reuseFailAlloc_3680_, 9, v_pos_3667_);
lean_ctor_set_uint8(v_reuseFailAlloc_3680_, sizeof(void*)*10, v_closed_3666_);
v___x_3675_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3676_ = lean_st_ref_put(v___y_3653_, v___x_3675_);
v___x_3677_ = lean_io_promise_result_opt(v___x_3655_);
lean_dec(v___x_3655_);
v___x_3678_ = lean_unsigned_to_nat(0u);
v___x_3679_ = l_EIO_chainTask___redArg(v___x_3677_, v___f_3650_, v___x_3678_, v_____do__lift_3652_);
return v___x_3679_;
}
}
}
else
{
lean_object* v___x_3682_; lean_object* v_lose_3683_; lean_object* v___x_3684_; 
lean_dec_ref(v___f_3650_);
v___x_3682_ = lean_box(v_____do__lift_3652_);
v_lose_3683_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3683_, 0, v___x_3682_);
v___x_3684_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3651_, v_waiter_3649_, v_lose_3683_, v___y_3653_);
lean_dec_ref(v_waiter_3649_);
return v___x_3684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3685_, lean_object* v___f_3686_, lean_object* v_id_3687_, lean_object* v_____do__lift_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
uint8_t v_____do__lift_3821__boxed_3691_; lean_object* v_res_3692_; 
v_____do__lift_3821__boxed_3691_ = lean_unbox(v_____do__lift_3688_);
v_res_3692_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3685_, v___f_3686_, v_id_3687_, v_____do__lift_3821__boxed_3691_, v___y_3689_);
lean_dec(v___y_3689_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3695_, lean_object* v_ch_3696_, lean_object* v_res_x3f_3697_){
_start:
{
if (lean_obj_tag(v_res_x3f_3697_) == 0)
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
lean_dec_ref(v_ch_3696_);
lean_dec_ref(v_waiter_3695_);
v___x_3699_ = lean_box(0);
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
return v___x_3700_;
}
else
{
lean_object* v_val_3701_; uint8_t v___x_3702_; 
v_val_3701_ = lean_ctor_get(v_res_x3f_3697_, 0);
v___x_3702_ = lean_unbox(v_val_3701_);
if (v___x_3702_ == 0)
{
lean_object* v___f_3703_; lean_object* v___x_3704_; 
lean_dec_ref(v_ch_3696_);
v___f_3703_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3704_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3695_, v___f_3703_);
lean_dec_ref(v_waiter_3695_);
return v___x_3704_;
}
else
{
lean_object* v___x_3705_; 
v___x_3705_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3696_, v_waiter_3695_);
return v___x_3705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3706_, lean_object* v_ch_3707_, lean_object* v_res_x3f_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3706_, v_ch_3707_, v_res_x3f_3708_);
lean_dec(v_res_x3f_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3711_, lean_object* v_waiter_3712_){
_start:
{
lean_object* v_state_3714_; lean_object* v_id_3715_; lean_object* v___f_3716_; lean_object* v___f_3717_; lean_object* v___f_3718_; lean_object* v___x_3719_; 
v_state_3714_ = lean_ctor_get(v_ch_3711_, 0);
lean_inc_ref(v_state_3714_);
v_id_3715_ = lean_ctor_get(v_ch_3711_, 1);
lean_inc_n(v_id_3715_, 2);
lean_inc_ref(v_waiter_3712_);
v___f_3716_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3716_, 0, v_waiter_3712_);
lean_closure_set(v___f_3716_, 1, v_ch_3711_);
v___f_3717_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3717_, 0, v_waiter_3712_);
lean_closure_set(v___f_3717_, 1, v___f_3716_);
lean_closure_set(v___f_3717_, 2, v_id_3715_);
v___f_3718_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3718_, 0, v_id_3715_);
lean_closure_set(v___f_3718_, 1, v___f_3717_);
v___x_3719_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3714_, v___f_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3720_, lean_object* v_waiter_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3720_, v_waiter_3721_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3724_, lean_object* v_ch_3725_, lean_object* v_waiter_3726_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3725_, v_waiter_3726_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3729_, lean_object* v_ch_3730_, lean_object* v_waiter_3731_, lean_object* v_a_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3729_, v_ch_3730_, v_waiter_3731_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3734_, lean_object* v_receiverId_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3735_, v_a_3736_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3739_, lean_object* v_receiverId_3740_, lean_object* v_a_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3739_, v_receiverId_3740_, v_a_3741_);
lean_dec(v_a_3741_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3744_, lean_object* v_x_3745_){
_start:
{
if (lean_obj_tag(v_x_3745_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3755_; 
v_a_3747_ = lean_ctor_get(v_x_3745_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v_x_3745_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3749_ = v_x_3745_;
v_isShared_3750_ = v_isSharedCheck_3755_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v_x_3745_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3755_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3747_);
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
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3768_; 
v_a_3756_ = lean_ctor_get(v_x_3745_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_x_3745_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3758_ = v_x_3745_;
v_isShared_3759_ = v_isSharedCheck_3768_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v_x_3745_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3768_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v_capacity_3760_; lean_object* v_buffer_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3765_; 
v_capacity_3760_ = lean_ctor_get(v_a_3756_, 2);
lean_inc(v_capacity_3760_);
v_buffer_3761_ = lean_ctor_get(v_a_3756_, 4);
lean_inc_ref(v_buffer_3761_);
lean_dec(v_a_3756_);
v___x_3762_ = lean_nat_mod(v_place_3744_, v_capacity_3760_);
lean_dec(v_capacity_3760_);
v___x_3763_ = lean_array_fget(v_buffer_3761_, v___x_3762_);
lean_dec(v___x_3762_);
lean_dec_ref(v_buffer_3761_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3763_);
v___x_3765_ = v___x_3758_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3763_);
v___x_3765_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
return v___x_3766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3769_, lean_object* v_x_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3769_, v_x_3770_);
lean_dec(v_place_3769_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v___f_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___f_3776_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3776_, 0, v_place_3773_);
v___x_3777_ = lean_unsigned_to_nat(0u);
v___x_3778_ = 0;
v___x_3779_ = lean_st_ref_get(v_a_3774_);
v___x_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
v___x_3782_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3777_, v___x_3778_, v___x_3781_, v___f_3776_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3783_, lean_object* v_a_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3783_, v_a_3784_);
lean_dec(v_a_3784_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3787_, lean_object* v_place_3788_, lean_object* v_a_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3788_, v_a_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3792_, lean_object* v_place_3793_, lean_object* v_a_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3792_, v_place_3793_, v_a_3794_);
lean_dec(v_a_3794_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v___y_3797_){
_start:
{
if (lean_obj_tag(v___y_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
v_a_3798_ = lean_ctor_get(v___y_3797_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___y_3797_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___y_3797_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___y_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
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
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3814_; 
v_a_3806_ = lean_ctor_get(v___y_3797_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___y_3797_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3808_ = v___y_3797_;
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___y_3797_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3814_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v_fst_3810_; lean_object* v___x_3812_; 
v_fst_3810_ = lean_ctor_get(v_a_3806_, 0);
lean_inc(v_fst_3810_);
lean_dec(v_a_3806_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v_fst_3810_);
v___x_3812_ = v___x_3808_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_fst_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_mutex_3815_, lean_object* v_x_3816_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = lean_io_basemutex_unlock(v_mutex_3815_);
v___x_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_3821_, lean_object* v_x_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_mutex_3821_, v_x_3822_);
lean_dec(v_x_3822_);
lean_dec(v_mutex_3821_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_k_3825_, lean_object* v_ref_3826_, lean_object* v_x_3827_){
_start:
{
if (lean_obj_tag(v_x_3827_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3837_; 
lean_dec(v_ref_3826_);
lean_dec_ref(v_k_3825_);
v_a_3829_ = lean_ctor_get(v_x_3827_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_x_3827_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3831_ = v_x_3827_;
v_isShared_3832_ = v_isSharedCheck_3837_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v_x_3827_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3837_;
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
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
return v___x_3835_;
}
}
}
else
{
lean_object* v___x_3838_; 
lean_dec_ref_known(v_x_3827_, 1);
v___x_3838_ = lean_apply_2(v_k_3825_, v_ref_3826_, lean_box(0));
return v___x_3838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_k_3839_, lean_object* v_ref_3840_, lean_object* v_x_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_k_3839_, v_ref_3840_, v_x_3841_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v_mutex_3844_, lean_object* v___f_3845_){
_start:
{
lean_object* v___x_3847_; uint8_t v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3847_ = lean_unsigned_to_nat(0u);
v___x_3848_ = 0;
v___x_3849_ = lean_io_basemutex_lock(v_mutex_3844_);
v___x_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
v___x_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
v___x_3852_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3847_, v___x_3848_, v___x_3851_, v___f_3845_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_3853_, lean_object* v___f_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(v_mutex_3853_, v___f_3854_);
lean_dec(v_mutex_3853_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_3858_, lean_object* v_k_3859_){
_start:
{
lean_object* v_ref_3861_; lean_object* v_mutex_3862_; lean_object* v___f_3863_; lean_object* v___f_3864_; lean_object* v___f_3865_; lean_object* v___f_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___y_3871_; 
v_ref_3861_ = lean_ctor_get(v_mutex_3858_, 0);
lean_inc(v_ref_3861_);
v_mutex_3862_ = lean_ctor_get(v_mutex_3858_, 1);
lean_inc_n(v_mutex_3862_, 2);
lean_dec_ref(v_mutex_3858_);
v___f_3863_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___f_3864_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3864_, 0, v_mutex_3862_);
v___f_3865_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3865_, 0, v_k_3859_);
lean_closure_set(v___f_3865_, 1, v_ref_3861_);
v___f_3866_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3866_, 0, v_mutex_3862_);
lean_closure_set(v___f_3866_, 1, v___f_3865_);
v___x_3867_ = lean_unsigned_to_nat(0u);
v___x_3868_ = 0;
v___x_3869_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_3866_, v___f_3864_, v___x_3867_, v___x_3868_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3873_; 
v_a_3873_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3869_, 1);
if (lean_obj_tag(v_a_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
v_a_3874_ = lean_ctor_get(v_a_3873_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v_a_3873_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v_a_3873_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v_a_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
v___y_3871_ = v___x_3879_;
goto v___jp_3870_;
}
}
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3890_; 
v_a_3882_ = lean_ctor_get(v_a_3873_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_a_3873_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3884_ = v_a_3873_;
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v_a_3873_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v_fst_3886_; lean_object* v___x_3888_; 
v_fst_3886_ = lean_ctor_get(v_a_3882_, 0);
lean_inc(v_fst_3886_);
lean_dec(v_a_3882_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v_fst_3886_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_fst_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
v___y_3871_ = v___x_3888_;
goto v___jp_3870_;
}
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3899_; 
v_a_3891_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3893_ = v___x_3869_;
v_isShared_3894_ = v_isSharedCheck_3899_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3869_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3899_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; lean_object* v___x_3897_; 
v___x_3895_ = lean_task_map(v___f_3863_, v_a_3891_, v___x_3867_, v___x_3868_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3895_);
v___x_3897_ = v___x_3893_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
v___jp_3870_:
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v___y_3871_);
return v___x_3872_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_3900_, lean_object* v_k_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3900_, v_k_3901_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_3904_, lean_object* v_00_u03b2_3905_, lean_object* v_mutex_3906_, lean_object* v_k_3907_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3906_, v_k_3907_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_3910_, lean_object* v_00_u03b2_3911_, lean_object* v_mutex_3912_, lean_object* v_k_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_3910_, v_00_u03b2_3911_, v_mutex_3912_, v_k_3913_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_3920_, lean_object* v_capacity_3921_, lean_object* v_size_3922_, lean_object* v_buffer_3923_, lean_object* v_write_3924_, lean_object* v_read_3925_, lean_object* v_receivers_3926_, lean_object* v_nextId_3927_, uint8_t v_closed_3928_, lean_object* v_pos_3929_, lean_object* v___y_3930_, lean_object* v_x_3931_){
_start:
{
if (lean_obj_tag(v_x_3931_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3941_; 
lean_dec(v_pos_3929_);
lean_dec(v_nextId_3927_);
lean_dec(v_receivers_3926_);
lean_dec(v_read_3925_);
lean_dec(v_write_3924_);
lean_dec_ref(v_buffer_3923_);
lean_dec(v_size_3922_);
lean_dec(v_capacity_3921_);
lean_dec_ref(v_producers_3920_);
v_a_3933_ = lean_ctor_get(v_x_3931_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_x_3931_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3935_ = v_x_3931_;
v_isShared_3936_ = v_isSharedCheck_3941_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v_x_3931_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3941_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
return v___x_3939_;
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v_a_3942_ = lean_ctor_get(v_x_3931_, 0);
lean_inc(v_a_3942_);
lean_dec_ref_known(v_x_3931_, 1);
v___x_3943_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3943_, 0, v_producers_3920_);
lean_ctor_set(v___x_3943_, 1, v_a_3942_);
lean_ctor_set(v___x_3943_, 2, v_capacity_3921_);
lean_ctor_set(v___x_3943_, 3, v_size_3922_);
lean_ctor_set(v___x_3943_, 4, v_buffer_3923_);
lean_ctor_set(v___x_3943_, 5, v_write_3924_);
lean_ctor_set(v___x_3943_, 6, v_read_3925_);
lean_ctor_set(v___x_3943_, 7, v_receivers_3926_);
lean_ctor_set(v___x_3943_, 8, v_nextId_3927_);
lean_ctor_set(v___x_3943_, 9, v_pos_3929_);
lean_ctor_set_uint8(v___x_3943_, sizeof(void*)*10, v_closed_3928_);
v___x_3944_ = lean_st_ref_swap(v___y_3930_, v___x_3943_);
lean_dec(v___x_3944_);
v___x_3945_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_3945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_3946_, lean_object* v_capacity_3947_, lean_object* v_size_3948_, lean_object* v_buffer_3949_, lean_object* v_write_3950_, lean_object* v_read_3951_, lean_object* v_receivers_3952_, lean_object* v_nextId_3953_, lean_object* v_closed_3954_, lean_object* v_pos_3955_, lean_object* v___y_3956_, lean_object* v_x_3957_, lean_object* v___y_3958_){
_start:
{
uint8_t v_closed_boxed_3959_; lean_object* v_res_3960_; 
v_closed_boxed_3959_ = lean_unbox(v_closed_3954_);
v_res_3960_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_3946_, v_capacity_3947_, v_size_3948_, v_buffer_3949_, v_write_3950_, v_read_3951_, v_receivers_3952_, v_nextId_3953_, v_closed_boxed_3959_, v_pos_3955_, v___y_3956_, v_x_3957_);
lean_dec(v___y_3956_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_3961_){
_start:
{
if (lean_obj_tag(v_x_3961_) == 0)
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v_x_3961_);
return v___x_3963_;
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3973_; 
v_a_3964_ = lean_ctor_get(v_x_3961_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_x_3961_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3966_ = v_x_3961_;
v_isShared_3967_ = v_isSharedCheck_3973_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v_x_3961_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3973_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3970_; 
v___x_3968_ = l_List_reverse___redArg(v_a_3964_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3968_);
v___x_3970_ = v___x_3966_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3968_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_3974_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_3977_, lean_object* v___x_3978_, lean_object* v_x_3979_){
_start:
{
if (lean_obj_tag(v_x_3979_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v___x_3978_);
lean_dec(v_a_3977_);
v_a_3981_ = lean_ctor_get(v_x_3979_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v_x_3979_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3983_ = v_x_3979_;
v_isShared_3984_ = v_isSharedCheck_3989_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v_x_3979_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3989_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3987_; 
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
return v___x_3987_;
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4006_; 
v_a_3990_ = lean_ctor_get(v_x_3979_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_x_3979_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3992_ = v_x_3979_;
v_isShared_3993_ = v_isSharedCheck_4006_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v_x_3979_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4006_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
uint8_t v___x_3994_; 
v___x_3994_ = l_List_isEmpty___redArg(v_a_3977_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
lean_dec(v___x_3978_);
v___x_3995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3995_, 0, v_a_3990_);
lean_ctor_set(v___x_3995_, 1, v_a_3977_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_3995_);
v___x_3997_ = v___x_3992_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4003_; 
lean_dec(v_a_3977_);
v___x_4000_ = l_List_reverse___redArg(v_a_3990_);
v___x_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3978_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_4001_);
v___x_4003_ = v___x_3992_;
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
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_4007_, lean_object* v___x_4008_, lean_object* v_x_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_4007_, v___x_4008_, v_x_4009_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_4012_){
_start:
{
uint8_t v___y_4015_; 
if (lean_obj_tag(v_x_4012_) == 0)
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4019_, 0, v_x_4012_);
return v___x_4019_;
}
else
{
lean_object* v_a_4020_; uint8_t v___x_4021_; 
v_a_4020_ = lean_ctor_get(v_x_4012_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v_x_4012_, 1);
v___x_4021_ = lean_unbox(v_a_4020_);
lean_dec(v_a_4020_);
if (v___x_4021_ == 0)
{
uint8_t v___x_4022_; 
v___x_4022_ = 1;
v___y_4015_ = v___x_4022_;
goto v___jp_4014_;
}
else
{
uint8_t v___x_4023_; 
v___x_4023_ = 0;
v___y_4015_ = v___x_4023_;
goto v___jp_4014_;
}
}
v___jp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = lean_box(v___y_4015_);
v___x_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4024_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_4027_, lean_object* v_x_4028_, lean_object* v_head_4029_, lean_object* v_x_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4027_, v_x_4028_, v_head_4029_, v_x_4030_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_4039_, lean_object* v_x_4040_){
_start:
{
if (lean_obj_tag(v_x_4039_) == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4042_, 0, v_x_4040_);
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
return v___x_4043_;
}
else
{
lean_object* v_head_4044_; lean_object* v_tail_4045_; lean_object* v_waiter_4046_; lean_object* v___f_4047_; lean_object* v___x_4048_; uint8_t v___x_4049_; 
v_head_4044_ = lean_ctor_get(v_x_4039_, 0);
lean_inc(v_head_4044_);
v_tail_4045_ = lean_ctor_get(v_x_4039_, 1);
lean_inc(v_tail_4045_);
lean_dec_ref_known(v_x_4039_, 2);
v_waiter_4046_ = lean_ctor_get(v_head_4044_, 1);
lean_inc(v_waiter_4046_);
v___f_4047_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4047_, 0, v_tail_4045_);
lean_closure_set(v___f_4047_, 1, v_x_4040_);
lean_closure_set(v___f_4047_, 2, v_head_4044_);
v___x_4048_ = lean_unsigned_to_nat(0u);
v___x_4049_ = 0;
if (lean_obj_tag(v_waiter_4046_) == 0)
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v___x_4051_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4048_, v___x_4049_, v___x_4050_, v___f_4047_);
return v___x_4051_;
}
else
{
lean_object* v_val_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4065_; 
v_val_4052_ = lean_ctor_get(v_waiter_4046_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_waiter_4046_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4054_ = v_waiter_4046_;
v_isShared_4055_ = v_isSharedCheck_4065_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_val_4052_);
lean_dec(v_waiter_4046_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4065_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v_finished_4056_; lean_object* v___f_4057_; lean_object* v___x_4058_; lean_object* v___x_4060_; 
v_finished_4056_ = lean_ctor_get(v_val_4052_, 0);
lean_inc(v_finished_4056_);
lean_dec(v_val_4052_);
v___f_4057_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
v___x_4058_ = lean_st_ref_get(v_finished_4056_);
lean_dec(v_finished_4056_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 0, v___x_4058_);
v___x_4060_ = v___x_4054_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
v___x_4062_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4048_, v___x_4049_, v___x_4061_, v___f_4057_);
v___x_4063_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4048_, v___x_4049_, v___x_4062_, v___f_4047_);
return v___x_4063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_4066_, lean_object* v_x_4067_, lean_object* v_head_4068_, lean_object* v_x_4069_){
_start:
{
if (lean_obj_tag(v_x_4069_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4079_; 
lean_dec_ref(v_head_4068_);
lean_dec(v_x_4067_);
lean_dec(v_tail_4066_);
v_a_4071_ = lean_ctor_get(v_x_4069_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_x_4069_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4073_ = v_x_4069_;
v_isShared_4074_ = v_isSharedCheck_4079_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v_x_4069_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4079_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
}
else
{
lean_object* v_a_4080_; uint8_t v___x_4081_; 
v_a_4080_ = lean_ctor_get(v_x_4069_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v_x_4069_, 1);
v___x_4081_ = lean_unbox(v_a_4080_);
lean_dec(v_a_4080_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; 
lean_dec_ref(v_head_4068_);
v___x_4082_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4066_, v_x_4067_);
return v___x_4082_;
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4083_, 0, v_head_4068_);
lean_ctor_set(v___x_4083_, 1, v_x_4067_);
v___x_4084_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4066_, v___x_4083_);
return v___x_4084_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_4085_, lean_object* v_x_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4085_, v_x_4086_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v___x_4089_, lean_object* v_eList_4090_, lean_object* v___f_4091_, lean_object* v_x_4092_){
_start:
{
if (lean_obj_tag(v_x_4092_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4102_; 
lean_dec_ref(v___f_4091_);
lean_dec(v_eList_4090_);
lean_dec(v___x_4089_);
v_a_4094_ = lean_ctor_get(v_x_4092_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_x_4092_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4096_ = v_x_4092_;
v_isShared_4097_ = v_isSharedCheck_4102_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v_x_4092_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4102_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
}
}
else
{
lean_object* v_a_4103_; lean_object* v___f_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v_a_4103_ = lean_ctor_get(v_x_4092_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v_x_4092_, 1);
lean_inc(v___x_4089_);
v___f_4104_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4104_, 0, v_a_4103_);
lean_closure_set(v___f_4104_, 1, v___x_4089_);
v___x_4105_ = lean_unsigned_to_nat(0u);
v___x_4106_ = 0;
v___x_4107_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4090_, v___x_4089_);
v___x_4108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4105_, v___x_4106_, v___x_4107_, v___f_4091_);
v___x_4109_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4105_, v___x_4106_, v___x_4108_, v___f_4104_);
return v___x_4109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v___x_4110_, lean_object* v_eList_4111_, lean_object* v___f_4112_, lean_object* v_x_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v___x_4110_, v_eList_4111_, v___f_4112_, v_x_4113_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_eList_4120_; lean_object* v_dList_4121_; lean_object* v___f_4122_; lean_object* v___x_4123_; lean_object* v___f_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v_eList_4120_ = lean_ctor_get(v_q_4117_, 0);
lean_inc(v_eList_4120_);
v_dList_4121_ = lean_ctor_get(v_q_4117_, 1);
lean_inc(v_dList_4121_);
lean_dec_ref(v_q_4117_);
v___f_4122_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4123_ = lean_box(0);
v___f_4124_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4124_, 0, v___x_4123_);
lean_closure_set(v___f_4124_, 1, v_eList_4120_);
lean_closure_set(v___f_4124_, 2, v___f_4122_);
v___x_4125_ = lean_unsigned_to_nat(0u);
v___x_4126_ = 0;
v___x_4127_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4121_, v___x_4123_);
v___x_4128_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4125_, v___x_4126_, v___x_4127_, v___f_4122_);
v___x_4129_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4125_, v___x_4126_, v___x_4128_, v___f_4124_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4130_, v___y_4131_);
lean_dec(v___y_4131_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4134_, lean_object* v_x_4135_){
_start:
{
if (lean_obj_tag(v_x_4135_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4145_; 
v_a_4137_ = lean_ctor_get(v_x_4135_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_x_4135_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4139_ = v_x_4135_;
v_isShared_4140_ = v_isSharedCheck_4145_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v_x_4135_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4145_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4143_; 
v___x_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
return v___x_4143_;
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v_producers_4147_; lean_object* v_waiters_4148_; lean_object* v_capacity_4149_; lean_object* v_size_4150_; lean_object* v_buffer_4151_; lean_object* v_write_4152_; lean_object* v_read_4153_; lean_object* v_receivers_4154_; lean_object* v_nextId_4155_; uint8_t v_closed_4156_; lean_object* v_pos_4157_; lean_object* v___x_4158_; lean_object* v___f_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v_a_4146_ = lean_ctor_get(v_x_4135_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v_x_4135_, 1);
v_producers_4147_ = lean_ctor_get(v_a_4146_, 0);
lean_inc_ref(v_producers_4147_);
v_waiters_4148_ = lean_ctor_get(v_a_4146_, 1);
lean_inc_ref(v_waiters_4148_);
v_capacity_4149_ = lean_ctor_get(v_a_4146_, 2);
lean_inc(v_capacity_4149_);
v_size_4150_ = lean_ctor_get(v_a_4146_, 3);
lean_inc(v_size_4150_);
v_buffer_4151_ = lean_ctor_get(v_a_4146_, 4);
lean_inc_ref(v_buffer_4151_);
v_write_4152_ = lean_ctor_get(v_a_4146_, 5);
lean_inc(v_write_4152_);
v_read_4153_ = lean_ctor_get(v_a_4146_, 6);
lean_inc(v_read_4153_);
v_receivers_4154_ = lean_ctor_get(v_a_4146_, 7);
lean_inc(v_receivers_4154_);
v_nextId_4155_ = lean_ctor_get(v_a_4146_, 8);
lean_inc(v_nextId_4155_);
v_closed_4156_ = lean_ctor_get_uint8(v_a_4146_, sizeof(void*)*10);
v_pos_4157_ = lean_ctor_get(v_a_4146_, 9);
lean_inc(v_pos_4157_);
lean_dec(v_a_4146_);
v___x_4158_ = lean_box(v_closed_4156_);
lean_inc(v___y_4134_);
v___f_4159_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4159_, 0, v_producers_4147_);
lean_closure_set(v___f_4159_, 1, v_capacity_4149_);
lean_closure_set(v___f_4159_, 2, v_size_4150_);
lean_closure_set(v___f_4159_, 3, v_buffer_4151_);
lean_closure_set(v___f_4159_, 4, v_write_4152_);
lean_closure_set(v___f_4159_, 5, v_read_4153_);
lean_closure_set(v___f_4159_, 6, v_receivers_4154_);
lean_closure_set(v___f_4159_, 7, v_nextId_4155_);
lean_closure_set(v___f_4159_, 8, v___x_4158_);
lean_closure_set(v___f_4159_, 9, v_pos_4157_);
lean_closure_set(v___f_4159_, 10, v___y_4134_);
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = 0;
v___x_4162_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4148_, v___y_4134_);
v___x_4163_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4160_, v___x_4161_, v___x_4162_, v___f_4159_);
return v___x_4163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4164_, lean_object* v_x_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4164_, v_x_4165_);
lean_dec(v___y_4164_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4168_){
_start:
{
lean_object* v___f_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_inc(v___y_4168_);
v___f_4170_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4170_, 0, v___y_4168_);
v___x_4171_ = lean_unsigned_to_nat(0u);
v___x_4172_ = 0;
v___x_4173_ = lean_st_ref_get(v___y_4168_);
v___x_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
v___x_4176_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4171_, v___x_4172_, v___x_4175_, v___f_4170_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4177_);
lean_dec(v___y_4177_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4180_, lean_object* v_waiter_4181_){
_start:
{
lean_object* v_val_4184_; lean_object* v___x_4186_; 
v___x_4186_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4180_, v_waiter_4181_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4186_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
lean_ctor_set_tag(v___x_4189_, 1);
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
v_val_4184_ = v___x_4192_;
goto v___jp_4183_;
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
v_a_4195_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4186_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4186_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set_tag(v___x_4197_, 0);
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
v_val_4184_ = v___x_4200_;
goto v___jp_4183_;
}
}
}
v___jp_4183_:
{
lean_object* v___x_4185_; 
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v_val_4184_);
return v___x_4185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4203_, lean_object* v_waiter_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4203_, v_waiter_4204_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4207_){
_start:
{
if (lean_obj_tag(v_x_4207_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4217_; 
v_a_4209_ = lean_ctor_get(v_x_4207_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v_x_4207_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4211_ = v_x_4207_;
v_isShared_4212_ = v_isSharedCheck_4217_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v_x_4207_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4217_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
lean_object* v___x_4215_; 
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
return v___x_4215_;
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4227_; 
v_a_4218_ = lean_ctor_get(v_x_4207_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v_x_4207_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4220_ = v_x_4207_;
v_isShared_4221_ = v_isSharedCheck_4227_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v_x_4207_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4227_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4222_, 0, v_a_4218_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4222_);
v___x_4224_ = v___x_4220_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
return v___x_4225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4231_, lean_object* v_x_4232_){
_start:
{
if (lean_obj_tag(v_x_4232_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v_x_4231_);
v_a_4234_ = lean_ctor_get(v_x_4232_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_x_4232_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4236_ = v_x_4232_;
v_isShared_4237_ = v_isSharedCheck_4242_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v_x_4232_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4242_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4234_);
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
else
{
lean_object* v___x_4243_; 
lean_dec_ref_known(v_x_4232_, 1);
v___x_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4243_, 0, v_x_4231_);
return v___x_4243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4244_, lean_object* v_x_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4244_, v_x_4245_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4250_, lean_object* v_receiverId_4251_, lean_object* v_receivers_4252_, lean_object* v_x_4253_){
_start:
{
if (lean_obj_tag(v_x_4253_) == 0)
{
lean_object* v___x_4255_; 
lean_dec(v_receivers_4252_);
lean_dec(v_receiverId_4251_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v_x_4253_);
return v___x_4255_;
}
else
{
lean_object* v_a_4256_; 
v_a_4256_ = lean_ctor_get(v_x_4253_, 0);
if (lean_obj_tag(v_a_4256_) == 1)
{
lean_object* v___f_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___x_4260_; lean_object* v_producers_4261_; lean_object* v_waiters_4262_; lean_object* v_capacity_4263_; lean_object* v_size_4264_; lean_object* v_buffer_4265_; lean_object* v_write_4266_; lean_object* v_read_4267_; lean_object* v_nextId_4268_; uint8_t v_closed_4269_; lean_object* v_pos_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4281_; 
v___f_4257_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4257_, 0, v_x_4253_);
v___x_4258_ = lean_unsigned_to_nat(0u);
v___x_4259_ = 0;
v___x_4260_ = lean_st_ref_take(v_a_4250_);
v_producers_4261_ = lean_ctor_get(v___x_4260_, 0);
v_waiters_4262_ = lean_ctor_get(v___x_4260_, 1);
v_capacity_4263_ = lean_ctor_get(v___x_4260_, 2);
v_size_4264_ = lean_ctor_get(v___x_4260_, 3);
v_buffer_4265_ = lean_ctor_get(v___x_4260_, 4);
v_write_4266_ = lean_ctor_get(v___x_4260_, 5);
v_read_4267_ = lean_ctor_get(v___x_4260_, 6);
v_nextId_4268_ = lean_ctor_get(v___x_4260_, 8);
v_closed_4269_ = lean_ctor_get_uint8(v___x_4260_, sizeof(void*)*10);
v_pos_4270_ = lean_ctor_get(v___x_4260_, 9);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4281_ == 0)
{
lean_object* v_unused_4282_; 
v_unused_4282_ = lean_ctor_get(v___x_4260_, 7);
lean_dec(v_unused_4282_);
v___x_4272_ = v___x_4260_;
v_isShared_4273_ = v_isSharedCheck_4281_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_pos_4270_);
lean_inc(v_nextId_4268_);
lean_inc(v_read_4267_);
lean_inc(v_write_4266_);
lean_inc(v_buffer_4265_);
lean_inc(v_size_4264_);
lean_inc(v_capacity_4263_);
lean_inc(v_waiters_4262_);
lean_inc(v_producers_4261_);
lean_dec(v___x_4260_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4281_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4274_; lean_object* v___x_4276_; 
v___x_4274_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4251_, v_receivers_4252_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 7, v___x_4274_);
v___x_4276_ = v___x_4272_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_producers_4261_);
lean_ctor_set(v_reuseFailAlloc_4280_, 1, v_waiters_4262_);
lean_ctor_set(v_reuseFailAlloc_4280_, 2, v_capacity_4263_);
lean_ctor_set(v_reuseFailAlloc_4280_, 3, v_size_4264_);
lean_ctor_set(v_reuseFailAlloc_4280_, 4, v_buffer_4265_);
lean_ctor_set(v_reuseFailAlloc_4280_, 5, v_write_4266_);
lean_ctor_set(v_reuseFailAlloc_4280_, 6, v_read_4267_);
lean_ctor_set(v_reuseFailAlloc_4280_, 7, v___x_4274_);
lean_ctor_set(v_reuseFailAlloc_4280_, 8, v_nextId_4268_);
lean_ctor_set(v_reuseFailAlloc_4280_, 9, v_pos_4270_);
lean_ctor_set_uint8(v_reuseFailAlloc_4280_, sizeof(void*)*10, v_closed_4269_);
v___x_4276_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4277_ = lean_st_ref_put(v_a_4250_, v___x_4276_);
v___x_4278_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4279_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4258_, v___x_4259_, v___x_4278_, v___f_4257_);
return v___x_4279_;
}
}
}
else
{
lean_object* v___x_4283_; 
lean_dec_ref_known(v_x_4253_, 1);
lean_dec(v_receivers_4252_);
lean_dec(v_receiverId_4251_);
v___x_4283_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4283_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4284_, lean_object* v_receiverId_4285_, lean_object* v_receivers_4286_, lean_object* v_x_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4284_, v_receiverId_4285_, v_receivers_4286_, v_x_4287_);
lean_dec(v_a_4284_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4290_){
_start:
{
if (lean_obj_tag(v_x_4290_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4300_; 
v_a_4292_ = lean_ctor_get(v_x_4290_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_x_4290_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4294_ = v_x_4290_;
v_isShared_4295_ = v_isSharedCheck_4300_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v_x_4290_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4300_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4292_);
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
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4313_; 
v_a_4301_ = lean_ctor_get(v_x_4290_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v_x_4290_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4303_ = v_x_4290_;
v_isShared_4304_ = v_isSharedCheck_4313_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v_x_4290_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4313_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v_size_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4310_; 
v_size_4305_ = lean_ctor_get(v_a_4301_, 3);
lean_inc(v_size_4305_);
lean_dec(v_a_4301_);
v___x_4306_ = lean_unsigned_to_nat(0u);
v___x_4307_ = lean_nat_dec_eq(v_size_4305_, v___x_4306_);
lean_dec(v_size_4305_);
v___x_4308_ = lean_box(v___x_4307_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 0, v___x_4308_);
v___x_4310_ = v___x_4303_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4308_);
v___x_4310_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v___x_4311_; 
v___x_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
return v___x_4311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4314_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4318_){
_start:
{
lean_object* v___f_4320_; lean_object* v___x_4321_; uint8_t v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___f_4320_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4321_ = lean_unsigned_to_nat(0u);
v___x_4322_ = 0;
v___x_4323_ = lean_st_ref_get(v_a_4318_);
v___x_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
v___x_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
v___x_4326_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4321_, v___x_4322_, v___x_4325_, v___f_4320_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4327_);
lean_dec(v_a_4327_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4330_, lean_object* v_next_4331_){
_start:
{
lean_object* v___x_4333_; lean_object* v_fst_4335_; lean_object* v_snd_4336_; lean_object* v_value_4340_; lean_object* v_pos_4341_; lean_object* v_remaining_4342_; uint8_t v___x_4343_; 
v___x_4333_ = lean_st_ref_take(v_slot_4330_);
v_value_4340_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_value_4340_);
v_pos_4341_ = lean_ctor_get(v___x_4333_, 1);
lean_inc(v_pos_4341_);
v_remaining_4342_ = lean_ctor_get(v___x_4333_, 2);
lean_inc(v_remaining_4342_);
v___x_4343_ = lean_nat_dec_eq(v_next_4331_, v_pos_4341_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
lean_dec(v_remaining_4342_);
lean_dec(v_pos_4341_);
lean_dec(v_value_4340_);
v___x_4344_ = lean_box(0);
v___x_4345_ = lean_box(v___x_4343_);
v___x_4346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4344_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
v_fst_4335_ = v___x_4346_;
v_snd_4336_ = v___x_4333_;
goto v___jp_4334_;
}
else
{
lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4365_; 
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4365_ == 0)
{
lean_object* v_unused_4366_; lean_object* v_unused_4367_; lean_object* v_unused_4368_; 
v_unused_4366_ = lean_ctor_get(v___x_4333_, 2);
lean_dec(v_unused_4366_);
v_unused_4367_ = lean_ctor_get(v___x_4333_, 1);
lean_dec(v_unused_4367_);
v_unused_4368_ = lean_ctor_get(v___x_4333_, 0);
lean_dec(v_unused_4368_);
v___x_4348_ = v___x_4333_;
v_isShared_4349_ = v_isSharedCheck_4365_;
goto v_resetjp_4347_;
}
else
{
lean_dec(v___x_4333_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4365_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4350_; uint8_t v___x_4351_; 
v___x_4350_ = lean_unsigned_to_nat(1u);
v___x_4351_ = lean_nat_dec_eq(v_remaining_4342_, v___x_4350_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4352_ = lean_box(v___x_4351_);
lean_inc(v_value_4340_);
v___x_4353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4353_, 0, v_value_4340_);
lean_ctor_set(v___x_4353_, 1, v___x_4352_);
v___x_4354_ = lean_nat_sub(v_remaining_4342_, v___x_4350_);
lean_dec(v_remaining_4342_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 2, v___x_4354_);
v___x_4356_ = v___x_4348_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_value_4340_);
lean_ctor_set(v_reuseFailAlloc_4357_, 1, v_pos_4341_);
lean_ctor_set(v_reuseFailAlloc_4357_, 2, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
v_fst_4335_ = v___x_4353_;
v_snd_4336_ = v___x_4356_;
goto v___jp_4334_;
}
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
lean_dec(v_remaining_4342_);
v___x_4358_ = lean_box(v___x_4343_);
v___x_4359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4359_, 0, v_value_4340_);
lean_ctor_set(v___x_4359_, 1, v___x_4358_);
v___x_4360_ = lean_box(0);
v___x_4361_ = lean_unsigned_to_nat(0u);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 2, v___x_4361_);
lean_ctor_set(v___x_4348_, 0, v___x_4360_);
v___x_4363_ = v___x_4348_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v_pos_4341_);
lean_ctor_set(v_reuseFailAlloc_4364_, 2, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
v_fst_4335_ = v___x_4359_;
v_snd_4336_ = v___x_4363_;
goto v___jp_4334_;
}
}
}
}
v___jp_4334_:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4337_ = lean_st_ref_put(v_slot_4330_, v_snd_4336_);
v___x_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4338_, 0, v_fst_4335_);
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
return v___x_4339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4369_, lean_object* v_next_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4369_, v_next_4370_);
lean_dec(v_next_4370_);
lean_dec(v_slot_4369_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4373_, uint8_t v_a_4374_, lean_object* v___f_4375_, lean_object* v_x_4376_){
_start:
{
if (lean_obj_tag(v_x_4376_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4386_; 
lean_dec_ref(v___f_4375_);
v_a_4378_ = lean_ctor_get(v_x_4376_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v_x_4376_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4380_ = v_x_4376_;
v_isShared_4381_ = v_isSharedCheck_4386_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v_x_4376_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4386_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
return v___x_4384_;
}
}
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; 
v_a_4387_ = lean_ctor_get(v_x_4376_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v_x_4376_, 1);
v___x_4388_ = lean_unsigned_to_nat(0u);
v___x_4389_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4387_, v_next_4373_);
lean_dec(v_a_4387_);
v___x_4390_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4388_, v_a_4374_, v___x_4389_, v___f_4375_);
return v___x_4390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4391_, lean_object* v_a_4392_, lean_object* v___f_4393_, lean_object* v_x_4394_, lean_object* v___y_4395_){
_start:
{
uint8_t v_a_12032__boxed_4396_; lean_object* v_res_4397_; 
v_a_12032__boxed_4396_ = lean_unbox(v_a_4392_);
v_res_4397_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4391_, v_a_12032__boxed_4396_, v___f_4393_, v_x_4394_);
lean_dec(v_next_4391_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4398_, lean_object* v___f_4399_, lean_object* v_____r_4400_, lean_object* v_st_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4404_ = lean_unsigned_to_nat(0u);
v___x_4405_ = lean_st_ref_swap(v___y_4402_, v_st_4401_);
lean_dec(v___x_4405_);
v___x_4406_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4407_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4404_, v_a_4398_, v___x_4406_, v___f_4399_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4408_, lean_object* v___f_4409_, lean_object* v_____r_4410_, lean_object* v_st_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v_a_12074__boxed_4414_; lean_object* v_res_4415_; 
v_a_12074__boxed_4414_ = lean_unbox(v_a_4408_);
v_res_4415_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_12074__boxed_4414_, v___f_4409_, v_____r_4410_, v_st_4411_, v___y_4412_);
lean_dec(v___y_4412_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4416_, lean_object* v_waiters_4417_, lean_object* v_capacity_4418_, lean_object* v_size_4419_, lean_object* v_buffer_4420_, lean_object* v_write_4421_, lean_object* v_read_4422_, lean_object* v_receivers_4423_, lean_object* v_nextId_4424_, uint8_t v_closed_4425_, lean_object* v_pos_4426_, lean_object* v___f_4427_, lean_object* v_a_4428_, lean_object* v_x_4429_){
_start:
{
if (lean_obj_tag(v_x_4429_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4439_; 
lean_dec_ref(v___f_4427_);
lean_dec(v_pos_4426_);
lean_dec(v_nextId_4424_);
lean_dec(v_receivers_4423_);
lean_dec(v_read_4422_);
lean_dec(v_write_4421_);
lean_dec_ref(v_buffer_4420_);
lean_dec(v_size_4419_);
lean_dec(v_capacity_4418_);
lean_dec_ref(v_waiters_4417_);
lean_dec_ref(v_snd_4416_);
v_a_4431_ = lean_ctor_get(v_x_4429_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_x_4429_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4433_ = v_x_4429_;
v_isShared_4434_ = v_isSharedCheck_4439_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v_x_4429_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4439_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4436_);
return v___x_4437_;
}
}
}
else
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
lean_dec_ref_known(v_x_4429_, 1);
v___x_4440_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4440_, 0, v_snd_4416_);
lean_ctor_set(v___x_4440_, 1, v_waiters_4417_);
lean_ctor_set(v___x_4440_, 2, v_capacity_4418_);
lean_ctor_set(v___x_4440_, 3, v_size_4419_);
lean_ctor_set(v___x_4440_, 4, v_buffer_4420_);
lean_ctor_set(v___x_4440_, 5, v_write_4421_);
lean_ctor_set(v___x_4440_, 6, v_read_4422_);
lean_ctor_set(v___x_4440_, 7, v_receivers_4423_);
lean_ctor_set(v___x_4440_, 8, v_nextId_4424_);
lean_ctor_set(v___x_4440_, 9, v_pos_4426_);
lean_ctor_set_uint8(v___x_4440_, sizeof(void*)*10, v_closed_4425_);
v___x_4441_ = lean_box(0);
lean_inc(v_a_4428_);
v___x_4442_ = lean_apply_4(v___f_4427_, v___x_4441_, v___x_4440_, v_a_4428_, lean_box(0));
return v___x_4442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4443_, lean_object* v_waiters_4444_, lean_object* v_capacity_4445_, lean_object* v_size_4446_, lean_object* v_buffer_4447_, lean_object* v_write_4448_, lean_object* v_read_4449_, lean_object* v_receivers_4450_, lean_object* v_nextId_4451_, lean_object* v_closed_4452_, lean_object* v_pos_4453_, lean_object* v___f_4454_, lean_object* v_a_4455_, lean_object* v_x_4456_, lean_object* v___y_4457_){
_start:
{
uint8_t v_closed_boxed_4458_; lean_object* v_res_4459_; 
v_closed_boxed_4458_ = lean_unbox(v_closed_4452_);
v_res_4459_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4443_, v_waiters_4444_, v_capacity_4445_, v_size_4446_, v_buffer_4447_, v_write_4448_, v_read_4449_, v_receivers_4450_, v_nextId_4451_, v_closed_boxed_4458_, v_pos_4453_, v___f_4454_, v_a_4455_, v_x_4456_);
lean_dec(v_a_4455_);
return v_res_4459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4460_, lean_object* v_x_4461_){
_start:
{
if (lean_obj_tag(v_x_4461_) == 0)
{
lean_object* v_a_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4471_; 
lean_dec(v_fst_4460_);
v_a_4463_ = lean_ctor_get(v_x_4461_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v_x_4461_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4465_ = v_x_4461_;
v_isShared_4466_ = v_isSharedCheck_4471_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_a_4463_);
lean_dec(v_x_4461_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4471_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4466_ == 0)
{
v___x_4468_ = v___x_4465_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4463_);
v___x_4468_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4469_; 
v___x_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4468_);
return v___x_4469_;
}
}
}
else
{
lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4479_; 
v_isSharedCheck_4479_ = !lean_is_exclusive(v_x_4461_);
if (v_isSharedCheck_4479_ == 0)
{
lean_object* v_unused_4480_; 
v_unused_4480_ = lean_ctor_get(v_x_4461_, 0);
lean_dec(v_unused_4480_);
v___x_4473_ = v_x_4461_;
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
else
{
lean_dec(v_x_4461_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4479_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v_fst_4460_);
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_fst_4460_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4481_, lean_object* v_x_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4481_, v_x_4482_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, uint8_t v___x_4488_, lean_object* v_x_4489_){
_start:
{
if (lean_obj_tag(v_x_4489_) == 0)
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4499_; 
lean_dec_ref(v_a_4486_);
v_a_4491_ = lean_ctor_get(v_x_4489_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_x_4489_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4493_ = v_x_4489_;
v_isShared_4494_ = v_isSharedCheck_4499_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v_x_4489_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4499_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4497_; 
v___x_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
return v___x_4497_;
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4547_; 
v_a_4500_ = lean_ctor_get(v_x_4489_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v_x_4489_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4502_ = v_x_4489_;
v_isShared_4503_ = v_isSharedCheck_4547_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v_x_4489_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4547_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v_fst_4504_; 
v_fst_4504_ = lean_ctor_get(v_a_4500_, 0);
lean_inc(v_fst_4504_);
if (lean_obj_tag(v_fst_4504_) == 1)
{
lean_object* v_snd_4505_; lean_object* v___f_4506_; lean_object* v___x_4507_; lean_object* v___f_4508_; uint8_t v___x_4509_; 
v_snd_4505_ = lean_ctor_get(v_a_4500_, 1);
lean_inc(v_snd_4505_);
lean_dec(v_a_4500_);
v___f_4506_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4506_, 0, v_fst_4504_);
v___x_4507_ = lean_box(v_a_4485_);
lean_inc_ref(v___f_4506_);
v___f_4508_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4508_, 0, v___x_4507_);
lean_closure_set(v___f_4508_, 1, v___f_4506_);
v___x_4509_ = lean_unbox(v_snd_4505_);
lean_dec(v_snd_4505_);
if (v___x_4509_ == 0)
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec_ref(v___f_4508_);
lean_del_object(v___x_4502_);
v___x_4510_ = lean_box(0);
v___x_4511_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4485_, v___f_4506_, v___x_4510_, v_a_4486_, v_a_4487_);
return v___x_4511_;
}
else
{
lean_object* v___x_4512_; lean_object* v_producers_4513_; lean_object* v_waiters_4514_; lean_object* v_capacity_4515_; lean_object* v_size_4516_; lean_object* v_buffer_4517_; lean_object* v_write_4518_; lean_object* v_read_4519_; lean_object* v_receivers_4520_; lean_object* v_nextId_4521_; uint8_t v_closed_4522_; lean_object* v_pos_4523_; lean_object* v___x_4524_; 
v___x_4512_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4486_);
v_producers_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc_ref(v_producers_4513_);
v_waiters_4514_ = lean_ctor_get(v___x_4512_, 1);
lean_inc_ref(v_waiters_4514_);
v_capacity_4515_ = lean_ctor_get(v___x_4512_, 2);
lean_inc(v_capacity_4515_);
v_size_4516_ = lean_ctor_get(v___x_4512_, 3);
lean_inc(v_size_4516_);
v_buffer_4517_ = lean_ctor_get(v___x_4512_, 4);
lean_inc_ref(v_buffer_4517_);
v_write_4518_ = lean_ctor_get(v___x_4512_, 5);
lean_inc(v_write_4518_);
v_read_4519_ = lean_ctor_get(v___x_4512_, 6);
lean_inc(v_read_4519_);
v_receivers_4520_ = lean_ctor_get(v___x_4512_, 7);
lean_inc(v_receivers_4520_);
v_nextId_4521_ = lean_ctor_get(v___x_4512_, 8);
lean_inc(v_nextId_4521_);
v_closed_4522_ = lean_ctor_get_uint8(v___x_4512_, sizeof(void*)*10);
v_pos_4523_ = lean_ctor_get(v___x_4512_, 9);
lean_inc(v_pos_4523_);
v___x_4524_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4513_);
if (lean_obj_tag(v___x_4524_) == 1)
{
lean_object* v_val_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4543_; 
lean_dec_ref(v___x_4512_);
lean_dec_ref(v___f_4506_);
v_val_4525_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4527_ = v___x_4524_;
v_isShared_4528_ = v_isSharedCheck_4543_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_val_4525_);
lean_dec(v___x_4524_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4543_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v_fst_4529_; lean_object* v_snd_4530_; lean_object* v___x_4531_; lean_object* v___f_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4537_; 
v_fst_4529_ = lean_ctor_get(v_val_4525_, 0);
lean_inc(v_fst_4529_);
v_snd_4530_ = lean_ctor_get(v_val_4525_, 1);
lean_inc(v_snd_4530_);
lean_dec(v_val_4525_);
v___x_4531_ = lean_box(v_closed_4522_);
lean_inc(v_a_4487_);
v___f_4532_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4532_, 0, v_snd_4530_);
lean_closure_set(v___f_4532_, 1, v_waiters_4514_);
lean_closure_set(v___f_4532_, 2, v_capacity_4515_);
lean_closure_set(v___f_4532_, 3, v_size_4516_);
lean_closure_set(v___f_4532_, 4, v_buffer_4517_);
lean_closure_set(v___f_4532_, 5, v_write_4518_);
lean_closure_set(v___f_4532_, 6, v_read_4519_);
lean_closure_set(v___f_4532_, 7, v_receivers_4520_);
lean_closure_set(v___f_4532_, 8, v_nextId_4521_);
lean_closure_set(v___f_4532_, 9, v___x_4531_);
lean_closure_set(v___f_4532_, 10, v_pos_4523_);
lean_closure_set(v___f_4532_, 11, v___f_4508_);
lean_closure_set(v___f_4532_, 12, v_a_4487_);
v___x_4533_ = lean_unsigned_to_nat(0u);
v___x_4534_ = lean_box(v___x_4488_);
v___x_4535_ = lean_io_promise_resolve(v___x_4534_, v_fst_4529_);
lean_dec(v_fst_4529_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v___x_4535_);
v___x_4537_ = v___x_4502_;
goto v_reusejp_4536_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4535_);
v___x_4537_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4536_;
}
v_reusejp_4536_:
{
lean_object* v___x_4539_; 
if (v_isShared_4528_ == 0)
{
lean_ctor_set_tag(v___x_4527_, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4537_);
v___x_4539_ = v___x_4527_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4537_);
v___x_4539_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4540_; 
v___x_4540_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4533_, v_a_4485_, v___x_4539_, v___f_4532_);
return v___x_4540_;
}
}
}
}
else
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
lean_dec(v___x_4524_);
lean_dec(v_pos_4523_);
lean_dec(v_nextId_4521_);
lean_dec(v_receivers_4520_);
lean_dec(v_read_4519_);
lean_dec(v_write_4518_);
lean_dec_ref(v_buffer_4517_);
lean_dec(v_size_4516_);
lean_dec(v_capacity_4515_);
lean_dec_ref(v_waiters_4514_);
lean_dec_ref(v___f_4508_);
lean_del_object(v___x_4502_);
v___x_4544_ = lean_box(0);
v___x_4545_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4485_, v___f_4506_, v___x_4544_, v___x_4512_, v_a_4487_);
return v___x_4545_;
}
}
}
else
{
lean_object* v___x_4546_; 
lean_dec(v_fst_4504_);
lean_del_object(v___x_4502_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4486_);
v___x_4546_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v___x_4551_, lean_object* v_x_4552_, lean_object* v___y_4553_){
_start:
{
uint8_t v_a_12186__boxed_4554_; uint8_t v___x_12188__boxed_4555_; lean_object* v_res_4556_; 
v_a_12186__boxed_4554_ = lean_unbox(v_a_4548_);
v___x_12188__boxed_4555_ = lean_unbox(v___x_4551_);
v_res_4556_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12186__boxed_4554_, v_a_4549_, v_a_4550_, v___x_12188__boxed_4555_, v_x_4552_);
lean_dec(v_a_4550_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_next_4559_, lean_object* v_x_4560_){
_start:
{
if (lean_obj_tag(v_x_4560_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_next_4559_);
lean_dec_ref(v_a_4557_);
v_a_4562_ = lean_ctor_get(v_x_4560_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v_x_4560_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4564_ = v_x_4560_;
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v_x_4560_);
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
lean_object* v_a_4571_; uint8_t v___x_4572_; 
v_a_4571_ = lean_ctor_get(v_x_4560_, 0);
lean_inc(v_a_4571_);
lean_dec_ref_known(v_x_4560_, 1);
v___x_4572_ = lean_unbox(v_a_4571_);
if (v___x_4572_ == 0)
{
lean_object* v_capacity_4573_; uint8_t v___x_4574_; lean_object* v___x_4575_; lean_object* v___f_4576_; lean_object* v___f_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; uint8_t v___x_4581_; lean_object* v___x_4582_; 
v_capacity_4573_ = lean_ctor_get(v_a_4557_, 2);
lean_inc(v_capacity_4573_);
v___x_4574_ = 1;
v___x_4575_ = lean_box(v___x_4574_);
lean_inc(v_a_4558_);
lean_inc_n(v_a_4571_, 2);
v___f_4576_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4576_, 0, v_a_4571_);
lean_closure_set(v___f_4576_, 1, v_a_4557_);
lean_closure_set(v___f_4576_, 2, v_a_4558_);
lean_closure_set(v___f_4576_, 3, v___x_4575_);
lean_inc(v_next_4559_);
v___f_4577_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4577_, 0, v_next_4559_);
lean_closure_set(v___f_4577_, 1, v_a_4571_);
lean_closure_set(v___f_4577_, 2, v___f_4576_);
v___x_4578_ = lean_nat_mod(v_next_4559_, v_capacity_4573_);
lean_dec(v_capacity_4573_);
lean_dec(v_next_4559_);
v___x_4579_ = lean_unsigned_to_nat(0u);
v___x_4580_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4578_, v_a_4558_);
v___x_4581_ = lean_unbox(v_a_4571_);
lean_dec(v_a_4571_);
v___x_4582_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4579_, v___x_4581_, v___x_4580_, v___f_4577_);
return v___x_4582_;
}
else
{
lean_object* v___x_4583_; 
lean_dec(v_a_4571_);
lean_dec(v_next_4559_);
lean_dec_ref(v_a_4557_);
v___x_4583_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_next_4586_, lean_object* v_x_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4584_, v_a_4585_, v_next_4586_, v_x_4587_);
lean_dec(v_a_4585_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4590_, lean_object* v_next_4591_, lean_object* v_x_4592_){
_start:
{
if (lean_obj_tag(v_x_4592_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4602_; 
lean_dec(v_next_4591_);
v_a_4594_ = lean_ctor_get(v_x_4592_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v_x_4592_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4596_ = v_x_4592_;
v_isShared_4597_ = v_isSharedCheck_4602_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_a_4594_);
lean_dec(v_x_4592_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4602_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v___x_4599_; 
if (v_isShared_4597_ == 0)
{
v___x_4599_ = v___x_4596_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4594_);
v___x_4599_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
lean_object* v___x_4600_; 
v___x_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4599_);
return v___x_4600_;
}
}
}
else
{
lean_object* v_a_4603_; lean_object* v___f_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v_a_4603_ = lean_ctor_get(v_x_4592_, 0);
lean_inc(v_a_4603_);
lean_dec_ref_known(v_x_4592_, 1);
lean_inc(v_a_4590_);
v___f_4604_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4604_, 0, v_a_4603_);
lean_closure_set(v___f_4604_, 1, v_a_4590_);
lean_closure_set(v___f_4604_, 2, v_next_4591_);
v___x_4605_ = lean_unsigned_to_nat(0u);
v___x_4606_ = 0;
v___x_4607_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4590_);
v___x_4608_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4605_, v___x_4606_, v___x_4607_, v___f_4604_);
return v___x_4608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4609_, lean_object* v_next_4610_, lean_object* v_x_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4609_, v_next_4610_, v_x_4611_);
lean_dec(v_a_4609_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4614_, lean_object* v_a_4615_){
_start:
{
lean_object* v___f_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; 
lean_inc(v_a_4615_);
v___f_4617_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4617_, 0, v_a_4615_);
lean_closure_set(v___f_4617_, 1, v_next_4614_);
v___x_4618_ = lean_unsigned_to_nat(0u);
v___x_4619_ = 0;
v___x_4620_ = lean_st_ref_get(v_a_4615_);
v___x_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
v___x_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4621_);
v___x_4623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4618_, v___x_4619_, v___x_4622_, v___f_4617_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4624_, lean_object* v_a_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v_res_4627_; 
v_res_4627_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4624_, v_a_4625_);
lean_dec(v_a_4625_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4628_, lean_object* v_a_4629_, lean_object* v_x_4630_){
_start:
{
if (lean_obj_tag(v_x_4630_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4640_; 
lean_dec(v_receiverId_4628_);
v_a_4632_ = lean_ctor_get(v_x_4630_, 0);
v_isSharedCheck_4640_ = !lean_is_exclusive(v_x_4630_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4634_ = v_x_4630_;
v_isShared_4635_ = v_isSharedCheck_4640_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v_x_4630_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4640_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
lean_object* v___x_4638_; 
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
return v___x_4638_;
}
}
}
else
{
lean_object* v_a_4641_; lean_object* v_receivers_4642_; lean_object* v___x_4643_; 
v_a_4641_ = lean_ctor_get(v_x_4630_, 0);
lean_inc(v_a_4641_);
lean_dec_ref_known(v_x_4630_, 1);
v_receivers_4642_ = lean_ctor_get(v_a_4641_, 7);
lean_inc(v_receivers_4642_);
lean_dec(v_a_4641_);
v___x_4643_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4642_, v_receiverId_4628_);
if (lean_obj_tag(v___x_4643_) == 1)
{
lean_object* v_val_4644_; lean_object* v___f_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v_val_4644_ = lean_ctor_get(v___x_4643_, 0);
lean_inc(v_val_4644_);
lean_dec_ref_known(v___x_4643_, 1);
lean_inc(v_a_4629_);
v___f_4645_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4645_, 0, v_a_4629_);
lean_closure_set(v___f_4645_, 1, v_receiverId_4628_);
lean_closure_set(v___f_4645_, 2, v_receivers_4642_);
v___x_4646_ = lean_unsigned_to_nat(0u);
v___x_4647_ = 0;
v___x_4648_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4644_, v_a_4629_);
v___x_4649_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4646_, v___x_4647_, v___x_4648_, v___f_4645_);
return v___x_4649_;
}
else
{
lean_object* v___x_4650_; 
lean_dec(v___x_4643_);
lean_dec(v_receivers_4642_);
lean_dec(v_receiverId_4628_);
v___x_4650_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4650_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4651_, lean_object* v_a_4652_, lean_object* v_x_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4651_, v_a_4652_, v_x_4653_);
lean_dec(v_a_4652_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v___f_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
lean_inc(v_a_4657_);
v___f_4659_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4659_, 0, v_receiverId_4656_);
lean_closure_set(v___f_4659_, 1, v_a_4657_);
v___x_4660_ = lean_unsigned_to_nat(0u);
v___x_4661_ = 0;
v___x_4662_ = lean_st_ref_get(v_a_4657_);
v___x_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4662_);
v___x_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
v___x_4665_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4660_, v___x_4661_, v___x_4664_, v___f_4659_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4666_, lean_object* v_a_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4666_, v_a_4667_);
lean_dec(v_a_4667_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_id_4674_, lean_object* v___y_4675_, lean_object* v___f_4676_, lean_object* v_x_4677_){
_start:
{
if (lean_obj_tag(v_x_4677_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4687_; 
lean_dec_ref(v___f_4676_);
lean_dec(v_id_4674_);
v_a_4679_ = lean_ctor_get(v_x_4677_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_x_4677_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4681_ = v_x_4677_;
v_isShared_4682_ = v_isSharedCheck_4687_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v_x_4677_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4687_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
lean_object* v___x_4685_; 
v___x_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
return v___x_4685_;
}
}
}
else
{
lean_object* v_a_4688_; uint8_t v___x_4689_; 
v_a_4688_ = lean_ctor_get(v_x_4677_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v_x_4677_, 1);
v___x_4689_ = lean_unbox(v_a_4688_);
lean_dec(v_a_4688_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; 
lean_dec_ref(v___f_4676_);
lean_dec(v_id_4674_);
v___x_4690_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__1));
return v___x_4690_;
}
else
{
lean_object* v___x_4691_; uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4691_ = lean_unsigned_to_nat(0u);
v___x_4692_ = 0;
v___x_4693_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4674_, v___y_4675_);
v___x_4694_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4691_, v___x_4692_, v___x_4693_, v___f_4676_);
return v___x_4694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_id_4695_, lean_object* v___y_4696_, lean_object* v___f_4697_, lean_object* v_x_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_id_4695_, v___y_4696_, v___f_4697_, v_x_4698_);
lean_dec(v___y_4696_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v_val_4701_, lean_object* v_x_4702_){
_start:
{
if (lean_obj_tag(v_x_4702_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4712_; 
v_a_4704_ = lean_ctor_get(v_x_4702_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v_x_4702_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4706_ = v_x_4702_;
v_isShared_4707_ = v_isSharedCheck_4712_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v_x_4702_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4712_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
lean_object* v___x_4710_; 
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
return v___x_4710_;
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4724_; 
v_a_4713_ = lean_ctor_get(v_x_4702_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v_x_4702_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4715_ = v_x_4702_;
v_isShared_4716_ = v_isSharedCheck_4724_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v_x_4702_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4724_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v_pos_4717_; uint8_t v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4721_; 
v_pos_4717_ = lean_ctor_get(v_a_4713_, 1);
lean_inc(v_pos_4717_);
lean_dec(v_a_4713_);
v___x_4718_ = lean_nat_dec_eq(v_pos_4717_, v_val_4701_);
lean_dec(v_pos_4717_);
v___x_4719_ = lean_box(v___x_4718_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 0, v___x_4719_);
v___x_4721_ = v___x_4715_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; 
v___x_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4721_);
return v___x_4722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v_val_4725_, lean_object* v_x_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v_val_4725_, v_x_4726_);
lean_dec(v_val_4725_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v___x_4729_, uint8_t v_closed_4730_, lean_object* v___f_4731_, lean_object* v_x_4732_){
_start:
{
if (lean_obj_tag(v_x_4732_) == 0)
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4742_; 
lean_dec_ref(v___f_4731_);
lean_dec(v___x_4729_);
v_a_4734_ = lean_ctor_get(v_x_4732_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v_x_4732_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4736_ = v_x_4732_;
v_isShared_4737_ = v_isSharedCheck_4742_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v_x_4732_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4742_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4734_);
v___x_4739_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
lean_object* v___x_4740_; 
v___x_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
return v___x_4740_;
}
}
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4753_; 
v_a_4743_ = lean_ctor_get(v_x_4732_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_x_4732_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4745_ = v_x_4732_;
v_isShared_4746_ = v_isSharedCheck_4753_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v_x_4732_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4753_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4747_ = lean_st_ref_get(v_a_4743_);
lean_dec(v_a_4743_);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v___x_4747_);
v___x_4749_ = v___x_4745_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
v___x_4751_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4729_, v_closed_4730_, v___x_4750_, v___f_4731_);
return v___x_4751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v___x_4754_, lean_object* v_closed_4755_, lean_object* v___f_4756_, lean_object* v_x_4757_, lean_object* v___y_4758_){
_start:
{
uint8_t v_closed_boxed_4759_; lean_object* v_res_4760_; 
v_closed_boxed_4759_ = lean_unbox(v_closed_4755_);
v_res_4760_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v___x_4754_, v_closed_boxed_4759_, v___f_4756_, v_x_4757_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4761_, lean_object* v___x_4762_, lean_object* v___y_4763_, lean_object* v_x_4764_){
_start:
{
if (lean_obj_tag(v_x_4764_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4774_; 
lean_dec(v___x_4762_);
v_a_4766_ = lean_ctor_get(v_x_4764_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v_x_4764_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4768_ = v_x_4764_;
v_isShared_4769_ = v_isSharedCheck_4774_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v_x_4764_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4774_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4772_; 
v___x_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4813_; 
v_a_4775_ = lean_ctor_get(v_x_4764_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_x_4764_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4777_ = v_x_4764_;
v_isShared_4778_ = v_isSharedCheck_4813_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v_x_4764_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4813_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
uint8_t v_closed_4779_; 
v_closed_4779_ = lean_ctor_get_uint8(v_a_4775_, sizeof(void*)*10);
if (v_closed_4779_ == 0)
{
lean_object* v_capacity_4780_; lean_object* v_size_4781_; lean_object* v_receivers_4782_; lean_object* v___x_4783_; 
v_capacity_4780_ = lean_ctor_get(v_a_4775_, 2);
lean_inc(v_capacity_4780_);
v_size_4781_ = lean_ctor_get(v_a_4775_, 3);
lean_inc(v_size_4781_);
v_receivers_4782_ = lean_ctor_get(v_a_4775_, 7);
lean_inc(v_receivers_4782_);
lean_dec(v_a_4775_);
v___x_4783_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4782_, v_id_4761_);
lean_dec(v_receivers_4782_);
if (lean_obj_tag(v___x_4783_) == 1)
{
lean_object* v_val_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4802_; 
v_val_4784_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4786_ = v___x_4783_;
v_isShared_4787_ = v_isSharedCheck_4802_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_val_4784_);
lean_dec(v___x_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4802_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
uint8_t v___x_4788_; 
v___x_4788_ = lean_nat_dec_eq(v_size_4781_, v___x_4762_);
lean_dec(v_size_4781_);
if (v___x_4788_ == 0)
{
lean_object* v___f_4789_; lean_object* v___x_4790_; lean_object* v___f_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_del_object(v___x_4786_);
lean_del_object(v___x_4777_);
lean_inc(v_val_4784_);
v___f_4789_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4789_, 0, v_val_4784_);
v___x_4790_ = lean_box(v_closed_4779_);
lean_inc(v___x_4762_);
v___f_4791_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 5, 3);
lean_closure_set(v___f_4791_, 0, v___x_4762_);
lean_closure_set(v___f_4791_, 1, v___x_4790_);
lean_closure_set(v___f_4791_, 2, v___f_4789_);
v___x_4792_ = lean_nat_mod(v_val_4784_, v_capacity_4780_);
lean_dec(v_capacity_4780_);
lean_dec(v_val_4784_);
v___x_4793_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4792_, v___y_4763_);
v___x_4794_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4762_, v___x_4788_, v___x_4793_, v___f_4791_);
return v___x_4794_;
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4797_; 
lean_dec(v_val_4784_);
lean_dec(v_capacity_4780_);
lean_dec(v___x_4762_);
v___x_4795_ = lean_box(v_closed_4779_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4795_);
v___x_4797_ = v___x_4777_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4795_);
v___x_4797_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
lean_object* v___x_4799_; 
if (v_isShared_4787_ == 0)
{
lean_ctor_set_tag(v___x_4786_, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4797_);
v___x_4799_ = v___x_4786_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4797_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
}
}
else
{
lean_object* v___x_4803_; lean_object* v___x_4805_; 
lean_dec(v___x_4783_);
lean_dec(v_size_4781_);
lean_dec(v_capacity_4780_);
lean_dec(v___x_4762_);
v___x_4803_ = lean_box(v_closed_4779_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4803_);
v___x_4805_ = v___x_4777_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4803_);
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
lean_object* v___x_4808_; lean_object* v___x_4810_; 
lean_dec(v_a_4775_);
lean_dec(v___x_4762_);
v___x_4808_ = lean_box(v_closed_4779_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4808_);
v___x_4810_ = v___x_4777_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4808_);
v___x_4810_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
lean_object* v___x_4811_; 
v___x_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4811_, 0, v___x_4810_);
return v___x_4811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4814_, lean_object* v___x_4815_, lean_object* v___y_4816_, lean_object* v_x_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4814_, v___x_4815_, v___y_4816_, v_x_4817_);
lean_dec(v___y_4816_);
lean_dec(v_id_4814_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4820_, lean_object* v___f_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v___f_4824_; lean_object* v___x_4825_; lean_object* v___f_4826_; uint8_t v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
lean_inc_n(v___y_4822_, 2);
lean_inc(v_id_4820_);
v___f_4824_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4824_, 0, v_id_4820_);
lean_closure_set(v___f_4824_, 1, v___y_4822_);
lean_closure_set(v___f_4824_, 2, v___f_4821_);
v___x_4825_ = lean_unsigned_to_nat(0u);
v___f_4826_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4826_, 0, v_id_4820_);
lean_closure_set(v___f_4826_, 1, v___x_4825_);
lean_closure_set(v___f_4826_, 2, v___y_4822_);
v___x_4827_ = 0;
v___x_4828_ = lean_st_ref_get(v___y_4822_);
v___x_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
v___x_4830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4829_);
v___x_4831_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4825_, v___x_4827_, v___x_4830_, v___f_4826_);
v___x_4832_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4825_, v___x_4827_, v___x_4831_, v___f_4824_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4833_, lean_object* v___f_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4833_, v___f_4834_, v___y_4835_);
lean_dec(v___y_4835_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4840_){
_start:
{
lean_object* v_state_4841_; lean_object* v_id_4842_; lean_object* v___f_4843_; lean_object* v___f_4844_; lean_object* v___f_4845_; lean_object* v___f_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v_state_4841_ = lean_ctor_get(v_ch_4840_, 0);
lean_inc_ref_n(v_state_4841_, 2);
v_id_4842_ = lean_ctor_get(v_ch_4840_, 1);
lean_inc(v_id_4842_);
v___f_4843_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4844_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4844_, 0, v_ch_4840_);
v___f_4845_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4846_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4846_, 0, v_id_4842_);
lean_closure_set(v___f_4846_, 1, v___f_4845_);
v___x_4847_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4847_, 0, lean_box(0));
lean_closure_set(v___x_4847_, 1, lean_box(0));
lean_closure_set(v___x_4847_, 2, v_state_4841_);
lean_closure_set(v___x_4847_, 3, v___f_4846_);
v___x_4848_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4848_, 0, lean_box(0));
lean_closure_set(v___x_4848_, 1, lean_box(0));
lean_closure_set(v___x_4848_, 2, v_state_4841_);
lean_closure_set(v___x_4848_, 3, v___f_4843_);
v___x_4849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4847_);
lean_ctor_set(v___x_4849_, 1, v___f_4844_);
lean_ctor_set(v___x_4849_, 2, v___x_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4850_, lean_object* v_ch_4851_){
_start:
{
lean_object* v___x_4852_; 
v___x_4852_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4851_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4853_, lean_object* v_receiverId_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4854_, v_a_4855_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4858_, lean_object* v_receiverId_4859_, lean_object* v_a_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4858_, v_receiverId_4859_, v_a_4860_);
lean_dec(v_a_4860_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4863_, lean_object* v_q_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4864_, v___y_4865_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4868_, lean_object* v_q_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_){
_start:
{
lean_object* v_res_4872_; 
v_res_4872_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4868_, v_q_4869_, v___y_4870_);
lean_dec(v___y_4870_);
return v_res_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4873_, lean_object* v_slot_4874_, lean_object* v_next_4875_, lean_object* v_a_4876_){
_start:
{
lean_object* v___x_4878_; 
v___x_4878_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4874_, v_next_4875_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4879_, lean_object* v_slot_4880_, lean_object* v_next_4881_, lean_object* v_a_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4879_, v_slot_4880_, v_next_4881_, v_a_4882_);
lean_dec(v_a_4882_);
lean_dec(v_next_4881_);
lean_dec(v_slot_4880_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4885_, lean_object* v_a_4886_){
_start:
{
lean_object* v___x_4888_; 
v___x_4888_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4886_);
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4889_, lean_object* v_a_4890_, lean_object* v___y_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4889_, v_a_4890_);
lean_dec(v_a_4890_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4893_, lean_object* v_next_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4894_, v_a_4895_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4898_, lean_object* v_next_4899_, lean_object* v_a_4900_, lean_object* v___y_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4898_, v_next_4899_, v_a_4900_);
lean_dec(v_a_4900_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4903_, lean_object* v_x_4904_, lean_object* v_x_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v___x_4908_; 
v___x_4908_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4904_, v_x_4905_);
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4909_, lean_object* v_x_4910_, lean_object* v_x_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4909_, v_x_4910_, v_x_4911_, v___y_4912_);
lean_dec(v___y_4912_);
return v_res_4914_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4916_){
_start:
{
lean_object* v___x_4918_; 
v___x_4918_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4916_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4919_, lean_object* v_a_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l_Std_Broadcast_new___redArg(v_capacity_4919_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4922_, lean_object* v_capacity_4923_, lean_object* v_h_4924_){
_start:
{
lean_object* v___x_4926_; 
v___x_4926_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4923_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4927_, lean_object* v_capacity_4928_, lean_object* v_h_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Std_Broadcast_new(v_00_u03b1_4927_, v_capacity_4928_, v_h_4929_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4932_, lean_object* v_v_4933_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4932_, v_v_4933_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4936_, lean_object* v_v_4937_, lean_object* v_a_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_Std_Broadcast_trySend___redArg(v_ch_4936_, v_v_4937_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4940_, lean_object* v_ch_4941_, lean_object* v_v_4942_){
_start:
{
lean_object* v___x_4944_; 
v___x_4944_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4941_, v_v_4942_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4945_, lean_object* v_ch_4946_, lean_object* v_v_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Std_Broadcast_trySend(v_00_u03b1_4945_, v_ch_4946_, v_v_4947_);
return v_res_4949_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4950_){
_start:
{
lean_object* v___x_4952_; 
v___x_4952_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4950_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v_a_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4960_; 
v_a_4953_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4955_ = v___x_4952_;
v_isShared_4956_ = v_isSharedCheck_4960_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_a_4953_);
lean_dec(v___x_4952_);
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
v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
v_a_4961_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4952_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4952_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_4969_, lean_object* v_a_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l_Std_Broadcast_subscribe___redArg(v_ch_4969_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_4972_, lean_object* v_ch_4973_){
_start:
{
lean_object* v___x_4975_; 
v___x_4975_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4973_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4975_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4975_);
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
v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
v_a_4984_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4975_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4975_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_4992_, lean_object* v_ch_4993_, lean_object* v_a_4994_){
_start:
{
lean_object* v_res_4995_; 
v_res_4995_ = l_Std_Broadcast_subscribe(v_00_u03b1_4992_, v_ch_4993_);
return v_res_4995_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_4996_){
_start:
{
lean_object* v___x_4998_; 
v___x_4998_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_4996_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4998_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4998_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5024_; 
v_a_5007_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5009_ = v___x_4998_;
v_isShared_5010_ = v_isSharedCheck_5024_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_4998_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5024_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
uint8_t v___x_5011_; 
v___x_5011_ = lean_unbox(v_a_5007_);
lean_dec(v_a_5007_);
switch(v___x_5011_)
{
case 0:
{
lean_object* v___x_5012_; lean_object* v___x_5014_; 
v___x_5012_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 0, v___x_5012_);
v___x_5014_ = v___x_5009_;
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
case 1:
{
lean_object* v___x_5016_; lean_object* v___x_5018_; 
v___x_5016_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 0, v___x_5016_);
v___x_5018_ = v___x_5009_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_5016_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
default: 
{
lean_object* v___x_5020_; lean_object* v___x_5022_; 
v___x_5020_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 0, v___x_5020_);
v___x_5022_ = v___x_5009_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5020_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5025_, lean_object* v_a_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Std_Broadcast_close___redArg(v_ch_5025_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5028_, lean_object* v_ch_5029_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5029_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5039_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5039_ == 0)
{
v___x_5034_ = v___x_5031_;
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5031_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5039_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5037_; 
if (v_isShared_5035_ == 0)
{
v___x_5037_ = v___x_5034_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_a_5032_);
v___x_5037_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
return v___x_5037_;
}
}
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5057_; 
v_a_5040_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5042_ = v___x_5031_;
v_isShared_5043_ = v_isSharedCheck_5057_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5031_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5057_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
uint8_t v___x_5044_; 
v___x_5044_ = lean_unbox(v_a_5040_);
lean_dec(v_a_5040_);
switch(v___x_5044_)
{
case 0:
{
lean_object* v___x_5045_; lean_object* v___x_5047_; 
v___x_5045_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5045_);
v___x_5047_ = v___x_5042_;
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
case 1:
{
lean_object* v___x_5049_; lean_object* v___x_5051_; 
v___x_5049_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5049_);
v___x_5051_ = v___x_5042_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v___x_5049_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
default: 
{
lean_object* v___x_5053_; lean_object* v___x_5055_; 
v___x_5053_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5053_);
v___x_5055_ = v___x_5042_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5053_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5058_, lean_object* v_ch_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Std_Broadcast_close(v_00_u03b1_5058_, v_ch_5059_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5062_){
_start:
{
lean_object* v___y_5065_; 
if (lean_obj_tag(v_x_5062_) == 0)
{
lean_object* v_a_5069_; uint8_t v___x_5070_; 
v_a_5069_ = lean_ctor_get(v_x_5062_, 0);
lean_inc(v_a_5069_);
lean_dec_ref_known(v_x_5062_, 1);
v___x_5070_ = lean_unbox(v_a_5069_);
lean_dec(v_a_5069_);
switch(v___x_5070_)
{
case 0:
{
lean_object* v___x_5071_; 
v___x_5071_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5065_ = v___x_5071_;
goto v___jp_5064_;
}
case 1:
{
lean_object* v___x_5072_; 
v___x_5072_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5065_ = v___x_5072_;
goto v___jp_5064_;
}
default: 
{
lean_object* v___x_5073_; 
v___x_5073_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5065_ = v___x_5073_;
goto v___jp_5064_;
}
}
}
else
{
lean_object* v_a_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5082_; 
v_a_5074_ = lean_ctor_get(v_x_5062_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v_x_5062_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5076_ = v_x_5062_;
v_isShared_5077_ = v_isSharedCheck_5082_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_a_5074_);
lean_dec(v_x_5062_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5082_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5079_; 
if (v_isShared_5077_ == 0)
{
v___x_5079_ = v___x_5076_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5074_);
v___x_5079_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
lean_object* v___x_5080_; 
v___x_5080_ = lean_task_pure(v___x_5079_);
return v___x_5080_;
}
}
}
v___jp_5064_:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
lean_inc_ref(v___y_5065_);
v___x_5066_ = lean_mk_io_user_error(v___y_5065_);
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
v___x_5068_ = lean_task_pure(v___x_5067_);
return v___x_5068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5083_, lean_object* v___y_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5083_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5087_, lean_object* v_v_5088_){
_start:
{
lean_object* v___f_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; lean_object* v___x_5094_; 
v___f_5090_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5091_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5087_, v_v_5088_);
v___x_5092_ = lean_unsigned_to_nat(0u);
v___x_5093_ = 1;
v___x_5094_ = lean_io_bind_task(v___x_5091_, v___f_5090_, v___x_5092_, v___x_5093_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5095_, lean_object* v_v_5096_, lean_object* v_a_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l_Std_Broadcast_send___redArg(v_ch_5095_, v_v_5096_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5099_, lean_object* v_ch_5100_, lean_object* v_v_5101_){
_start:
{
lean_object* v___f_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; uint8_t v___x_5106_; lean_object* v___x_5107_; 
v___f_5103_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5104_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5100_, v_v_5101_);
v___x_5105_ = lean_unsigned_to_nat(0u);
v___x_5106_ = 1;
v___x_5107_ = lean_io_bind_task(v___x_5104_, v___f_5103_, v___x_5105_, v___x_5106_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5108_, lean_object* v_ch_5109_, lean_object* v_v_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Std_Broadcast_send(v_00_u03b1_5108_, v_ch_5109_, v_v_5110_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5113_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5113_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5116_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5119_, lean_object* v_ch_5120_){
_start:
{
lean_object* v___x_5122_; 
v___x_5122_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5120_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5123_, lean_object* v_ch_5124_, lean_object* v_a_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5123_, v_ch_5124_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5127_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5127_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5130_, lean_object* v_a_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5130_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5133_, lean_object* v_inst_5134_, lean_object* v_ch_5135_){
_start:
{
lean_object* v___x_5137_; 
v___x_5137_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5135_);
return v___x_5137_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5138_, lean_object* v_inst_5139_, lean_object* v_ch_5140_, lean_object* v_a_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5138_, v_inst_5139_, v_ch_5140_);
lean_dec(v_inst_5139_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5143_){
_start:
{
lean_object* v___x_5144_; 
v___x_5144_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5143_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5145_, lean_object* v_inst_5146_, lean_object* v_ch_5147_){
_start:
{
lean_object* v___x_5148_; 
v___x_5148_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5147_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5149_, lean_object* v_inst_5150_, lean_object* v_ch_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5149_, v_inst_5150_, v_ch_5151_);
lean_dec(v_inst_5150_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5153_){
_start:
{
lean_object* v___x_5155_; 
v___x_5155_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5153_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5156_, lean_object* v_a_5157_){
_start:
{
lean_object* v_res_5158_; 
v_res_5158_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5156_);
return v_res_5158_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5159_, lean_object* v_ch_5160_){
_start:
{
lean_object* v___x_5162_; 
v___x_5162_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5160_);
return v___x_5162_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5163_, lean_object* v_ch_5164_, lean_object* v_a_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5163_, v_ch_5164_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5167_, lean_object* v_ch_5168_, lean_object* v_prio_5169_){
_start:
{
lean_object* v___x_5171_; 
v___x_5171_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5167_, v_ch_5168_, v_prio_5169_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5172_, lean_object* v_ch_5173_, lean_object* v_prio_5174_, lean_object* v_a_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5172_, v_ch_5173_, v_prio_5174_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5177_, lean_object* v_f_5178_, lean_object* v_ch_5179_, lean_object* v_prio_5180_){
_start:
{
lean_object* v___x_5182_; 
v___x_5182_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5178_, v_ch_5179_, v_prio_5180_);
return v___x_5182_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5183_, lean_object* v_f_5184_, lean_object* v_ch_5185_, lean_object* v_prio_5186_, lean_object* v_a_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5183_, v_f_5184_, v_ch_5185_, v_prio_5186_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg(){
_start:
{
lean_object* v___x_5195_; 
v___x_5195_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__2));
return v___x_5195_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object* v___dummy_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
return v_res_5197_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5199_, lean_object* v_inst_5200_){
_start:
{
lean_object* v___x_5201_; 
v___x_5201_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5202_, lean_object* v_inst_5203_){
_start:
{
lean_object* v_res_5204_; 
v_res_5204_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5202_, v_inst_5203_);
lean_dec(v_inst_5203_);
return v_res_5204_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object* v_a_5205_){
_start:
{
lean_object* v___x_5206_; 
v___x_5206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5206_, 0, v_a_5205_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object* v___f_5207_, lean_object* v_x_5208_){
_start:
{
if (lean_obj_tag(v_x_5208_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5218_; 
lean_dec_ref(v___f_5207_);
v_a_5210_ = lean_ctor_get(v_x_5208_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v_x_5208_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5212_ = v_x_5208_;
v_isShared_5213_ = v_isSharedCheck_5218_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v_x_5208_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5218_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
lean_object* v___x_5216_; 
v___x_5216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5216_, 0, v___x_5215_);
return v___x_5216_;
}
}
}
else
{
lean_object* v_a_5219_; 
v_a_5219_ = lean_ctor_get(v_x_5208_, 0);
lean_inc(v_a_5219_);
lean_dec_ref_known(v_x_5208_, 1);
if (lean_obj_tag(v_a_5219_) == 0)
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5228_; 
lean_dec_ref(v___f_5207_);
v_a_5220_ = lean_ctor_get(v_a_5219_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v_a_5219_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5222_ = v_a_5219_;
v_isShared_5223_ = v_isSharedCheck_5228_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v_a_5219_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5228_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5226_; 
v___x_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5226_, 0, v___x_5225_);
return v___x_5226_;
}
}
}
else
{
lean_object* v_a_5229_; lean_object* v___x_5230_; uint8_t v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; 
v_a_5229_ = lean_ctor_get(v_a_5219_, 0);
lean_inc(v_a_5229_);
lean_dec_ref_known(v_a_5219_, 1);
v___x_5230_ = lean_unsigned_to_nat(0u);
v___x_5231_ = 0;
v___x_5232_ = lean_task_map(v___f_5207_, v_a_5229_, v___x_5230_, v___x_5231_);
v___x_5233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5232_);
return v___x_5233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5234_, lean_object* v_x_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_5234_, v_x_5235_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object* v___f_5238_, lean_object* v_receiver_5239_){
_start:
{
lean_object* v___x_5241_; uint8_t v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; 
v___x_5241_ = lean_unsigned_to_nat(0u);
v___x_5242_ = 0;
v___x_5243_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5239_);
v___x_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5244_, 0, v___x_5243_);
v___x_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5245_, 0, v___x_5244_);
v___x_5246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5246_, 0, v___x_5245_);
v___x_5247_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5241_, v___x_5242_, v___x_5246_, v___f_5238_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5248_, lean_object* v_receiver_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_5248_, v_receiver_5249_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg(){
_start:
{
lean_object* v___f_5258_; 
v___f_5258_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__2));
return v___f_5258_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object* v___dummy_5259_){
_start:
{
lean_object* v_res_5260_; 
v_res_5260_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
return v_res_5260_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5261_; 
v___x_5261_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5262_, lean_object* v_inst_5263_){
_start:
{
lean_object* v___x_5264_; 
v___x_5264_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0);
return v___x_5264_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5265_, lean_object* v_inst_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5265_, v_inst_5266_);
lean_dec(v_inst_5266_);
return v_res_5267_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v_a_5268_){
_start:
{
lean_object* v___x_5269_; 
v___x_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5269_, 0, v_a_5268_);
return v___x_5269_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v___f_5274_, lean_object* v_x_5275_){
_start:
{
if (lean_obj_tag(v_x_5275_) == 0)
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5285_; 
lean_dec_ref(v___f_5274_);
v_a_5277_ = lean_ctor_get(v_x_5275_, 0);
v_isSharedCheck_5285_ = !lean_is_exclusive(v_x_5275_);
if (v_isSharedCheck_5285_ == 0)
{
v___x_5279_ = v_x_5275_;
v_isShared_5280_ = v_isSharedCheck_5285_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v_x_5275_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5285_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5282_; 
if (v_isShared_5280_ == 0)
{
v___x_5282_ = v___x_5279_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v_a_5277_);
v___x_5282_ = v_reuseFailAlloc_5284_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
lean_object* v___x_5283_; 
v___x_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5283_, 0, v___x_5282_);
return v___x_5283_;
}
}
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; uint8_t v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; 
v_a_5286_ = lean_ctor_get(v_x_5275_, 0);
lean_inc(v_a_5286_);
lean_dec_ref_known(v_x_5275_, 1);
v___x_5287_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___closed__1));
v___x_5288_ = lean_unsigned_to_nat(0u);
v___x_5289_ = 0;
v___x_5290_ = lean_task_map(v___f_5274_, v_a_5286_, v___x_5288_, v___x_5289_);
v___x_5291_ = lean_task_map(v___x_5287_, v___x_5290_, v___x_5288_, v___x_5289_);
v___x_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5292_, 0, v___x_5291_);
return v___x_5292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5293_, lean_object* v_x_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(v___f_5293_, v_x_5294_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(lean_object* v___f_5297_, lean_object* v___f_5298_, lean_object* v_receiver_5299_, lean_object* v_x_5300_){
_start:
{
lean_object* v___x_5302_; uint8_t v___x_5303_; lean_object* v___x_5304_; uint8_t v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___x_5302_ = lean_unsigned_to_nat(0u);
v___x_5303_ = 0;
v___x_5304_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5299_, v_x_5300_);
v___x_5305_ = 1;
v___x_5306_ = lean_io_bind_task(v___x_5304_, v___f_5297_, v___x_5302_, v___x_5305_);
v___x_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5307_, 0, v___x_5306_);
v___x_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5307_);
v___x_5309_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5302_, v___x_5303_, v___x_5308_, v___f_5298_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object* v___f_5310_, lean_object* v___f_5311_, lean_object* v_receiver_5312_, lean_object* v_x_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(v___f_5310_, v___f_5311_, v_receiver_5312_, v_x_5313_);
return v_res_5315_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v_x_5316_){
_start:
{
lean_object* v___x_5318_; 
v___x_5318_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v_x_5319_, lean_object* v___y_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(v_x_5319_);
lean_dec_ref(v_x_5319_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(lean_object* v___f_5322_, lean_object* v_socket_5323_, lean_object* v_x_5324_, lean_object* v___y_5325_){
_start:
{
lean_object* v___x_5327_; 
v___x_5327_ = lean_apply_3(v___f_5322_, v_socket_5323_, v___y_5325_, lean_box(0));
return v___x_5327_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object* v___f_5328_, lean_object* v_socket_5329_, lean_object* v_x_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v_res_5333_; 
v_res_5333_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(v___f_5328_, v_socket_5329_, v_x_5330_, v___y_5331_);
return v_res_5333_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__5(lean_object* v___f_5334_, lean_object* v___x_5335_, lean_object* v_socket_5336_, lean_object* v_data_5337_){
_start:
{
lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; uint8_t v___x_5342_; 
v___x_5339_ = lean_unsigned_to_nat(0u);
v___x_5340_ = lean_array_get_size(v_data_5337_);
v___x_5341_ = lean_box(0);
v___x_5342_ = lean_nat_dec_lt(v___x_5339_, v___x_5340_);
if (v___x_5342_ == 0)
{
lean_object* v___x_5343_; 
lean_dec_ref(v_data_5337_);
lean_dec_ref(v_socket_5336_);
lean_dec_ref(v___x_5335_);
lean_dec_ref(v___f_5334_);
v___x_5343_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5343_;
}
else
{
lean_object* v___f_5344_; uint8_t v___x_5345_; 
v___f_5344_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5344_, 0, v___f_5334_);
lean_closure_set(v___f_5344_, 1, v_socket_5336_);
v___x_5345_ = lean_nat_dec_le(v___x_5340_, v___x_5340_);
if (v___x_5345_ == 0)
{
if (v___x_5342_ == 0)
{
lean_object* v___x_5346_; 
lean_dec_ref(v___f_5344_);
lean_dec_ref(v_data_5337_);
lean_dec_ref(v___x_5335_);
v___x_5346_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5346_;
}
else
{
size_t v___x_5347_; size_t v___x_5348_; lean_object* v___x_895__overap_5349_; lean_object* v___x_5350_; 
v___x_5347_ = ((size_t)0ULL);
v___x_5348_ = lean_usize_of_nat(v___x_5340_);
v___x_895__overap_5349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5335_, v___f_5344_, v_data_5337_, v___x_5347_, v___x_5348_, v___x_5341_);
v___x_5350_ = lean_apply_1(v___x_895__overap_5349_, lean_box(0));
return v___x_5350_;
}
}
else
{
size_t v___x_5351_; size_t v___x_5352_; lean_object* v___x_898__overap_5353_; lean_object* v___x_5354_; 
v___x_5351_ = ((size_t)0ULL);
v___x_5352_ = lean_usize_of_nat(v___x_5340_);
v___x_898__overap_5353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5335_, v___f_5344_, v_data_5337_, v___x_5351_, v___x_5352_, v___x_5341_);
v___x_5354_ = lean_apply_1(v___x_898__overap_5353_, lean_box(0));
return v___x_5354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__5___boxed(lean_object* v___f_5355_, lean_object* v___x_5356_, lean_object* v_socket_5357_, lean_object* v_data_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v_res_5360_; 
v_res_5360_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__5(v___f_5355_, v___x_5356_, v_socket_5357_, v_data_5358_);
return v_res_5360_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_5368_; 
v___x_5368_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_5368_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5(void){
_start:
{
lean_object* v___x_5369_; lean_object* v___f_5370_; lean_object* v___f_5371_; 
v___x_5369_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4);
v___f_5370_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5371_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__5___boxed), 5, 2);
lean_closure_set(v___f_5371_, 0, v___f_5370_);
lean_closure_set(v___f_5371_, 1, v___x_5369_);
return v___f_5371_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__6(void){
_start:
{
lean_object* v___f_5372_; lean_object* v___f_5373_; lean_object* v___f_5374_; lean_object* v___x_5375_; 
v___f_5372_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3));
v___f_5373_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5);
v___f_5374_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2));
v___x_5375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5375_, 0, v___f_5374_);
lean_ctor_set(v___x_5375_, 1, v___f_5373_);
lean_ctor_set(v___x_5375_, 2, v___f_5372_);
return v___x_5375_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_5377_; 
v___x_5377_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__6, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__6_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__6);
return v___x_5377_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_5378_){
_start:
{
lean_object* v_res_5379_; 
v_res_5379_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
return v_res_5379_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5380_; 
v___x_5380_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
return v___x_5380_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5381_, lean_object* v_inst_5382_){
_start:
{
lean_object* v___x_5383_; 
v___x_5383_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0);
return v___x_5383_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5384_, lean_object* v_inst_5385_){
_start:
{
lean_object* v_res_5386_; 
v_res_5386_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5384_, v_inst_5385_);
lean_dec(v_inst_5385_);
return v_res_5386_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5387_; 
v___x_5387_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5387_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5388_){
_start:
{
lean_object* v___x_5390_; 
v___x_5390_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5388_);
return v___x_5390_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5391_, lean_object* v_a_5392_){
_start:
{
lean_object* v_res_5393_; 
v_res_5393_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5391_);
return v_res_5393_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5394_, lean_object* v_capacity_5395_, lean_object* v_h_5396_){
_start:
{
lean_object* v___x_5398_; 
v___x_5398_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5395_);
return v___x_5398_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5399_, lean_object* v_capacity_5400_, lean_object* v_h_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5399_, v_capacity_5400_, v_h_5401_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5404_, lean_object* v_v_5405_){
_start:
{
lean_object* v___x_5407_; 
v___x_5407_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5404_, v_v_5405_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5408_, lean_object* v_v_5409_, lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5408_, v_v_5409_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5412_, lean_object* v_ch_5413_, lean_object* v_v_5414_){
_start:
{
lean_object* v___x_5416_; 
v___x_5416_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5413_, v_v_5414_);
return v___x_5416_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5417_, lean_object* v_ch_5418_, lean_object* v_v_5419_, lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5417_, v_ch_5418_, v_v_5419_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5423_, lean_object* v_v_5424_){
_start:
{
lean_object* v___f_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; uint8_t v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___f_5426_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5427_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5428_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5423_, v_v_5424_);
v___x_5429_ = lean_unsigned_to_nat(0u);
v___x_5430_ = 1;
v___x_5431_ = lean_io_bind_task(v___x_5428_, v___f_5426_, v___x_5429_, v___x_5430_);
v___x_5432_ = lean_io_wait(v___x_5431_);
v___x_5433_ = l_IO_ofExcept___redArg(v___x_5427_, v___x_5432_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5434_, lean_object* v_v_5435_, lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5434_, v_v_5435_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5438_, lean_object* v_ch_5439_, lean_object* v_v_5440_){
_start:
{
lean_object* v___f_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; uint8_t v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; 
v___f_5442_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5443_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5444_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5439_, v_v_5440_);
v___x_5445_ = lean_unsigned_to_nat(0u);
v___x_5446_ = 1;
v___x_5447_ = lean_io_bind_task(v___x_5444_, v___f_5442_, v___x_5445_, v___x_5446_);
v___x_5448_ = lean_io_wait(v___x_5447_);
v___x_5449_ = l_IO_ofExcept___redArg(v___x_5443_, v___x_5448_);
return v___x_5449_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5450_, lean_object* v_ch_5451_, lean_object* v_v_5452_, lean_object* v_a_5453_){
_start:
{
lean_object* v_res_5454_; 
v_res_5454_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5450_, v_ch_5451_, v_v_5452_);
return v_res_5454_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5455_){
_start:
{
lean_object* v___x_5457_; 
v___x_5457_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5458_, lean_object* v_a_5459_){
_start:
{
lean_object* v_res_5460_; 
v_res_5460_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5458_);
return v_res_5460_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5461_, lean_object* v_ch_5462_){
_start:
{
lean_object* v___x_5464_; 
v___x_5464_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5462_);
return v___x_5464_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5465_, lean_object* v_ch_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v_res_5468_; 
v_res_5468_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5465_, v_ch_5466_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5469_){
_start:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5469_);
v___x_5472_ = lean_io_wait(v___x_5471_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5473_, lean_object* v_a_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5473_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5476_, lean_object* v_inst_5477_, lean_object* v_ch_5478_){
_start:
{
lean_object* v___x_5480_; 
v___x_5480_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5478_);
return v___x_5480_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5481_, lean_object* v_inst_5482_, lean_object* v_ch_5483_, lean_object* v_a_5484_){
_start:
{
lean_object* v_res_5485_; 
v_res_5485_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5481_, v_inst_5482_, v_ch_5483_);
lean_dec(v_inst_5482_);
return v_res_5485_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5486_, lean_object* v_b_5487_, lean_object* v_f_5488_, lean_object* v_toBind_5489_, lean_object* v___f_5490_, lean_object* v_a_5491_){
_start:
{
if (lean_obj_tag(v_a_5491_) == 0)
{
lean_object* v___x_5492_; 
lean_dec(v___f_5490_);
lean_dec(v_toBind_5489_);
lean_dec(v_f_5488_);
v___x_5492_ = lean_apply_2(v_toPure_5486_, lean_box(0), v_b_5487_);
return v___x_5492_;
}
else
{
lean_object* v_val_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
lean_dec(v_toPure_5486_);
v_val_5493_ = lean_ctor_get(v_a_5491_, 0);
lean_inc(v_val_5493_);
lean_dec_ref_known(v_a_5491_, 1);
v___x_5494_ = lean_apply_2(v_f_5488_, v_val_5493_, v_b_5487_);
v___x_5495_ = lean_apply_4(v_toBind_5489_, lean_box(0), lean_box(0), v___x_5494_, v___f_5490_);
return v___x_5495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5496_, lean_object* v_inst_5497_, lean_object* v_inst_5498_, lean_object* v_ch_5499_, lean_object* v_f_5500_, lean_object* v_b_5501_){
_start:
{
lean_object* v_toApplicative_5502_; lean_object* v_toBind_5503_; lean_object* v_toPure_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___f_5507_; lean_object* v___f_5508_; lean_object* v___x_5509_; 
v_toApplicative_5502_ = lean_ctor_get(v_inst_5497_, 0);
v_toBind_5503_ = lean_ctor_get(v_inst_5497_, 1);
lean_inc_n(v_toBind_5503_, 2);
v_toPure_5504_ = lean_ctor_get(v_toApplicative_5502_, 1);
lean_inc_n(v_toPure_5504_, 2);
lean_inc_ref(v_ch_5499_);
lean_inc(v_inst_5496_);
v___x_5505_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5505_, 0, lean_box(0));
lean_closure_set(v___x_5505_, 1, v_inst_5496_);
lean_closure_set(v___x_5505_, 2, v_ch_5499_);
lean_inc(v_inst_5498_);
v___x_5506_ = lean_apply_2(v_inst_5498_, lean_box(0), v___x_5505_);
lean_inc(v_f_5500_);
v___f_5507_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5507_, 0, v_toPure_5504_);
lean_closure_set(v___f_5507_, 1, v_inst_5496_);
lean_closure_set(v___f_5507_, 2, v_inst_5497_);
lean_closure_set(v___f_5507_, 3, v_inst_5498_);
lean_closure_set(v___f_5507_, 4, v_ch_5499_);
lean_closure_set(v___f_5507_, 5, v_f_5500_);
v___f_5508_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5508_, 0, v_toPure_5504_);
lean_closure_set(v___f_5508_, 1, v_b_5501_);
lean_closure_set(v___f_5508_, 2, v_f_5500_);
lean_closure_set(v___f_5508_, 3, v_toBind_5503_);
lean_closure_set(v___f_5508_, 4, v___f_5507_);
v___x_5509_ = lean_apply_4(v_toBind_5503_, lean_box(0), lean_box(0), v___x_5506_, v___f_5508_);
return v___x_5509_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5510_, lean_object* v_inst_5511_, lean_object* v_inst_5512_, lean_object* v_inst_5513_, lean_object* v_ch_5514_, lean_object* v_f_5515_, lean_object* v_____do__lift_5516_){
_start:
{
if (lean_obj_tag(v_____do__lift_5516_) == 0)
{
lean_object* v_a_5517_; lean_object* v___x_5518_; 
lean_dec(v_f_5515_);
lean_dec_ref(v_ch_5514_);
lean_dec(v_inst_5513_);
lean_dec_ref(v_inst_5512_);
lean_dec(v_inst_5511_);
v_a_5517_ = lean_ctor_get(v_____do__lift_5516_, 0);
lean_inc(v_a_5517_);
lean_dec_ref_known(v_____do__lift_5516_, 1);
v___x_5518_ = lean_apply_2(v_toPure_5510_, lean_box(0), v_a_5517_);
return v___x_5518_;
}
else
{
lean_object* v_a_5519_; lean_object* v___x_5520_; 
lean_dec(v_toPure_5510_);
v_a_5519_ = lean_ctor_get(v_____do__lift_5516_, 0);
lean_inc(v_a_5519_);
lean_dec_ref_known(v_____do__lift_5516_, 1);
v___x_5520_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5511_, v_inst_5512_, v_inst_5513_, v_ch_5514_, v_f_5515_, v_a_5519_);
return v___x_5520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5521_, lean_object* v_m_5522_, lean_object* v_00_u03b2_5523_, lean_object* v_inst_5524_, lean_object* v_inst_5525_, lean_object* v_inst_5526_, lean_object* v_ch_5527_, lean_object* v_f_5528_, lean_object* v_b_5529_){
_start:
{
lean_object* v___x_5530_; 
v___x_5530_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5524_, v_inst_5525_, v_inst_5526_, v_ch_5527_, v_f_5528_, v_b_5529_);
return v___x_5530_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5531_, lean_object* v_inst_5532_, lean_object* v_inst_5533_, lean_object* v_00_u03b2_5534_, lean_object* v_ch_5535_, lean_object* v_b_5536_, lean_object* v_f_5537_){
_start:
{
lean_object* v___x_5538_; 
v___x_5538_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5531_, v_inst_5532_, v_inst_5533_, v_ch_5535_, v_f_5537_, v_b_5536_);
return v___x_5538_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5539_, lean_object* v_inst_5540_, lean_object* v_inst_5541_){
_start:
{
lean_object* v___f_5542_; 
v___f_5542_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5542_, 0, v_inst_5539_);
lean_closure_set(v___f_5542_, 1, v_inst_5540_);
lean_closure_set(v___f_5542_, 2, v_inst_5541_);
return v___f_5542_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5543_, lean_object* v_m_5544_, lean_object* v_inst_5545_, lean_object* v_inst_5546_, lean_object* v_inst_5547_){
_start:
{
lean_object* v___f_5548_; 
v___f_5548_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5548_, 0, v_inst_5545_);
lean_closure_set(v___f_5548_, 1, v_inst_5546_);
lean_closure_set(v___f_5548_, 2, v_inst_5547_);
return v___f_5548_;
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

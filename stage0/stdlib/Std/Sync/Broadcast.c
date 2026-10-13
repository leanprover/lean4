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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Broadcast_Error_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Broadcast_Error_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Broadcast_Error_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg(lean_object* v_closed_22_){
_start:
{
lean_inc(v_closed_22_);
return v_closed_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg___boxed(lean_object* v_closed_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Broadcast_Error_closed_elim___redArg(v_closed_23_);
lean_dec(v_closed_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_closed_28_){
_start:
{
lean_inc(v_closed_28_);
return v_closed_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_closed_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Broadcast_Error_closed_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_closed_32_);
lean_dec(v_closed_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg(lean_object* v_alreadyClosed_35_){
_start:
{
lean_inc(v_alreadyClosed_35_);
return v_alreadyClosed_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg___boxed(lean_object* v_alreadyClosed_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Broadcast_Error_alreadyClosed_elim___redArg(v_alreadyClosed_36_);
lean_dec(v_alreadyClosed_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_alreadyClosed_41_){
_start:
{
lean_inc(v_alreadyClosed_41_);
return v_alreadyClosed_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_alreadyClosed_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Broadcast_Error_alreadyClosed_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_alreadyClosed_45_);
lean_dec(v_alreadyClosed_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg(lean_object* v_notSubscribed_48_){
_start:
{
lean_inc(v_notSubscribed_48_);
return v_notSubscribed_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg___boxed(lean_object* v_notSubscribed_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Broadcast_Error_notSubscribed_elim___redArg(v_notSubscribed_49_);
lean_dec(v_notSubscribed_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_notSubscribed_54_){
_start:
{
lean_inc(v_notSubscribed_54_);
return v_notSubscribed_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_notSubscribed_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Std_Broadcast_Error_notSubscribed_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_notSubscribed_58_);
lean_dec(v_notSubscribed_58_);
return v_res_60_;
}
}
static lean_object* _init_l_Std_Broadcast_instReprError_repr___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = lean_nat_to_int(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Std_Broadcast_instReprError_repr___closed__7(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr(uint8_t v_x_74_, lean_object* v_prec_75_){
_start:
{
lean_object* v___y_77_; lean_object* v___y_84_; lean_object* v___y_91_; 
switch(v_x_74_)
{
case 0:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = lean_nat_dec_le(v___x_97_, v_prec_75_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_77_ = v___x_99_;
goto v___jp_76_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_77_ = v___x_100_;
goto v___jp_76_;
}
}
case 1:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1024u);
v___x_102_ = lean_nat_dec_le(v___x_101_, v_prec_75_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_84_ = v___x_103_;
goto v___jp_83_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_84_ = v___x_104_;
goto v___jp_83_;
}
}
default: 
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_75_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_91_ = v___x_107_;
goto v___jp_90_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_91_ = v___x_108_;
goto v___jp_90_;
}
}
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_78_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__1));
lean_inc(v___y_77_);
v___x_79_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_79_, 0, v___y_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = 0;
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_80_);
v___x_82_ = l_Repr_addAppParen(v___x_81_, v_prec_75_);
return v___x_82_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_85_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__3));
lean_inc(v___y_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___y_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = 0;
v___x_88_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = l_Repr_addAppParen(v___x_88_, v_prec_75_);
return v___x_89_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__5));
lean_inc(v___y_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___y_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = 0;
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = l_Repr_addAppParen(v___x_95_, v_prec_75_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr___boxed(lean_object* v_x_109_, lean_object* v_prec_110_){
_start:
{
uint8_t v_x_171__boxed_111_; lean_object* v_res_112_; 
v_x_171__boxed_111_ = lean_unbox(v_x_109_);
v_res_112_ = l_Std_Broadcast_instReprError_repr(v_x_171__boxed_111_, v_prec_110_);
lean_dec(v_prec_110_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Std_Broadcast_Error_ofNat(lean_object* v_n_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_nat_dec_le(v_n_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_dec_le(v_n_115_, v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 2;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 1;
return v___x_121_;
}
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ofNat___boxed(lean_object* v_n_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Std_Broadcast_Error_ofNat(v_n_123_);
lean_dec(v_n_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Std_Broadcast_instDecidableEqError(uint8_t v_x_126_, uint8_t v_y_127_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = lean_box(v_x_126_);
v___x_129_ = lean_obj_tag_nat(v___x_128_);
lean_dec(v___x_128_);
v___x_130_ = lean_box(v_y_127_);
v___x_131_ = lean_obj_tag_nat(v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_nat_dec_eq(v___x_129_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instDecidableEqError___boxed(lean_object* v_x_133_, lean_object* v_y_134_){
_start:
{
uint8_t v_x_23__boxed_135_; uint8_t v_y_24__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_x_23__boxed_135_ = lean_unbox(v_x_133_);
v_y_24__boxed_136_ = lean_unbox(v_y_134_);
v_res_137_ = l_Std_Broadcast_instDecidableEqError(v_x_23__boxed_135_, v_y_24__boxed_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint64_t l_Std_Broadcast_instHashableError_hash(uint8_t v_x_139_){
_start:
{
switch(v_x_139_)
{
case 0:
{
uint64_t v___x_140_; 
v___x_140_ = 0ULL;
return v___x_140_;
}
case 1:
{
uint64_t v___x_141_; 
v___x_141_ = 1ULL;
return v___x_141_;
}
default: 
{
uint64_t v___x_142_; 
v___x_142_ = 2ULL;
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instHashableError_hash___boxed(lean_object* v_x_143_){
_start:
{
uint8_t v_x_40__boxed_144_; uint64_t v_res_145_; lean_object* v_r_146_; 
v_x_40__boxed_144_ = lean_unbox(v_x_143_);
v_res_145_ = l_Std_Broadcast_instHashableError_hash(v_x_40__boxed_144_);
v_r_146_ = lean_box_uint64(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0(uint8_t v_x_152_){
_start:
{
switch(v_x_152_)
{
case 0:
{
lean_object* v___x_153_; 
v___x_153_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
return v___x_153_;
}
case 1:
{
lean_object* v___x_154_; 
v___x_154_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
return v___x_154_;
}
default: 
{
lean_object* v___x_155_; 
v___x_155_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0___boxed(lean_object* v_x_156_){
_start:
{
uint8_t v_x_36__boxed_157_; lean_object* v_res_158_; 
v_x_36__boxed_157_ = lean_unbox(v_x_156_);
v_res_158_ = l_Std_instToStringBroadcastError___lam__0(v_x_36__boxed_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0(lean_object* v_00_u03b1_167_, lean_object* v_x_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_apply_1(v_x_168_, lean_box(0));
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_196_; 
v_a_179_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_196_ == 0)
{
v___x_181_ = v___x_170_;
v_isShared_182_ = v_isSharedCheck_196_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_170_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_196_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
uint8_t v___x_183_; 
v___x_183_ = lean_unbox(v_a_179_);
lean_dec(v_a_179_);
switch(v___x_183_)
{
case 0:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
case 1:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_188_);
v___x_190_ = v___x_181_;
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
default: 
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_192_);
v___x_194_ = v___x_181_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0___boxed(lean_object* v_00_u03b1_197_, lean_object* v_x_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_instMonadLiftBroadcastIO___lam__0(v_00_u03b1_197_, v_x_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(lean_object* v_c_203_, uint8_t v_b_204_){
_start:
{
lean_object* v_promise_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_promise_206_ = lean_ctor_get(v_c_203_, 0);
v___x_207_ = lean_box(v_b_204_);
v___x_208_ = lean_io_promise_resolve(v___x_207_, v_promise_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg___boxed(lean_object* v_c_209_, lean_object* v_b_210_, lean_object* v_a_211_){
_start:
{
uint8_t v_b_boxed_212_; lean_object* v_res_213_; 
v_b_boxed_212_ = lean_unbox(v_b_210_);
v_res_213_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_209_, v_b_boxed_212_);
lean_dec_ref(v_c_209_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(lean_object* v_00_u03b1_214_, lean_object* v_c_215_, uint8_t v_b_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_215_, v_b_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___boxed(lean_object* v_00_u03b1_219_, lean_object* v_c_220_, lean_object* v_b_221_, lean_object* v_a_222_){
_start:
{
uint8_t v_b_boxed_223_; lean_object* v_res_224_; 
v_b_boxed_223_ = lean_unbox(v_b_221_);
v_res_224_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(v_00_u03b1_219_, v_c_220_, v_b_boxed_223_);
lean_dec_ref(v_c_220_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default___redArg(){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = ((lean_object*)(l_Std_instInhabitedSlot_default___redArg___closed__0));
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default___redArg___boxed(lean_object* v___dummy_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_instInhabitedSlot_default___redArg();
return v_res_231_;
}
}
static lean_object* _init_l_Std_instInhabitedSlot_default___closed__0(void){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_instInhabitedSlot_default___redArg();
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default(lean_object* v_00_u03b1_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg(){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg___boxed(lean_object* v___dummy_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg();
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot(lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_240_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(9u);
v___x_255_ = lean_nat_to_int(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_unsigned_to_nat(7u);
v___x_263_ = lean_nat_to_int(v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(13u);
v___x_268_ = lean_nat_to_int(v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0));
v___x_271_ = lean_string_length(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17);
v___x_273_ = lean_nat_to_int(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(lean_object* v_inst_278_, lean_object* v_x_279_){
_start:
{
lean_object* v_value_280_; lean_object* v_pos_281_; lean_object* v_remaining_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_value_280_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_value_280_);
v_pos_281_ = lean_ctor_get(v_x_279_, 1);
lean_inc(v_pos_281_);
v_remaining_282_ = lean_ctor_get(v_x_279_, 2);
lean_inc(v_remaining_282_);
lean_dec_ref(v_x_279_);
v___x_283_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5));
v___x_284_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__6));
v___x_285_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = l_Option_repr___redArg(v_inst_278_, v_value_280_, v___x_286_);
v___x_288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = 0;
v___x_290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1, v___x_289_);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_284_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__9));
v___x_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
v___x_294_ = lean_box(1);
v___x_295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__11));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_283_);
v___x_299_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12);
v___x_300_ = l_Nat_reprFast(v_pos_281_);
v___x_301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
v___x_302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_299_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set_uint8(v___x_303_, sizeof(void*)*1, v___x_289_);
v___x_304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_298_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_292_);
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_294_);
v___x_307_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__14));
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_283_);
v___x_310_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15);
v___x_311_ = l_Nat_reprFast(v_remaining_282_);
v___x_312_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
v___x_313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_310_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*1, v___x_289_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_309_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18);
v___x_317_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__19));
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_315_);
v___x_319_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__20));
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_316_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*1, v___x_289_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, lean_object* v_x_325_, lean_object* v_prec_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(v_inst_324_, v_x_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, lean_object* v_x_330_, lean_object* v_prec_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(v_00_u03b1_328_, v_inst_329_, v_x_330_, v_prec_331_);
lean_dec(v_prec_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot___redArg(lean_object* v_inst_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_334_, 0, lean_box(0));
lean_closure_set(v___x_334_, 1, v_inst_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot(lean_object* v_00_u03b1_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_337_, 0, lean_box(0));
lean_closure_set(v___x_337_, 1, v_inst_336_);
return v___x_337_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10));
v___x_365_ = l_Lean_mkAtom(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_366_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12);
v___x_367_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_368_ = lean_array_push(v___x_367_, v___x_366_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__16));
v___x_380_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_381_ = lean_array_push(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_382_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17);
v___x_383_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15));
v___x_384_ = lean_box(2);
v___x_385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___x_383_);
lean_ctor_set(v___x_385_, 2, v___x_382_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18);
v___x_387_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13);
v___x_388_ = lean_array_push(v___x_387_, v___x_386_);
return v___x_388_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_389_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19);
v___x_390_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11));
v___x_391_ = lean_box(2);
v___x_392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
lean_ctor_set(v___x_392_, 2, v___x_389_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20);
v___x_394_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_395_ = lean_array_push(v___x_394_, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21);
v___x_397_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9));
v___x_398_ = lean_box(2);
v___x_399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
lean_ctor_set(v___x_399_, 2, v___x_396_);
return v___x_399_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22);
v___x_401_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_402_ = lean_array_push(v___x_401_, v___x_400_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23);
v___x_404_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7));
v___x_405_ = lean_box(2);
v___x_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_403_);
return v___x_406_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24);
v___x_408_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_409_ = lean_array_push(v___x_408_, v___x_407_);
return v___x_409_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_410_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25);
v___x_411_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4));
v___x_412_ = lean_box(2);
v___x_413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
lean_ctor_set(v___x_413_, 2, v___x_410_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1(void){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(lean_object* v_x_415_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Std_instInhabitedSlot_default___redArg___closed__0));
v___x_418_ = lean_st_mk_ref(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(v_x_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(lean_object* v_n_422_, lean_object* v_f_423_, lean_object* v_xs_424_, lean_object* v_k_425_, lean_object* v_acc_426_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_lt(v_k_425_, v_n_422_);
if (v___x_428_ == 0)
{
lean_dec(v_k_425_);
lean_dec_ref(v_f_423_);
return v_acc_426_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_429_ = lean_array_fget_borrowed(v_xs_424_, v_k_425_);
lean_inc_ref(v_f_423_);
lean_inc(v___x_429_);
v___x_430_ = lean_apply_2(v_f_423_, v___x_429_, lean_box(0));
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = lean_nat_add(v_k_425_, v___x_431_);
lean_dec(v_k_425_);
v___x_433_ = lean_array_push(v_acc_426_, v___x_430_);
v_k_425_ = v___x_432_;
v_acc_426_ = v___x_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_435_, lean_object* v_f_436_, lean_object* v_xs_437_, lean_object* v_k_438_, lean_object* v_acc_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_435_, v_f_436_, v_xs_437_, v_k_438_, v_acc_439_);
lean_dec_ref(v_xs_437_);
lean_dec(v_n_435_);
return v_res_441_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_Queue_empty___redArg();
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(lean_object* v_capacity_446_){
_start:
{
lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___f_448_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__0));
v___x_449_ = lean_box(0);
lean_inc(v_capacity_446_);
v___x_450_ = lean_mk_array(v_capacity_446_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__1));
v___x_453_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_capacity_446_, v___f_448_, v___x_450_, v___x_451_, v___x_452_);
lean_dec_ref(v___x_450_);
v___x_454_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_455_ = lean_box(1);
v___x_456_ = 0;
v___x_457_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_457_, 0, v___x_454_);
lean_ctor_set(v___x_457_, 1, v___x_454_);
lean_ctor_set(v___x_457_, 2, v_capacity_446_);
lean_ctor_set(v___x_457_, 3, v___x_451_);
lean_ctor_set(v___x_457_, 4, v___x_453_);
lean_ctor_set(v___x_457_, 5, v___x_451_);
lean_ctor_set(v___x_457_, 6, v___x_451_);
lean_ctor_set(v___x_457_, 7, v___x_455_);
lean_ctor_set(v___x_457_, 8, v___x_451_);
lean_ctor_set(v___x_457_, 9, v___x_451_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*10, v___x_456_);
v___x_458_ = l_Std_Mutex_new___redArg(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___boxed(lean_object* v_capacity_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new(lean_object* v_00_u03b1_462_, lean_object* v_capacity_463_, lean_object* v_h_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_463_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___boxed(lean_object* v_00_u03b1_467_, lean_object* v_capacity_468_, lean_object* v_h_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new(v_00_u03b1_467_, v_capacity_468_, v_h_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(lean_object* v_00_u03b1_472_, lean_object* v_00_u03b2_473_, lean_object* v_n_474_, lean_object* v_f_475_, lean_object* v_xs_476_, lean_object* v_k_477_, lean_object* v_h_478_, lean_object* v_acc_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_474_, v_f_475_, v_xs_476_, v_k_477_, v_acc_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_n_484_, lean_object* v_f_485_, lean_object* v_xs_486_, lean_object* v_k_487_, lean_object* v_h_488_, lean_object* v_acc_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(v_00_u03b1_482_, v_00_u03b2_483_, v_n_484_, v_f_485_, v_xs_486_, v_k_487_, v_h_488_, v_acc_489_);
lean_dec_ref(v_xs_486_);
lean_dec(v_n_484_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(lean_object* v_mutex_492_, lean_object* v_k_493_){
_start:
{
lean_object* v_ref_495_; lean_object* v_mutex_496_; lean_object* v___x_497_; lean_object* v_r_498_; 
v_ref_495_ = lean_ctor_get(v_mutex_492_, 0);
lean_inc(v_ref_495_);
v_mutex_496_ = lean_ctor_get(v_mutex_492_, 1);
lean_inc(v_mutex_496_);
lean_dec_ref(v_mutex_492_);
v___x_497_ = lean_io_basemutex_lock(v_mutex_496_);
v_r_498_ = lean_apply_2(v_k_493_, v_ref_495_, lean_box(0));
if (lean_obj_tag(v_r_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_a_499_ = lean_ctor_get(v_r_498_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v_r_498_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v_r_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_io_basemutex_unlock(v_mutex_496_);
lean_dec(v_mutex_496_);
if (v_isShared_502_ == 0)
{
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
v_a_508_ = lean_ctor_get(v_r_498_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_r_498_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v_r_498_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v_r_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = lean_io_basemutex_unlock(v_mutex_496_);
lean_dec(v_mutex_496_);
if (v_isShared_511_ == 0)
{
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_508_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg___boxed(lean_object* v_mutex_517_, lean_object* v_k_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_517_, v_k_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(lean_object* v_00_u03b1_521_, lean_object* v_00_u03b2_522_, lean_object* v_mutex_523_, lean_object* v_k_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_523_, v_k_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___boxed(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_mutex_529_, lean_object* v_k_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(v_00_u03b1_527_, v_00_u03b2_528_, v_mutex_529_, v_k_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(lean_object* v_k_533_, lean_object* v_v_534_, lean_object* v_t_535_){
_start:
{
if (lean_obj_tag(v_t_535_) == 0)
{
lean_object* v_size_536_; lean_object* v_k_537_; lean_object* v_v_538_; lean_object* v_l_539_; lean_object* v_r_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_821_; 
v_size_536_ = lean_ctor_get(v_t_535_, 0);
v_k_537_ = lean_ctor_get(v_t_535_, 1);
v_v_538_ = lean_ctor_get(v_t_535_, 2);
v_l_539_ = lean_ctor_get(v_t_535_, 3);
v_r_540_ = lean_ctor_get(v_t_535_, 4);
v_isSharedCheck_821_ = !lean_is_exclusive(v_t_535_);
if (v_isSharedCheck_821_ == 0)
{
v___x_542_ = v_t_535_;
v_isShared_543_ = v_isSharedCheck_821_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_r_540_);
lean_inc(v_l_539_);
lean_inc(v_v_538_);
lean_inc(v_k_537_);
lean_inc(v_size_536_);
lean_dec(v_t_535_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_821_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
uint8_t v___x_544_; 
v___x_544_ = lean_nat_dec_lt(v_k_533_, v_k_537_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = lean_nat_dec_eq(v_k_533_, v_k_537_);
if (v___x_545_ == 0)
{
lean_object* v_impl_546_; lean_object* v___x_547_; 
lean_dec(v_size_536_);
v_impl_546_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_533_, v_v_534_, v_r_540_);
v___x_547_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_539_) == 0)
{
lean_object* v_size_548_; lean_object* v_size_549_; lean_object* v_k_550_; lean_object* v_v_551_; lean_object* v_l_552_; lean_object* v_r_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_size_548_ = lean_ctor_get(v_l_539_, 0);
v_size_549_ = lean_ctor_get(v_impl_546_, 0);
v_k_550_ = lean_ctor_get(v_impl_546_, 1);
v_v_551_ = lean_ctor_get(v_impl_546_, 2);
v_l_552_ = lean_ctor_get(v_impl_546_, 3);
lean_inc(v_l_552_);
v_r_553_ = lean_ctor_get(v_impl_546_, 4);
v___x_554_ = lean_unsigned_to_nat(3u);
v___x_555_ = lean_nat_mul(v___x_554_, v_size_548_);
v___x_556_ = lean_nat_dec_lt(v___x_555_, v_size_549_);
lean_dec(v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
lean_dec(v_l_552_);
v___x_557_ = lean_nat_add(v___x_547_, v_size_548_);
v___x_558_ = lean_nat_add(v___x_557_, v_size_549_);
lean_dec(v___x_557_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v_impl_546_);
lean_ctor_set(v___x_542_, 0, v___x_558_);
v___x_560_ = v___x_542_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_l_539_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_impl_546_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_625_; 
lean_inc(v_r_553_);
lean_inc(v_v_551_);
lean_inc(v_k_550_);
lean_inc(v_size_549_);
v_isSharedCheck_625_ = !lean_is_exclusive(v_impl_546_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; lean_object* v_unused_627_; lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; 
v_unused_626_ = lean_ctor_get(v_impl_546_, 4);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v_impl_546_, 3);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_impl_546_, 2);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_impl_546_, 1);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_impl_546_, 0);
lean_dec(v_unused_630_);
v___x_563_ = v_impl_546_;
v_isShared_564_ = v_isSharedCheck_625_;
goto v_resetjp_562_;
}
else
{
lean_dec(v_impl_546_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_625_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_size_565_; lean_object* v_k_566_; lean_object* v_v_567_; lean_object* v_l_568_; lean_object* v_r_569_; lean_object* v_size_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_size_565_ = lean_ctor_get(v_l_552_, 0);
v_k_566_ = lean_ctor_get(v_l_552_, 1);
v_v_567_ = lean_ctor_get(v_l_552_, 2);
v_l_568_ = lean_ctor_get(v_l_552_, 3);
v_r_569_ = lean_ctor_get(v_l_552_, 4);
v_size_570_ = lean_ctor_get(v_r_553_, 0);
v___x_571_ = lean_unsigned_to_nat(2u);
v___x_572_ = lean_nat_mul(v___x_571_, v_size_570_);
v___x_573_ = lean_nat_dec_lt(v_size_565_, v___x_572_);
lean_dec(v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_601_; 
lean_inc(v_r_569_);
lean_inc(v_l_568_);
lean_inc(v_v_567_);
lean_inc(v_k_566_);
v_isSharedCheck_601_ = !lean_is_exclusive(v_l_552_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; lean_object* v_unused_603_; lean_object* v_unused_604_; lean_object* v_unused_605_; lean_object* v_unused_606_; 
v_unused_602_ = lean_ctor_get(v_l_552_, 4);
lean_dec(v_unused_602_);
v_unused_603_ = lean_ctor_get(v_l_552_, 3);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_l_552_, 2);
lean_dec(v_unused_604_);
v_unused_605_ = lean_ctor_get(v_l_552_, 1);
lean_dec(v_unused_605_);
v_unused_606_ = lean_ctor_get(v_l_552_, 0);
lean_dec(v_unused_606_);
v___x_575_ = v_l_552_;
v_isShared_576_ = v_isSharedCheck_601_;
goto v_resetjp_574_;
}
else
{
lean_dec(v_l_552_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_601_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_591_; 
v___x_577_ = lean_nat_add(v___x_547_, v_size_548_);
v___x_578_ = lean_nat_add(v___x_577_, v_size_549_);
lean_dec(v_size_549_);
if (lean_obj_tag(v_l_568_) == 0)
{
lean_object* v_size_599_; 
v_size_599_ = lean_ctor_get(v_l_568_, 0);
lean_inc(v_size_599_);
v___y_591_ = v_size_599_;
goto v___jp_590_;
}
else
{
lean_object* v___x_600_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___y_591_ = v___x_600_;
goto v___jp_590_;
}
v___jp_579_:
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = lean_nat_add(v___y_580_, v___y_582_);
lean_dec(v___y_582_);
lean_dec(v___y_580_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 4, v_r_553_);
lean_ctor_set(v___x_575_, 3, v_r_569_);
lean_ctor_set(v___x_575_, 2, v_v_551_);
lean_ctor_set(v___x_575_, 1, v_k_550_);
lean_ctor_set(v___x_575_, 0, v___x_583_);
v___x_585_ = v___x_575_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_k_550_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_v_551_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_r_569_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v_r_553_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 4, v___x_585_);
lean_ctor_set(v___x_563_, 3, v___y_581_);
lean_ctor_set(v___x_563_, 2, v_v_567_);
lean_ctor_set(v___x_563_, 1, v_k_566_);
lean_ctor_set(v___x_563_, 0, v___x_578_);
v___x_587_ = v___x_563_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_k_566_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_v_567_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v___y_581_);
lean_ctor_set(v_reuseFailAlloc_588_, 4, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_nat_add(v___x_577_, v___y_591_);
lean_dec(v___y_591_);
lean_dec(v___x_577_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v_l_568_);
lean_ctor_set(v___x_542_, 0, v___x_592_);
v___x_594_ = v___x_542_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_l_539_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_l_568_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_nat_add(v___x_547_, v_size_570_);
if (lean_obj_tag(v_r_569_) == 0)
{
lean_object* v_size_596_; 
v_size_596_ = lean_ctor_get(v_r_569_, 0);
lean_inc(v_size_596_);
v___y_580_ = v___x_595_;
v___y_581_ = v___x_594_;
v___y_582_ = v_size_596_;
goto v___jp_579_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___y_580_ = v___x_595_;
v___y_581_ = v___x_594_;
v___y_582_ = v___x_597_;
goto v___jp_579_;
}
}
}
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
lean_del_object(v___x_542_);
v___x_607_ = lean_nat_add(v___x_547_, v_size_548_);
v___x_608_ = lean_nat_add(v___x_607_, v_size_549_);
lean_dec(v_size_549_);
v___x_609_ = lean_nat_add(v___x_607_, v_size_565_);
lean_dec(v___x_607_);
lean_inc_ref(v_l_539_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 4, v_l_552_);
lean_ctor_set(v___x_563_, 3, v_l_539_);
lean_ctor_set(v___x_563_, 2, v_v_538_);
lean_ctor_set(v___x_563_, 1, v_k_537_);
lean_ctor_set(v___x_563_, 0, v___x_609_);
v___x_611_ = v___x_563_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_l_539_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v_l_552_);
v___x_611_ = v_reuseFailAlloc_624_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_isSharedCheck_618_ = !lean_is_exclusive(v_l_539_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; lean_object* v_unused_621_; lean_object* v_unused_622_; lean_object* v_unused_623_; 
v_unused_619_ = lean_ctor_get(v_l_539_, 4);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_l_539_, 3);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v_l_539_, 2);
lean_dec(v_unused_621_);
v_unused_622_ = lean_ctor_get(v_l_539_, 1);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_l_539_, 0);
lean_dec(v_unused_623_);
v___x_613_ = v_l_539_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_dec(v_l_539_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 4, v_r_553_);
lean_ctor_set(v___x_613_, 3, v___x_611_);
lean_ctor_set(v___x_613_, 2, v_v_551_);
lean_ctor_set(v___x_613_, 1, v_k_550_);
lean_ctor_set(v___x_613_, 0, v___x_608_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_k_550_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_v_551_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_r_553_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_631_; 
v_l_631_ = lean_ctor_get(v_impl_546_, 3);
lean_inc(v_l_631_);
if (lean_obj_tag(v_l_631_) == 0)
{
lean_object* v_r_632_; lean_object* v_k_633_; lean_object* v_v_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_657_; 
v_r_632_ = lean_ctor_get(v_impl_546_, 4);
v_k_633_ = lean_ctor_get(v_impl_546_, 1);
v_v_634_ = lean_ctor_get(v_impl_546_, 2);
v_isSharedCheck_657_ = !lean_is_exclusive(v_impl_546_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; lean_object* v_unused_659_; 
v_unused_658_ = lean_ctor_get(v_impl_546_, 3);
lean_dec(v_unused_658_);
v_unused_659_ = lean_ctor_get(v_impl_546_, 0);
lean_dec(v_unused_659_);
v___x_636_ = v_impl_546_;
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_r_632_);
lean_inc(v_v_634_);
lean_inc(v_k_633_);
lean_dec(v_impl_546_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_657_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_k_638_; lean_object* v_v_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_653_; 
v_k_638_ = lean_ctor_get(v_l_631_, 1);
v_v_639_ = lean_ctor_get(v_l_631_, 2);
v_isSharedCheck_653_ = !lean_is_exclusive(v_l_631_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_654_ = lean_ctor_get(v_l_631_, 4);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_l_631_, 3);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_l_631_, 0);
lean_dec(v_unused_656_);
v___x_641_ = v_l_631_;
v_isShared_642_ = v_isSharedCheck_653_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_v_639_);
lean_inc(v_k_638_);
lean_dec(v_l_631_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_653_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_632_, 2);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 4, v_r_632_);
lean_ctor_set(v___x_641_, 3, v_r_632_);
lean_ctor_set(v___x_641_, 2, v_v_538_);
lean_ctor_set(v___x_641_, 1, v_k_537_);
lean_ctor_set(v___x_641_, 0, v___x_547_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v_r_632_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v_r_632_);
v___x_645_ = v_reuseFailAlloc_652_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
lean_inc(v_r_632_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 3, v_r_632_);
lean_ctor_set(v___x_636_, 0, v___x_547_);
v___x_647_ = v___x_636_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_k_633_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_v_634_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_r_632_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v_r_632_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v___x_647_);
lean_ctor_set(v___x_542_, 3, v___x_645_);
lean_ctor_set(v___x_542_, 2, v_v_639_);
lean_ctor_set(v___x_542_, 1, v_k_638_);
lean_ctor_set(v___x_542_, 0, v___x_643_);
v___x_649_ = v___x_542_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_643_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_k_638_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_v_639_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
else
{
lean_object* v_r_660_; 
v_r_660_ = lean_ctor_get(v_impl_546_, 4);
lean_inc(v_r_660_);
if (lean_obj_tag(v_r_660_) == 0)
{
lean_object* v_k_661_; lean_object* v_v_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_673_; 
v_k_661_ = lean_ctor_get(v_impl_546_, 1);
v_v_662_ = lean_ctor_get(v_impl_546_, 2);
v_isSharedCheck_673_ = !lean_is_exclusive(v_impl_546_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; lean_object* v_unused_675_; lean_object* v_unused_676_; 
v_unused_674_ = lean_ctor_get(v_impl_546_, 4);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_impl_546_, 3);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v_impl_546_, 0);
lean_dec(v_unused_676_);
v___x_664_ = v_impl_546_;
v_isShared_665_ = v_isSharedCheck_673_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_v_662_);
lean_inc(v_k_661_);
lean_dec(v_impl_546_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_673_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(3u);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 4, v_l_631_);
lean_ctor_set(v___x_664_, 2, v_v_538_);
lean_ctor_set(v___x_664_, 1, v_k_537_);
lean_ctor_set(v___x_664_, 0, v___x_547_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_l_631_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v_l_631_);
v___x_668_ = v_reuseFailAlloc_672_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v_r_660_);
lean_ctor_set(v___x_542_, 3, v___x_668_);
lean_ctor_set(v___x_542_, 2, v_v_662_);
lean_ctor_set(v___x_542_, 1, v_k_661_);
lean_ctor_set(v___x_542_, 0, v___x_666_);
v___x_670_ = v___x_542_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_k_661_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_v_662_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_r_660_);
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
else
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(2u);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v_impl_546_);
lean_ctor_set(v___x_542_, 3, v_r_660_);
lean_ctor_set(v___x_542_, 0, v___x_677_);
v___x_679_ = v___x_542_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_680_, 3, v_r_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 4, v_impl_546_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
else
{
lean_object* v___x_682_; 
lean_dec(v_v_538_);
lean_dec(v_k_537_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 2, v_v_534_);
lean_ctor_set(v___x_542_, 1, v_k_533_);
v___x_682_ = v___x_542_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_size_536_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_k_533_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_v_534_);
lean_ctor_set(v_reuseFailAlloc_683_, 3, v_l_539_);
lean_ctor_set(v_reuseFailAlloc_683_, 4, v_r_540_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
lean_object* v_impl_684_; lean_object* v___x_685_; 
lean_dec(v_size_536_);
v_impl_684_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_533_, v_v_534_, v_l_539_);
v___x_685_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_540_) == 0)
{
lean_object* v_size_686_; lean_object* v_size_687_; lean_object* v_k_688_; lean_object* v_v_689_; lean_object* v_l_690_; lean_object* v_r_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_size_686_ = lean_ctor_get(v_r_540_, 0);
v_size_687_ = lean_ctor_get(v_impl_684_, 0);
v_k_688_ = lean_ctor_get(v_impl_684_, 1);
v_v_689_ = lean_ctor_get(v_impl_684_, 2);
v_l_690_ = lean_ctor_get(v_impl_684_, 3);
v_r_691_ = lean_ctor_get(v_impl_684_, 4);
lean_inc(v_r_691_);
v___x_692_ = lean_unsigned_to_nat(3u);
v___x_693_ = lean_nat_mul(v___x_692_, v_size_686_);
v___x_694_ = lean_nat_dec_lt(v___x_693_, v_size_687_);
lean_dec(v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec(v_r_691_);
v___x_695_ = lean_nat_add(v___x_685_, v_size_687_);
v___x_696_ = lean_nat_add(v___x_695_, v_size_686_);
lean_dec(v___x_695_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 3, v_impl_684_);
lean_ctor_set(v___x_542_, 0, v___x_696_);
v___x_698_ = v___x_542_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_impl_684_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v_r_540_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_765_; 
lean_inc(v_l_690_);
lean_inc(v_v_689_);
lean_inc(v_k_688_);
lean_inc(v_size_687_);
v_isSharedCheck_765_ = !lean_is_exclusive(v_impl_684_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; lean_object* v_unused_770_; 
v_unused_766_ = lean_ctor_get(v_impl_684_, 4);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_impl_684_, 3);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_impl_684_, 2);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_impl_684_, 1);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_impl_684_, 0);
lean_dec(v_unused_770_);
v___x_701_ = v_impl_684_;
v_isShared_702_ = v_isSharedCheck_765_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_impl_684_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_765_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_size_703_; lean_object* v_size_704_; lean_object* v_k_705_; lean_object* v_v_706_; lean_object* v_l_707_; lean_object* v_r_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_size_703_ = lean_ctor_get(v_l_690_, 0);
v_size_704_ = lean_ctor_get(v_r_691_, 0);
v_k_705_ = lean_ctor_get(v_r_691_, 1);
v_v_706_ = lean_ctor_get(v_r_691_, 2);
v_l_707_ = lean_ctor_get(v_r_691_, 3);
v_r_708_ = lean_ctor_get(v_r_691_, 4);
v___x_709_ = lean_unsigned_to_nat(2u);
v___x_710_ = lean_nat_mul(v___x_709_, v_size_703_);
v___x_711_ = lean_nat_dec_lt(v_size_704_, v___x_710_);
lean_dec(v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_740_; 
lean_inc(v_r_708_);
lean_inc(v_l_707_);
lean_inc(v_v_706_);
lean_inc(v_k_705_);
v_isSharedCheck_740_ = !lean_is_exclusive(v_r_691_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; lean_object* v_unused_742_; lean_object* v_unused_743_; lean_object* v_unused_744_; lean_object* v_unused_745_; 
v_unused_741_ = lean_ctor_get(v_r_691_, 4);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v_r_691_, 3);
lean_dec(v_unused_742_);
v_unused_743_ = lean_ctor_get(v_r_691_, 2);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v_r_691_, 1);
lean_dec(v_unused_744_);
v_unused_745_ = lean_ctor_get(v_r_691_, 0);
lean_dec(v_unused_745_);
v___x_713_ = v_r_691_;
v_isShared_714_ = v_isSharedCheck_740_;
goto v_resetjp_712_;
}
else
{
lean_dec(v_r_691_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_740_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___x_728_; lean_object* v___y_730_; 
v___x_715_ = lean_nat_add(v___x_685_, v_size_687_);
lean_dec(v_size_687_);
v___x_716_ = lean_nat_add(v___x_715_, v_size_686_);
lean_dec(v___x_715_);
v___x_728_ = lean_nat_add(v___x_685_, v_size_703_);
if (lean_obj_tag(v_l_707_) == 0)
{
lean_object* v_size_738_; 
v_size_738_ = lean_ctor_get(v_l_707_, 0);
lean_inc(v_size_738_);
v___y_730_ = v_size_738_;
goto v___jp_729_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___y_730_ = v___x_739_;
goto v___jp_729_;
}
v___jp_717_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = lean_nat_add(v___y_718_, v___y_720_);
lean_dec(v___y_720_);
lean_dec(v___y_718_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 4, v_r_540_);
lean_ctor_set(v___x_713_, 3, v_r_708_);
lean_ctor_set(v___x_713_, 2, v_v_538_);
lean_ctor_set(v___x_713_, 1, v_k_537_);
lean_ctor_set(v___x_713_, 0, v___x_721_);
v___x_723_ = v___x_713_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_r_708_);
lean_ctor_set(v_reuseFailAlloc_727_, 4, v_r_540_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v___x_723_);
lean_ctor_set(v___x_701_, 3, v___y_719_);
lean_ctor_set(v___x_701_, 2, v_v_706_);
lean_ctor_set(v___x_701_, 1, v_k_705_);
lean_ctor_set(v___x_701_, 0, v___x_716_);
v___x_725_ = v___x_701_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_k_705_);
lean_ctor_set(v_reuseFailAlloc_726_, 2, v_v_706_);
lean_ctor_set(v_reuseFailAlloc_726_, 3, v___y_719_);
lean_ctor_set(v_reuseFailAlloc_726_, 4, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
v___jp_729_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_nat_add(v___x_728_, v___y_730_);
lean_dec(v___y_730_);
lean_dec(v___x_728_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v_l_707_);
lean_ctor_set(v___x_542_, 3, v_l_690_);
lean_ctor_set(v___x_542_, 2, v_v_689_);
lean_ctor_set(v___x_542_, 1, v_k_688_);
lean_ctor_set(v___x_542_, 0, v___x_731_);
v___x_733_ = v___x_542_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_k_688_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_v_689_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_l_690_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_l_707_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_nat_add(v___x_685_, v_size_686_);
if (lean_obj_tag(v_r_708_) == 0)
{
lean_object* v_size_735_; 
v_size_735_ = lean_ctor_get(v_r_708_, 0);
lean_inc(v_size_735_);
v___y_718_ = v___x_734_;
v___y_719_ = v___x_733_;
v___y_720_ = v_size_735_;
goto v___jp_717_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = lean_unsigned_to_nat(0u);
v___y_718_ = v___x_734_;
v___y_719_ = v___x_733_;
v___y_720_ = v___x_736_;
goto v___jp_717_;
}
}
}
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
lean_del_object(v___x_542_);
v___x_746_ = lean_nat_add(v___x_685_, v_size_687_);
lean_dec(v_size_687_);
v___x_747_ = lean_nat_add(v___x_746_, v_size_686_);
lean_dec(v___x_746_);
v___x_748_ = lean_nat_add(v___x_685_, v_size_686_);
v___x_749_ = lean_nat_add(v___x_748_, v_size_704_);
lean_dec(v___x_748_);
lean_inc_ref(v_r_540_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 4, v_r_540_);
lean_ctor_set(v___x_701_, 3, v_r_691_);
lean_ctor_set(v___x_701_, 2, v_v_538_);
lean_ctor_set(v___x_701_, 1, v_k_537_);
lean_ctor_set(v___x_701_, 0, v___x_749_);
v___x_751_ = v___x_701_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_r_691_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_r_540_);
v___x_751_ = v_reuseFailAlloc_764_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_isSharedCheck_758_ = !lean_is_exclusive(v_r_540_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; lean_object* v_unused_763_; 
v_unused_759_ = lean_ctor_get(v_r_540_, 4);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_r_540_, 3);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_r_540_, 2);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_r_540_, 1);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_r_540_, 0);
lean_dec(v_unused_763_);
v___x_753_ = v_r_540_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_dec(v_r_540_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 4, v___x_751_);
lean_ctor_set(v___x_753_, 3, v_l_690_);
lean_ctor_set(v___x_753_, 2, v_v_689_);
lean_ctor_set(v___x_753_, 1, v_k_688_);
lean_ctor_set(v___x_753_, 0, v___x_747_);
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_k_688_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_v_689_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_l_690_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v___x_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_771_; 
v_l_771_ = lean_ctor_get(v_impl_684_, 3);
if (lean_obj_tag(v_l_771_) == 0)
{
lean_object* v_r_772_; lean_object* v_k_773_; lean_object* v_v_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_785_; 
lean_inc_ref(v_l_771_);
v_r_772_ = lean_ctor_get(v_impl_684_, 4);
v_k_773_ = lean_ctor_get(v_impl_684_, 1);
v_v_774_ = lean_ctor_get(v_impl_684_, 2);
v_isSharedCheck_785_ = !lean_is_exclusive(v_impl_684_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; lean_object* v_unused_787_; 
v_unused_786_ = lean_ctor_get(v_impl_684_, 3);
lean_dec(v_unused_786_);
v_unused_787_ = lean_ctor_get(v_impl_684_, 0);
lean_dec(v_unused_787_);
v___x_776_ = v_impl_684_;
v_isShared_777_ = v_isSharedCheck_785_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_r_772_);
lean_inc(v_v_774_);
lean_inc(v_k_773_);
lean_dec(v_impl_684_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_785_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_772_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 3, v_r_772_);
lean_ctor_set(v___x_776_, 2, v_v_538_);
lean_ctor_set(v___x_776_, 1, v_k_537_);
lean_ctor_set(v___x_776_, 0, v___x_685_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_r_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_r_772_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v___x_780_);
lean_ctor_set(v___x_542_, 3, v_l_771_);
lean_ctor_set(v___x_542_, 2, v_v_774_);
lean_ctor_set(v___x_542_, 1, v_k_773_);
lean_ctor_set(v___x_542_, 0, v___x_778_);
v___x_782_ = v___x_542_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_k_773_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_v_774_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_l_771_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_r_788_; 
v_r_788_ = lean_ctor_get(v_impl_684_, 4);
lean_inc(v_r_788_);
if (lean_obj_tag(v_r_788_) == 0)
{
lean_object* v_k_789_; lean_object* v_v_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_813_; 
lean_inc(v_l_771_);
v_k_789_ = lean_ctor_get(v_impl_684_, 1);
v_v_790_ = lean_ctor_get(v_impl_684_, 2);
v_isSharedCheck_813_ = !lean_is_exclusive(v_impl_684_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; lean_object* v_unused_815_; lean_object* v_unused_816_; 
v_unused_814_ = lean_ctor_get(v_impl_684_, 4);
lean_dec(v_unused_814_);
v_unused_815_ = lean_ctor_get(v_impl_684_, 3);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_impl_684_, 0);
lean_dec(v_unused_816_);
v___x_792_ = v_impl_684_;
v_isShared_793_ = v_isSharedCheck_813_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_v_790_);
lean_inc(v_k_789_);
lean_dec(v_impl_684_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_813_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_809_; 
v_k_794_ = lean_ctor_get(v_r_788_, 1);
v_v_795_ = lean_ctor_get(v_r_788_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_r_788_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_810_ = lean_ctor_get(v_r_788_, 4);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_r_788_, 3);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_r_788_, 0);
lean_dec(v_unused_812_);
v___x_797_ = v_r_788_;
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_v_795_);
lean_inc(v_k_794_);
lean_dec(v_r_788_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_unsigned_to_nat(3u);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 4, v_l_771_);
lean_ctor_set(v___x_797_, 3, v_l_771_);
lean_ctor_set(v___x_797_, 2, v_v_790_);
lean_ctor_set(v___x_797_, 1, v_k_789_);
lean_ctor_set(v___x_797_, 0, v___x_685_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_789_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_790_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_l_771_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_l_771_);
v___x_801_ = v_reuseFailAlloc_808_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v_l_771_);
lean_ctor_set(v___x_792_, 2, v_v_538_);
lean_ctor_set(v___x_792_, 1, v_k_537_);
lean_ctor_set(v___x_792_, 0, v___x_685_);
v___x_803_ = v___x_792_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_l_771_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_l_771_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v___x_803_);
lean_ctor_set(v___x_542_, 3, v___x_801_);
lean_ctor_set(v___x_542_, 2, v_v_795_);
lean_ctor_set(v___x_542_, 1, v_k_794_);
lean_ctor_set(v___x_542_, 0, v___x_799_);
v___x_805_ = v___x_542_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_unsigned_to_nat(2u);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 4, v_r_788_);
lean_ctor_set(v___x_542_, 3, v_impl_684_);
lean_ctor_set(v___x_542_, 0, v___x_817_);
v___x_819_ = v___x_542_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_k_537_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_v_538_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_impl_684_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_r_788_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v_k_533_);
lean_ctor_set(v___x_823_, 2, v_v_534_);
lean_ctor_set(v___x_823_, 3, v_t_535_);
lean_ctor_set(v___x_823_, 4, v_t_535_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; lean_object* v_producers_827_; lean_object* v_waiters_828_; lean_object* v_capacity_829_; lean_object* v_size_830_; lean_object* v_buffer_831_; lean_object* v_write_832_; lean_object* v_read_833_; lean_object* v_receivers_834_; lean_object* v_nextId_835_; uint8_t v_closed_836_; lean_object* v_pos_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_849_; 
v___x_826_ = lean_st_ref_take(v___y_824_);
v_producers_827_ = lean_ctor_get(v___x_826_, 0);
v_waiters_828_ = lean_ctor_get(v___x_826_, 1);
v_capacity_829_ = lean_ctor_get(v___x_826_, 2);
v_size_830_ = lean_ctor_get(v___x_826_, 3);
v_buffer_831_ = lean_ctor_get(v___x_826_, 4);
v_write_832_ = lean_ctor_get(v___x_826_, 5);
v_read_833_ = lean_ctor_get(v___x_826_, 6);
v_receivers_834_ = lean_ctor_get(v___x_826_, 7);
v_nextId_835_ = lean_ctor_get(v___x_826_, 8);
v_closed_836_ = lean_ctor_get_uint8(v___x_826_, sizeof(void*)*10);
v_pos_837_ = lean_ctor_get(v___x_826_, 9);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_849_ == 0)
{
v___x_839_ = v___x_826_;
v_isShared_840_ = v_isSharedCheck_849_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_pos_837_);
lean_inc(v_nextId_835_);
lean_inc(v_receivers_834_);
lean_inc(v_read_833_);
lean_inc(v_write_832_);
lean_inc(v_buffer_831_);
lean_inc(v_size_830_);
lean_inc(v_capacity_829_);
lean_inc(v_waiters_828_);
lean_inc(v_producers_827_);
lean_dec(v___x_826_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_849_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
lean_inc(v_pos_837_);
lean_inc(v_nextId_835_);
v___x_841_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_nextId_835_, v_pos_837_, v_receivers_834_);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_add(v_nextId_835_, v___x_842_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 8, v___x_843_);
lean_ctor_set(v___x_839_, 7, v___x_841_);
v___x_845_ = v___x_839_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_producers_827_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_waiters_828_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_capacity_829_);
lean_ctor_set(v_reuseFailAlloc_848_, 3, v_size_830_);
lean_ctor_set(v_reuseFailAlloc_848_, 4, v_buffer_831_);
lean_ctor_set(v_reuseFailAlloc_848_, 5, v_write_832_);
lean_ctor_set(v_reuseFailAlloc_848_, 6, v_read_833_);
lean_ctor_set(v_reuseFailAlloc_848_, 7, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_848_, 8, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_848_, 9, v_pos_837_);
lean_ctor_set_uint8(v_reuseFailAlloc_848_, sizeof(void*)*10, v_closed_836_);
v___x_845_ = v_reuseFailAlloc_848_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_st_ref_put(v___y_824_, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_nextId_835_);
return v___x_847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0___boxed(lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(v___y_850_);
lean_dec(v___y_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(lean_object* v_bd_854_){
_start:
{
lean_object* v___f_856_; lean_object* v___x_857_; 
v___f_856_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___closed__0));
lean_inc_ref(v_bd_854_);
v___x_857_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_bd_854_, v___f_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_866_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_866_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_866_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v_bd_854_);
lean_ctor_set(v___x_862_, 1, v_a_858_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v_bd_854_);
v_a_867_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_857_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_857_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___boxed(lean_object* v_bd_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(lean_object* v_00_u03b1_878_, lean_object* v_bd_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___boxed(lean_object* v_00_u03b1_882_, lean_object* v_bd_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(v_00_u03b1_882_, v_bd_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0(lean_object* v_00_u03b2_886_, lean_object* v_k_887_, lean_object* v_v_888_, lean_object* v_t_889_, lean_object* v_hl_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_887_, v_v_888_, v_t_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(lean_object* v_toApplicative_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_size_894_; lean_object* v_toPure_895_; lean_object* v___x_896_; uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_size_894_ = lean_ctor_get(v_a_893_, 3);
v_toPure_895_ = lean_ctor_get(v_toApplicative_892_, 1);
lean_inc(v_toPure_895_);
lean_dec_ref(v_toApplicative_892_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_nat_dec_eq(v_size_894_, v___x_896_);
v___x_898_ = lean_box(v___x_897_);
v___x_899_ = lean_apply_2(v_toPure_895_, lean_box(0), v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed(lean_object* v_toApplicative_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(v_toApplicative_900_, v_a_901_);
lean_dec_ref(v_a_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_toApplicative_906_; lean_object* v_toBind_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_toApplicative_906_ = lean_ctor_get(v_inst_903_, 0);
lean_inc_ref(v_toApplicative_906_);
v_toBind_907_ = lean_ctor_get(v_inst_903_, 1);
lean_inc(v_toBind_907_);
lean_dec_ref(v_inst_903_);
v___f_908_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_908_, 0, v_toApplicative_906_);
lean_inc(v_a_905_);
v___x_909_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_909_, 0, lean_box(0));
lean_closure_set(v___x_909_, 1, lean_box(0));
lean_closure_set(v___x_909_, 2, v_a_905_);
v___x_910_ = lean_apply_2(v_inst_904_, lean_box(0), v___x_909_);
v___x_911_ = lean_apply_4(v_toBind_907_, lean_box(0), lean_box(0), v___x_910_, v___f_908_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___boxed(lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_912_, v_inst_913_, v_a_914_);
lean_dec(v_a_914_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(lean_object* v_m_916_, lean_object* v_00_u03b1_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_918_, v_inst_919_, v_a_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___boxed(lean_object* v_m_922_, lean_object* v_00_u03b1_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(v_m_922_, v_00_u03b1_923_, v_inst_924_, v_inst_925_, v_a_926_);
lean_dec(v_a_926_);
return v_res_927_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_capacity_931_; lean_object* v_size_932_; uint8_t v___x_933_; 
v___x_930_ = lean_st_ref_get(v_a_928_);
v_capacity_931_ = lean_ctor_get(v___x_930_, 2);
lean_inc(v_capacity_931_);
v_size_932_ = lean_ctor_get(v___x_930_, 3);
lean_inc(v_size_932_);
lean_dec(v___x_930_);
v___x_933_ = lean_nat_dec_le(v_capacity_931_, v_size_932_);
lean_dec(v_size_932_);
lean_dec(v_capacity_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg___boxed(lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_934_);
lean_dec(v_a_934_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(lean_object* v_00_u03b1_938_, lean_object* v_a_939_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___boxed(lean_object* v_00_u03b1_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(v_00_u03b1_942_, v_a_943_);
lean_dec(v_a_943_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(lean_object* v_value_947_, lean_object* v_st_948_){
_start:
{
lean_object* v_producers_950_; lean_object* v_waiters_951_; lean_object* v_capacity_952_; lean_object* v_size_953_; lean_object* v_buffer_954_; lean_object* v_write_955_; lean_object* v_read_956_; lean_object* v_receivers_957_; lean_object* v_nextId_958_; uint8_t v_closed_959_; lean_object* v_pos_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_980_; 
v_producers_950_ = lean_ctor_get(v_st_948_, 0);
v_waiters_951_ = lean_ctor_get(v_st_948_, 1);
v_capacity_952_ = lean_ctor_get(v_st_948_, 2);
v_size_953_ = lean_ctor_get(v_st_948_, 3);
v_buffer_954_ = lean_ctor_get(v_st_948_, 4);
v_write_955_ = lean_ctor_get(v_st_948_, 5);
v_read_956_ = lean_ctor_get(v_st_948_, 6);
v_receivers_957_ = lean_ctor_get(v_st_948_, 7);
v_nextId_958_ = lean_ctor_get(v_st_948_, 8);
v_closed_959_ = lean_ctor_get_uint8(v_st_948_, sizeof(void*)*10);
v_pos_960_ = lean_ctor_get(v_st_948_, 9);
v_isSharedCheck_980_ = !lean_is_exclusive(v_st_948_);
if (v_isSharedCheck_980_ == 0)
{
v___x_962_ = v_st_948_;
v_isShared_963_ = v_isSharedCheck_980_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_pos_960_);
lean_inc(v_nextId_958_);
lean_inc(v_receivers_957_);
lean_inc(v_read_956_);
lean_inc(v_write_955_);
lean_inc(v_buffer_954_);
lean_inc(v_size_953_);
lean_inc(v_capacity_952_);
lean_inc(v_waiters_951_);
lean_inc(v_producers_950_);
lean_dec(v_st_948_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_980_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_tailRef_964_; lean_object* v___x_965_; lean_object* v___y_967_; 
v_tailRef_964_ = lean_array_fget_borrowed(v_buffer_954_, v_write_955_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_value_947_);
if (lean_obj_tag(v_receivers_957_) == 0)
{
lean_object* v_size_978_; 
v_size_978_ = lean_ctor_get(v_receivers_957_, 0);
lean_inc(v_size_978_);
v___y_967_ = v_size_978_;
goto v___jp_966_;
}
else
{
lean_object* v___x_979_; 
v___x_979_ = lean_unsigned_to_nat(0u);
v___y_967_ = v___x_979_;
goto v___jp_966_;
}
v___jp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
lean_inc(v_pos_960_);
v___x_968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_968_, 0, v___x_965_);
lean_ctor_set(v___x_968_, 1, v_pos_960_);
lean_ctor_set(v___x_968_, 2, v___y_967_);
v___x_969_ = lean_st_ref_swap(v_tailRef_964_, v___x_968_);
lean_dec(v___x_969_);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_add(v_write_955_, v___x_970_);
lean_dec(v_write_955_);
v___x_972_ = lean_nat_mod(v___x_971_, v_capacity_952_);
lean_dec(v___x_971_);
v___x_973_ = lean_nat_add(v_size_953_, v___x_970_);
lean_dec(v_size_953_);
v___x_974_ = lean_nat_add(v_pos_960_, v___x_970_);
lean_dec(v_pos_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 9, v___x_974_);
lean_ctor_set(v___x_962_, 5, v___x_972_);
lean_ctor_set(v___x_962_, 3, v___x_973_);
v___x_976_ = v___x_962_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_producers_950_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_waiters_951_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_capacity_952_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_buffer_954_);
lean_ctor_set(v_reuseFailAlloc_977_, 5, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_977_, 6, v_read_956_);
lean_ctor_set(v_reuseFailAlloc_977_, 7, v_receivers_957_);
lean_ctor_set(v_reuseFailAlloc_977_, 8, v_nextId_958_);
lean_ctor_set(v_reuseFailAlloc_977_, 9, v___x_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_977_, sizeof(void*)*10, v_closed_959_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg___boxed(lean_object* v_value_981_, lean_object* v_st_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_981_, v_st_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(lean_object* v_00_u03b1_985_, lean_object* v_value_986_, lean_object* v_st_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_986_, v_st_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___boxed(lean_object* v_00_u03b1_990_, lean_object* v_value_991_, lean_object* v_st_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(v_00_u03b1_990_, v_value_991_, v_st_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(lean_object* v_st_995_){
_start:
{
lean_object* v_producers_996_; lean_object* v_waiters_997_; lean_object* v_capacity_998_; lean_object* v_size_999_; lean_object* v_buffer_1000_; lean_object* v_write_1001_; lean_object* v_read_1002_; lean_object* v_receivers_1003_; lean_object* v_nextId_1004_; uint8_t v_closed_1005_; lean_object* v_pos_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1017_; 
v_producers_996_ = lean_ctor_get(v_st_995_, 0);
v_waiters_997_ = lean_ctor_get(v_st_995_, 1);
v_capacity_998_ = lean_ctor_get(v_st_995_, 2);
v_size_999_ = lean_ctor_get(v_st_995_, 3);
v_buffer_1000_ = lean_ctor_get(v_st_995_, 4);
v_write_1001_ = lean_ctor_get(v_st_995_, 5);
v_read_1002_ = lean_ctor_get(v_st_995_, 6);
v_receivers_1003_ = lean_ctor_get(v_st_995_, 7);
v_nextId_1004_ = lean_ctor_get(v_st_995_, 8);
v_closed_1005_ = lean_ctor_get_uint8(v_st_995_, sizeof(void*)*10);
v_pos_1006_ = lean_ctor_get(v_st_995_, 9);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_st_995_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1008_ = v_st_995_;
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_pos_1006_);
lean_inc(v_nextId_1004_);
lean_inc(v_receivers_1003_);
lean_inc(v_read_1002_);
lean_inc(v_write_1001_);
lean_inc(v_buffer_1000_);
lean_inc(v_size_999_);
lean_inc(v_capacity_998_);
lean_inc(v_waiters_997_);
lean_inc(v_producers_996_);
lean_dec(v_st_995_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1017_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v_size_1011_; lean_object* v___x_1012_; lean_object* v_read_1013_; lean_object* v___x_1015_; 
v___x_1010_ = lean_unsigned_to_nat(1u);
v_size_1011_ = lean_nat_sub(v_size_999_, v___x_1010_);
lean_dec(v_size_999_);
v___x_1012_ = lean_nat_add(v_read_1002_, v___x_1010_);
lean_dec(v_read_1002_);
v_read_1013_ = lean_nat_mod(v___x_1012_, v_capacity_998_);
lean_dec(v___x_1012_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 6, v_read_1013_);
lean_ctor_set(v___x_1008_, 3, v_size_1011_);
v___x_1015_ = v___x_1008_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_producers_996_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_waiters_997_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_capacity_998_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_size_1011_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v_buffer_1000_);
lean_ctor_set(v_reuseFailAlloc_1016_, 5, v_write_1001_);
lean_ctor_set(v_reuseFailAlloc_1016_, 6, v_read_1013_);
lean_ctor_set(v_reuseFailAlloc_1016_, 7, v_receivers_1003_);
lean_ctor_set(v_reuseFailAlloc_1016_, 8, v_nextId_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 9, v_pos_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, sizeof(void*)*10, v_closed_1005_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue(lean_object* v_00_u03b1_1018_, lean_object* v_st_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_st_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(lean_object* v_toApplicative_1021_, lean_object* v_place_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_capacity_1024_; lean_object* v_buffer_1025_; lean_object* v_toPure_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_capacity_1024_ = lean_ctor_get(v_a_1023_, 2);
v_buffer_1025_ = lean_ctor_get(v_a_1023_, 4);
v_toPure_1026_ = lean_ctor_get(v_toApplicative_1021_, 1);
lean_inc(v_toPure_1026_);
lean_dec_ref(v_toApplicative_1021_);
v___x_1027_ = lean_nat_mod(v_place_1022_, v_capacity_1024_);
v___x_1028_ = lean_array_fget_borrowed(v_buffer_1025_, v___x_1027_);
lean_dec(v___x_1027_);
lean_inc(v___x_1028_);
v___x_1029_ = lean_apply_2(v_toPure_1026_, lean_box(0), v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed(lean_object* v_toApplicative_1030_, lean_object* v_place_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(v_toApplicative_1030_, v_place_1031_, v_a_1032_);
lean_dec_ref(v_a_1032_);
lean_dec(v_place_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_place_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_toApplicative_1038_; lean_object* v_toBind_1039_; lean_object* v___f_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_toApplicative_1038_ = lean_ctor_get(v_inst_1034_, 0);
lean_inc_ref(v_toApplicative_1038_);
v_toBind_1039_ = lean_ctor_get(v_inst_1034_, 1);
lean_inc(v_toBind_1039_);
lean_dec_ref(v_inst_1034_);
v___f_1040_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1040_, 0, v_toApplicative_1038_);
lean_closure_set(v___f_1040_, 1, v_place_1036_);
lean_inc(v_a_1037_);
v___x_1041_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1041_, 0, lean_box(0));
lean_closure_set(v___x_1041_, 1, lean_box(0));
lean_closure_set(v___x_1041_, 2, v_a_1037_);
v___x_1042_ = lean_apply_2(v_inst_1035_, lean_box(0), v___x_1041_);
v___x_1043_ = lean_apply_4(v_toBind_1039_, lean_box(0), lean_box(0), v___x_1042_, v___f_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___boxed(lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_place_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1044_, v_inst_1045_, v_place_1046_, v_a_1047_);
lean_dec(v_a_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(lean_object* v_m_1049_, lean_object* v_00_u03b1_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_place_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1051_, v_inst_1052_, v_place_1053_, v_a_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___boxed(lean_object* v_m_1056_, lean_object* v_00_u03b1_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_place_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(v_m_1056_, v_00_u03b1_1057_, v_inst_1058_, v_inst_1059_, v_place_1060_, v_a_1061_);
lean_dec(v_a_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(lean_object* v_as_1063_, size_t v_sz_1064_, size_t v_i_1065_, lean_object* v_b_1066_){
_start:
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_usize_dec_lt(v_i_1065_, v_sz_1064_);
if (v___x_1068_ == 0)
{
return v_b_1066_;
}
else
{
lean_object* v___x_1069_; lean_object* v_a_1070_; lean_object* v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; 
v___x_1069_ = lean_box(0);
v_a_1070_ = lean_array_uget_borrowed(v_as_1063_, v_i_1065_);
v___x_1071_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1070_, v___x_1068_);
v___x_1072_ = ((size_t)1ULL);
v___x_1073_ = lean_usize_add(v_i_1065_, v___x_1072_);
v_i_1065_ = v___x_1073_;
v_b_1066_ = v___x_1069_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg___boxed(lean_object* v_as_1075_, lean_object* v_sz_1076_, lean_object* v_i_1077_, lean_object* v_b_1078_, lean_object* v___y_1079_){
_start:
{
size_t v_sz_boxed_1080_; size_t v_i_boxed_1081_; lean_object* v_res_1082_; 
v_sz_boxed_1080_ = lean_unbox_usize(v_sz_1076_);
lean_dec(v_sz_1076_);
v_i_boxed_1081_ = lean_unbox_usize(v_i_1077_);
lean_dec(v_i_1077_);
v_res_1082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1075_, v_sz_boxed_1080_, v_i_boxed_1081_, v_b_1078_);
lean_dec_ref(v_as_1075_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(lean_object* v_v_1083_, lean_object* v_a_1084_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_1084_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_producers_1089_; lean_object* v_waiters_1090_; lean_object* v_capacity_1091_; lean_object* v_size_1092_; lean_object* v_buffer_1093_; lean_object* v_write_1094_; lean_object* v_read_1095_; lean_object* v_receivers_1096_; lean_object* v_nextId_1097_; uint8_t v_closed_1098_; lean_object* v_pos_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1118_; 
v___x_1087_ = lean_st_ref_get(v_a_1084_);
v___x_1088_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_v_1083_, v___x_1087_);
v_producers_1089_ = lean_ctor_get(v___x_1088_, 0);
v_waiters_1090_ = lean_ctor_get(v___x_1088_, 1);
v_capacity_1091_ = lean_ctor_get(v___x_1088_, 2);
v_size_1092_ = lean_ctor_get(v___x_1088_, 3);
v_buffer_1093_ = lean_ctor_get(v___x_1088_, 4);
v_write_1094_ = lean_ctor_get(v___x_1088_, 5);
v_read_1095_ = lean_ctor_get(v___x_1088_, 6);
v_receivers_1096_ = lean_ctor_get(v___x_1088_, 7);
v_nextId_1097_ = lean_ctor_get(v___x_1088_, 8);
v_closed_1098_ = lean_ctor_get_uint8(v___x_1088_, sizeof(void*)*10);
v_pos_1099_ = lean_ctor_get(v___x_1088_, 9);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1101_ = v___x_1088_;
v_isShared_1102_ = v_isSharedCheck_1118_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_pos_1099_);
lean_inc(v_nextId_1097_);
lean_inc(v_receivers_1096_);
lean_inc(v_read_1095_);
lean_inc(v_write_1094_);
lean_inc(v_buffer_1093_);
lean_inc(v_size_1092_);
lean_inc(v_capacity_1091_);
lean_inc(v_waiters_1090_);
lean_inc(v_producers_1089_);
lean_dec(v___x_1088_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1118_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1103_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
lean_inc(v_receivers_1096_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___x_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_producers_1089_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_capacity_1091_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_size_1092_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_buffer_1093_);
lean_ctor_set(v_reuseFailAlloc_1117_, 5, v_write_1094_);
lean_ctor_set(v_reuseFailAlloc_1117_, 6, v_read_1095_);
lean_ctor_set(v_reuseFailAlloc_1117_, 7, v_receivers_1096_);
lean_ctor_set(v_reuseFailAlloc_1117_, 8, v_nextId_1097_);
lean_ctor_set(v_reuseFailAlloc_1117_, 9, v_pos_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1117_, sizeof(void*)*10, v_closed_1098_);
v___x_1105_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; size_t v_sz_1109_; size_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___y_1113_; 
v___x_1106_ = lean_st_ref_swap(v_a_1084_, v___x_1105_);
lean_dec(v___x_1106_);
v___x_1107_ = l_Std_Queue_toArray___redArg(v_waiters_1090_);
v___x_1108_ = lean_box(0);
v_sz_1109_ = lean_array_size(v___x_1107_);
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v___x_1107_, v_sz_1109_, v___x_1110_, v___x_1108_);
lean_dec_ref(v___x_1107_);
if (lean_obj_tag(v_receivers_1096_) == 0)
{
lean_object* v_size_1115_; 
v_size_1115_ = lean_ctor_get(v_receivers_1096_, 0);
lean_inc(v_size_1115_);
lean_dec_ref_known(v_receivers_1096_, 5);
v___y_1113_ = v_size_1115_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_unsigned_to_nat(0u);
v___y_1113_ = v___x_1116_;
goto v___jp_1112_;
}
v___jp_1112_:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___y_1113_);
return v___x_1114_;
}
}
}
}
else
{
lean_object* v___x_1119_; 
lean_dec(v_v_1083_);
v___x_1119_ = lean_box(0);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1120_, v_a_1121_);
lean_dec(v_a_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(lean_object* v_00_u03b1_1124_, lean_object* v_v_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1125_, v_a_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_v_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(v_00_u03b1_1129_, v_v_1130_, v_a_1131_);
lean_dec(v_a_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(lean_object* v_00_u03b1_1134_, lean_object* v_as_1135_, size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1135_, v_sz_1136_, v_i_1137_, v_b_1138_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1142_, lean_object* v_as_1143_, lean_object* v_sz_1144_, lean_object* v_i_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
size_t v_sz_boxed_1149_; size_t v_i_boxed_1150_; lean_object* v_res_1151_; 
v_sz_boxed_1149_ = lean_unbox_usize(v_sz_1144_);
lean_dec(v_sz_1144_);
v_i_boxed_1150_ = lean_unbox_usize(v_i_1145_);
lean_dec(v_i_1145_);
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(v_00_u03b1_1142_, v_as_1143_, v_sz_boxed_1149_, v_i_boxed_1150_, v_b_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v_as_1143_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(lean_object* v_mutex_1152_, lean_object* v_k_1153_){
_start:
{
lean_object* v_ref_1155_; lean_object* v_mutex_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_ref_1155_ = lean_ctor_get(v_mutex_1152_, 0);
lean_inc(v_ref_1155_);
v_mutex_1156_ = lean_ctor_get(v_mutex_1152_, 1);
lean_inc(v_mutex_1156_);
lean_dec_ref(v_mutex_1152_);
v___x_1157_ = lean_io_basemutex_lock(v_mutex_1156_);
v___x_1158_ = lean_apply_2(v_k_1153_, v_ref_1155_, lean_box(0));
v___x_1159_ = lean_io_basemutex_unlock(v_mutex_1156_);
lean_dec(v_mutex_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg___boxed(lean_object* v_mutex_1160_, lean_object* v_k_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1160_, v_k_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_mutex_1166_, lean_object* v_k_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1166_, v_k_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_1170_, lean_object* v_00_u03b2_1171_, lean_object* v_mutex_1172_, lean_object* v_k_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(v_00_u03b1_1170_, v_00_u03b2_1171_, v_mutex_1172_, v_k_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(lean_object* v_v_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; uint8_t v_closed_1182_; 
v___x_1181_ = lean_st_ref_get(v___y_1179_);
v_closed_1182_ = lean_ctor_get_uint8(v___x_1181_, sizeof(void*)*10);
lean_dec(v___x_1181_);
if (v_closed_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v_receivers_1184_; 
v___x_1183_ = lean_st_ref_get(v___y_1179_);
v_receivers_1184_ = lean_ctor_get(v___x_1183_, 7);
lean_inc(v_receivers_1184_);
lean_dec(v___x_1183_);
if (lean_obj_tag(v_receivers_1184_) == 0)
{
lean_object* v___x_1185_; 
lean_dec_ref_known(v_receivers_1184_, 5);
v___x_1185_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1178_, v___y_1179_);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; 
lean_dec(v_v_1178_);
v___x_1186_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0));
return v___x_1186_;
}
}
else
{
lean_object* v___x_1187_; 
lean_dec(v_v_1178_);
v___x_1187_ = lean_box(0);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(v_v_1188_, v___y_1189_);
lean_dec(v___y_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(lean_object* v_ch_1192_, lean_object* v_v_1193_){
_start:
{
lean_object* v___f_1195_; lean_object* v___x_1196_; 
v___f_1195_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1195_, 0, v_v_1193_);
v___x_1196_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1192_, v___f_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___boxed(lean_object* v_ch_1197_, lean_object* v_v_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1197_, v_v_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(lean_object* v_00_u03b1_1201_, lean_object* v_ch_1202_, lean_object* v_v_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1202_, v_v_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___boxed(lean_object* v_00_u03b1_1206_, lean_object* v_ch_1207_, lean_object* v_v_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(v_00_u03b1_1206_, v_ch_1207_, v_v_1208_);
return v_res_1210_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0));
v___x_1214_ = lean_task_pure(v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2));
v___x_1219_ = lean_task_pure(v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(lean_object* v_v_1220_, lean_object* v___f_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; uint8_t v_closed_1225_; 
v___x_1224_ = lean_st_ref_get(v___y_1222_);
v_closed_1225_ = lean_ctor_get_uint8(v___x_1224_, sizeof(void*)*10);
lean_dec(v___x_1224_);
if (v_closed_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v_receivers_1227_; 
v___x_1226_ = lean_st_ref_get(v___y_1222_);
v_receivers_1227_ = lean_ctor_get(v___x_1226_, 7);
lean_inc(v_receivers_1227_);
lean_dec(v___x_1226_);
if (lean_obj_tag(v_receivers_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref_known(v_receivers_1227_, 5);
v___x_1228_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1220_, v___y_1222_);
if (lean_obj_tag(v___x_1228_) == 1)
{
lean_object* v_val_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v___f_1221_);
v_val_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_val_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1237_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_val_1229_);
v___x_1234_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_task_pure(v___x_1234_);
return v___x_1235_;
}
}
}
else
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_producers_1240_; lean_object* v_waiters_1241_; lean_object* v_capacity_1242_; lean_object* v_size_1243_; lean_object* v_buffer_1244_; lean_object* v_write_1245_; lean_object* v_read_1246_; lean_object* v_receivers_1247_; lean_object* v_nextId_1248_; uint8_t v_closed_1249_; lean_object* v_pos_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v___x_1228_);
v___x_1238_ = lean_io_promise_new();
v___x_1239_ = lean_st_ref_take(v___y_1222_);
v_producers_1240_ = lean_ctor_get(v___x_1239_, 0);
v_waiters_1241_ = lean_ctor_get(v___x_1239_, 1);
v_capacity_1242_ = lean_ctor_get(v___x_1239_, 2);
v_size_1243_ = lean_ctor_get(v___x_1239_, 3);
v_buffer_1244_ = lean_ctor_get(v___x_1239_, 4);
v_write_1245_ = lean_ctor_get(v___x_1239_, 5);
v_read_1246_ = lean_ctor_get(v___x_1239_, 6);
v_receivers_1247_ = lean_ctor_get(v___x_1239_, 7);
v_nextId_1248_ = lean_ctor_get(v___x_1239_, 8);
v_closed_1249_ = lean_ctor_get_uint8(v___x_1239_, sizeof(void*)*10);
v_pos_1250_ = lean_ctor_get(v___x_1239_, 9);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1252_ = v___x_1239_;
v_isShared_1253_ = v_isSharedCheck_1262_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_pos_1250_);
lean_inc(v_nextId_1248_);
lean_inc(v_receivers_1247_);
lean_inc(v_read_1246_);
lean_inc(v_write_1245_);
lean_inc(v_buffer_1244_);
lean_inc(v_size_1243_);
lean_inc(v_capacity_1242_);
lean_inc(v_waiters_1241_);
lean_inc(v_producers_1240_);
lean_dec(v___x_1239_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1262_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
lean_inc(v___x_1238_);
v___x_1254_ = l_Std_Queue_enqueue___redArg(v___x_1238_, v_producers_1240_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v___x_1254_);
v___x_1256_ = v___x_1252_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_waiters_1241_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_capacity_1242_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_size_1243_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_buffer_1244_);
lean_ctor_set(v_reuseFailAlloc_1261_, 5, v_write_1245_);
lean_ctor_set(v_reuseFailAlloc_1261_, 6, v_read_1246_);
lean_ctor_set(v_reuseFailAlloc_1261_, 7, v_receivers_1247_);
lean_ctor_set(v_reuseFailAlloc_1261_, 8, v_nextId_1248_);
lean_ctor_set(v_reuseFailAlloc_1261_, 9, v_pos_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1261_, sizeof(void*)*10, v_closed_1249_);
v___x_1256_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1257_ = lean_st_ref_put(v___y_1222_, v___x_1256_);
v___x_1258_ = lean_io_promise_result_opt(v___x_1238_);
lean_dec(v___x_1238_);
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_io_bind_task(v___x_1258_, v___f_1221_, v___x_1259_, v_closed_1225_);
return v___x_1260_;
}
}
}
}
else
{
lean_object* v___x_1263_; 
lean_dec_ref(v___f_1221_);
lean_dec(v_v_1220_);
v___x_1263_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1);
return v___x_1263_;
}
}
else
{
lean_object* v___x_1264_; 
lean_dec_ref(v___f_1221_);
lean_dec(v_v_1220_);
v___x_1264_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_1265_, lean_object* v___f_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(v_v_1265_, v___f_1266_, v___y_1267_);
lean_dec(v___y_1267_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(lean_object* v_ch_1270_, lean_object* v_v_1271_, lean_object* v_res_1272_){
_start:
{
if (lean_obj_tag(v_res_1272_) == 0)
{
lean_dec(v_v_1271_);
lean_dec_ref(v_ch_1270_);
goto v___jp_1274_;
}
else
{
lean_object* v_val_1276_; uint8_t v___x_1277_; 
v_val_1276_ = lean_ctor_get(v_res_1272_, 0);
v___x_1277_ = lean_unbox(v_val_1276_);
if (v___x_1277_ == 0)
{
lean_dec(v_v_1271_);
lean_dec_ref(v_ch_1270_);
goto v___jp_1274_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1270_, v_v_1271_);
return v___x_1278_;
}
}
v___jp_1274_:
{
lean_object* v___x_1275_; 
v___x_1275_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_1279_, lean_object* v_v_1280_, lean_object* v_res_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(v_ch_1279_, v_v_1280_, v_res_1281_);
lean_dec(v_res_1281_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(lean_object* v_ch_1284_, lean_object* v_v_1285_){
_start:
{
lean_object* v___f_1287_; lean_object* v___f_1288_; lean_object* v___x_1289_; 
lean_inc(v_v_1285_);
lean_inc_ref(v_ch_1284_);
v___f_1287_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1287_, 0, v_ch_1284_);
lean_closure_set(v___f_1287_, 1, v_v_1285_);
v___f_1288_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1288_, 0, v_v_1285_);
lean_closure_set(v___f_1288_, 1, v___f_1287_);
v___x_1289_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1284_, v___f_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___boxed(lean_object* v_ch_1290_, lean_object* v_v_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1290_, v_v_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send(lean_object* v_00_u03b1_1294_, lean_object* v_ch_1295_, lean_object* v_v_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1295_, v_v_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_ch_1300_, lean_object* v_v_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send(v_00_u03b1_1299_, v_ch_1300_, v_v_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(lean_object* v_mutex_1304_, lean_object* v_k_1305_){
_start:
{
lean_object* v_ref_1307_; lean_object* v_mutex_1308_; lean_object* v___x_1309_; lean_object* v_r_1310_; 
v_ref_1307_ = lean_ctor_get(v_mutex_1304_, 0);
lean_inc(v_ref_1307_);
v_mutex_1308_ = lean_ctor_get(v_mutex_1304_, 1);
lean_inc(v_mutex_1308_);
lean_dec_ref(v_mutex_1304_);
v___x_1309_ = lean_io_basemutex_lock(v_mutex_1308_);
v_r_1310_ = lean_apply_2(v_k_1305_, v_ref_1307_, lean_box(0));
if (lean_obj_tag(v_r_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1319_; 
v_a_1311_ = lean_ctor_get(v_r_1310_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_r_1310_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1313_ = v_r_1310_;
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v_r_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1319_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = lean_io_basemutex_unlock(v_mutex_1308_);
lean_dec(v_mutex_1308_);
if (v_isShared_1314_ == 0)
{
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1311_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
v_a_1320_ = lean_ctor_get(v_r_1310_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_r_1310_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1322_ = v_r_1310_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v_r_1310_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_io_basemutex_unlock(v_mutex_1308_);
lean_dec(v_mutex_1308_);
if (v_isShared_1323_ == 0)
{
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1320_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg___boxed(lean_object* v_mutex_1329_, lean_object* v_k_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_mutex_1329_, v_k_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2(lean_object* v_00_u03b1_1333_, lean_object* v_00_u03b2_1334_, lean_object* v_mutex_1335_, lean_object* v_k_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_mutex_1335_, v_k_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_00_u03b2_1340_, lean_object* v_mutex_1341_, lean_object* v_k_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2(v_00_u03b1_1339_, v_00_u03b2_1340_, v_mutex_1341_, v_k_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(uint8_t v___x_1345_, lean_object* v_as_1346_, size_t v_sz_1347_, size_t v_i_1348_, lean_object* v_b_1349_){
_start:
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_usize_dec_lt(v_i_1348_, v_sz_1347_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v_b_1349_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v_a_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; size_t v___x_1357_; size_t v___x_1358_; 
v___x_1353_ = lean_box(0);
v_a_1354_ = lean_array_uget_borrowed(v_as_1346_, v_i_1348_);
v___x_1355_ = lean_box(v___x_1345_);
v___x_1356_ = lean_io_promise_resolve(v___x_1355_, v_a_1354_);
v___x_1357_ = ((size_t)1ULL);
v___x_1358_ = lean_usize_add(v_i_1348_, v___x_1357_);
v_i_1348_ = v___x_1358_;
v_b_1349_ = v___x_1353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object* v___x_1360_, lean_object* v_as_1361_, lean_object* v_sz_1362_, lean_object* v_i_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v___x_2113__boxed_1366_; size_t v_sz_boxed_1367_; size_t v_i_boxed_1368_; lean_object* v_res_1369_; 
v___x_2113__boxed_1366_ = lean_unbox(v___x_1360_);
v_sz_boxed_1367_ = lean_unbox_usize(v_sz_1362_);
lean_dec(v_sz_1362_);
v_i_boxed_1368_ = lean_unbox_usize(v_i_1363_);
lean_dec(v_i_1363_);
v_res_1369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v___x_2113__boxed_1366_, v_as_1361_, v_sz_boxed_1367_, v_i_boxed_1368_, v_b_1364_);
lean_dec_ref(v_as_1361_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(uint8_t v___x_1370_, lean_object* v_as_1371_, size_t v_sz_1372_, size_t v_i_1373_, lean_object* v_b_1374_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_lt(v_i_1373_, v_sz_1372_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_b_1374_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; lean_object* v_a_1379_; lean_object* v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; 
v___x_1378_ = lean_box(0);
v_a_1379_ = lean_array_uget_borrowed(v_as_1371_, v_i_1373_);
v___x_1380_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1379_, v___x_1370_);
v___x_1381_ = ((size_t)1ULL);
v___x_1382_ = lean_usize_add(v_i_1373_, v___x_1381_);
v_i_1373_ = v___x_1382_;
v_b_1374_ = v___x_1378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_1384_, lean_object* v_as_1385_, lean_object* v_sz_1386_, lean_object* v_i_1387_, lean_object* v_b_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v___x_2135__boxed_1390_; size_t v_sz_boxed_1391_; size_t v_i_boxed_1392_; lean_object* v_res_1393_; 
v___x_2135__boxed_1390_ = lean_unbox(v___x_1384_);
v_sz_boxed_1391_ = lean_unbox_usize(v_sz_1386_);
lean_dec(v_sz_1386_);
v_i_boxed_1392_ = lean_unbox_usize(v_i_1387_);
lean_dec(v_i_1387_);
v_res_1393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_2135__boxed_1390_, v_as_1385_, v_sz_boxed_1391_, v_i_boxed_1392_, v_b_1388_);
lean_dec_ref(v_as_1385_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; uint8_t v_closed_1397_; 
v___x_1396_ = lean_st_ref_get(v___y_1394_);
v_closed_1397_ = lean_ctor_get_uint8(v___x_1396_, sizeof(void*)*10);
if (v_closed_1397_ == 0)
{
lean_object* v_producers_1398_; lean_object* v_waiters_1399_; lean_object* v_capacity_1400_; lean_object* v_size_1401_; lean_object* v_buffer_1402_; lean_object* v_write_1403_; lean_object* v_read_1404_; lean_object* v_receivers_1405_; lean_object* v_nextId_1406_; lean_object* v_pos_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1433_; 
v_producers_1398_ = lean_ctor_get(v___x_1396_, 0);
v_waiters_1399_ = lean_ctor_get(v___x_1396_, 1);
v_capacity_1400_ = lean_ctor_get(v___x_1396_, 2);
v_size_1401_ = lean_ctor_get(v___x_1396_, 3);
v_buffer_1402_ = lean_ctor_get(v___x_1396_, 4);
v_write_1403_ = lean_ctor_get(v___x_1396_, 5);
v_read_1404_ = lean_ctor_get(v___x_1396_, 6);
v_receivers_1405_ = lean_ctor_get(v___x_1396_, 7);
v_nextId_1406_ = lean_ctor_get(v___x_1396_, 8);
v_pos_1407_ = lean_ctor_get(v___x_1396_, 9);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1409_ = v___x_1396_;
v_isShared_1410_ = v_isSharedCheck_1433_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_pos_1407_);
lean_inc(v_nextId_1406_);
lean_inc(v_receivers_1405_);
lean_inc(v_read_1404_);
lean_inc(v_write_1403_);
lean_inc(v_buffer_1402_);
lean_inc(v_size_1401_);
lean_inc(v_capacity_1400_);
lean_inc(v_waiters_1399_);
lean_inc(v_producers_1398_);
lean_dec(v___x_1396_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1433_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; size_t v_sz_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1411_ = l_Std_Queue_toArray___redArg(v_waiters_1399_);
v___x_1412_ = lean_box(0);
v_sz_1413_ = lean_array_size(v___x_1411_);
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v_closed_1397_, v___x_1411_, v_sz_1413_, v___x_1414_, v___x_1412_);
lean_dec_ref(v___x_1411_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; size_t v_sz_1417_; lean_object* v___x_1418_; 
lean_dec_ref_known(v___x_1415_, 1);
v___x_1416_ = l_Std_Queue_toArray___redArg(v_producers_1398_);
v_sz_1417_ = lean_array_size(v___x_1416_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_closed_1397_, v___x_1416_, v_sz_1417_, v___x_1414_, v___x_1412_);
lean_dec_ref(v___x_1416_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1431_; 
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1418_, 0);
lean_dec(v_unused_1432_);
v___x_1420_ = v___x_1418_;
v_isShared_1421_ = v_isSharedCheck_1431_;
goto v_resetjp_1419_;
}
else
{
lean_dec(v___x_1418_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1431_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; uint8_t v___x_1423_; lean_object* v___x_1425_; 
v___x_1422_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_1423_ = 1;
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___x_1422_);
lean_ctor_set(v___x_1409_, 0, v___x_1422_);
v___x_1425_ = v___x_1409_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_capacity_1400_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_size_1401_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v_buffer_1402_);
lean_ctor_set(v_reuseFailAlloc_1430_, 5, v_write_1403_);
lean_ctor_set(v_reuseFailAlloc_1430_, 6, v_read_1404_);
lean_ctor_set(v_reuseFailAlloc_1430_, 7, v_receivers_1405_);
lean_ctor_set(v_reuseFailAlloc_1430_, 8, v_nextId_1406_);
lean_ctor_set(v_reuseFailAlloc_1430_, 9, v_pos_1407_);
v___x_1425_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*10, v___x_1423_);
v___x_1426_ = lean_st_ref_swap(v___y_1394_, v___x_1425_);
lean_dec(v___x_1426_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1412_);
v___x_1428_ = v___x_1420_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1412_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_del_object(v___x_1409_);
lean_dec(v_pos_1407_);
lean_dec(v_nextId_1406_);
lean_dec(v_receivers_1405_);
lean_dec(v_read_1404_);
lean_dec(v_write_1403_);
lean_dec_ref(v_buffer_1402_);
lean_dec(v_size_1401_);
lean_dec(v_capacity_1400_);
return v___x_1418_;
}
}
else
{
lean_del_object(v___x_1409_);
lean_dec(v_pos_1407_);
lean_dec(v_nextId_1406_);
lean_dec(v_receivers_1405_);
lean_dec(v_read_1404_);
lean_dec(v_write_1403_);
lean_dec_ref(v_buffer_1402_);
lean_dec(v_size_1401_);
lean_dec(v_capacity_1400_);
lean_dec_ref(v_producers_1398_);
return v___x_1415_;
}
}
}
else
{
uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v___x_1396_);
v___x_1434_ = 1;
v___x_1435_ = lean_box(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(v___y_1437_);
lean_dec(v___y_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(lean_object* v_ch_1441_){
_start:
{
lean_object* v___f_1443_; lean_object* v___x_1444_; 
v___f_1443_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0));
v___x_1444_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_ch_1441_, v___f_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___boxed(lean_object* v_ch_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1445_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_object* v_00_u03b1_1448_, lean_object* v_ch_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___boxed(lean_object* v_00_u03b1_1452_, lean_object* v_ch_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close(v_00_u03b1_1452_, v_ch_1453_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_object* v_00_u03b1_1456_, uint8_t v___x_1457_, lean_object* v_as_1458_, size_t v_sz_1459_, size_t v_i_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1457_, v_as_1458_, v_sz_1459_, v_i_1460_, v_b_1461_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_1465_, lean_object* v___x_1466_, lean_object* v_as_1467_, lean_object* v_sz_1468_, lean_object* v_i_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v___x_2237__boxed_1473_; size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v___x_2237__boxed_1473_ = lean_unbox(v___x_1466_);
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1468_);
lean_dec(v_sz_1468_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1465_, v___x_2237__boxed_1473_, v_as_1467_, v_sz_boxed_1474_, v_i_boxed_1475_, v_b_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v_as_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object* v_00_u03b1_1477_, uint8_t v___x_1478_, lean_object* v_as_1479_, size_t v_sz_1480_, size_t v_i_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v___x_1478_, v_as_1479_, v_sz_1480_, v_i_1481_, v_b_1482_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_1486_, lean_object* v___x_1487_, lean_object* v_as_1488_, lean_object* v_sz_1489_, lean_object* v_i_1490_, lean_object* v_b_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_2248__boxed_1494_; size_t v_sz_boxed_1495_; size_t v_i_boxed_1496_; lean_object* v_res_1497_; 
v___x_2248__boxed_1494_ = lean_unbox(v___x_1487_);
v_sz_boxed_1495_ = lean_unbox_usize(v_sz_1489_);
lean_dec(v_sz_1489_);
v_i_boxed_1496_ = lean_unbox_usize(v_i_1490_);
lean_dec(v_i_1490_);
v_res_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(v_00_u03b1_1486_, v___x_2248__boxed_1494_, v_as_1488_, v_sz_boxed_1495_, v_i_boxed_1496_, v_b_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v_as_1488_);
return v_res_1497_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; uint8_t v_closed_1501_; 
v___x_1500_ = lean_st_ref_get(v___y_1498_);
v_closed_1501_ = lean_ctor_get_uint8(v___x_1500_, sizeof(void*)*10);
lean_dec(v___x_1500_);
return v_closed_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v_res_1504_; lean_object* v_r_1505_; 
v_res_1504_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(v___y_1502_);
lean_dec(v___y_1502_);
v_r_1505_ = lean_box(v_res_1504_);
return v_r_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object* v_ch_1507_){
_start:
{
lean_object* v___f_1509_; lean_object* v___x_1510_; 
v___f_1509_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0));
v___x_1510_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1507_, v___f_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___boxed(lean_object* v_ch_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1511_);
return v_res_1513_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_object* v_00_u03b1_1514_, lean_object* v_ch_1515_){
_start:
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1515_);
v___x_1518_ = lean_unbox(v___x_1517_);
lean_dec(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_ch_1520_, lean_object* v_a_1521_){
_start:
{
uint8_t v_res_1522_; lean_object* v_r_1523_; 
v_res_1522_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(v_00_u03b1_1519_, v_ch_1520_);
v_r_1523_ = lean_box(v_res_1522_);
return v_r_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object* v_next_1524_, lean_object* v_slot_1525_){
_start:
{
lean_object* v_value_1526_; lean_object* v_pos_1527_; lean_object* v_remaining_1528_; uint8_t v___x_1529_; 
v_value_1526_ = lean_ctor_get(v_slot_1525_, 0);
v_pos_1527_ = lean_ctor_get(v_slot_1525_, 1);
v_remaining_1528_ = lean_ctor_get(v_slot_1525_, 2);
v___x_1529_ = lean_nat_dec_eq(v_next_1524_, v_pos_1527_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_box(v___x_1529_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v_slot_1525_);
return v___x_1533_;
}
else
{
lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1554_; 
lean_inc(v_remaining_1528_);
lean_inc(v_pos_1527_);
lean_inc(v_value_1526_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_slot_1525_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; lean_object* v_unused_1556_; lean_object* v_unused_1557_; 
v_unused_1555_ = lean_ctor_get(v_slot_1525_, 2);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_slot_1525_, 1);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_slot_1525_, 0);
lean_dec(v_unused_1557_);
v___x_1535_ = v_slot_1525_;
v_isShared_1536_ = v_isSharedCheck_1554_;
goto v_resetjp_1534_;
}
else
{
lean_dec(v_slot_1525_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1554_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = lean_nat_dec_eq(v_remaining_1528_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
v___x_1539_ = lean_box(v___x_1538_);
lean_inc(v_value_1526_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v_value_1526_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_nat_sub(v_remaining_1528_, v___x_1537_);
lean_dec(v_remaining_1528_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 2, v___x_1541_);
v___x_1543_ = v___x_1535_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_value_1526_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_pos_1527_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1540_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
return v___x_1544_;
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec(v_remaining_1528_);
v___x_1546_ = lean_box(v___x_1529_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_value_1526_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_unsigned_to_nat(0u);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 2, v___x_1549_);
lean_ctor_set(v___x_1535_, 0, v___x_1548_);
v___x_1551_ = v___x_1535_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_pos_1527_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
return v___x_1552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object* v_next_1558_, lean_object* v_slot_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(v_next_1558_, v_slot_1559_);
lean_dec(v_next_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object* v_inst_1561_, lean_object* v_slot_1562_, lean_object* v_next_1563_){
_start:
{
lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___f_1564_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1564_, 0, v_next_1563_);
v___x_1565_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1565_, 0, lean_box(0));
lean_closure_set(v___x_1565_, 1, lean_box(0));
lean_closure_set(v___x_1565_, 2, lean_box(0));
lean_closure_set(v___x_1565_, 3, v_slot_1562_);
lean_closure_set(v___x_1565_, 4, v___f_1564_);
v___x_1566_ = lean_apply_2(v_inst_1561_, lean_box(0), v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object* v_m_1567_, lean_object* v_00_u03b1_1568_, lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_slot_1571_, lean_object* v_next_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1570_, v_slot_1571_, v_next_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object* v_m_1575_, lean_object* v_00_u03b1_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_slot_1579_, lean_object* v_next_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(v_m_1575_, v_00_u03b1_1576_, v_inst_1577_, v_inst_1578_, v_slot_1579_, v_next_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_inst_1577_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object* v_toApplicative_1583_, lean_object* v_fst_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_toPure_1586_; lean_object* v___x_1587_; 
v_toPure_1586_ = lean_ctor_get(v_toApplicative_1583_, 1);
lean_inc(v_toPure_1586_);
lean_dec_ref(v_toApplicative_1583_);
v___x_1587_ = lean_apply_2(v_toPure_1586_, lean_box(0), v_fst_1584_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object* v_inst_1588_, lean_object* v_toBind_1589_, lean_object* v___f_1590_, lean_object* v_____r_1591_, lean_object* v_st_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_inc(v___y_1593_);
v___x_1594_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1594_, 0, lean_box(0));
lean_closure_set(v___x_1594_, 1, lean_box(0));
lean_closure_set(v___x_1594_, 2, v___y_1593_);
lean_closure_set(v___x_1594_, 3, v_st_1592_);
v___x_1595_ = lean_apply_2(v_inst_1588_, lean_box(0), v___x_1594_);
v___x_1596_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1595_, v___f_1590_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed(lean_object* v_inst_1597_, lean_object* v_toBind_1598_, lean_object* v___f_1599_, lean_object* v_____r_1600_, lean_object* v_st_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1597_, v_toBind_1598_, v___f_1599_, v_____r_1600_, v_st_1601_, v___y_1602_);
lean_dec(v___y_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object* v_snd_1604_, lean_object* v_waiters_1605_, lean_object* v_capacity_1606_, lean_object* v_size_1607_, lean_object* v_buffer_1608_, lean_object* v_write_1609_, lean_object* v_read_1610_, lean_object* v_receivers_1611_, lean_object* v_nextId_1612_, uint8_t v_closed_1613_, lean_object* v_pos_1614_, lean_object* v___f_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1618_, 0, v_snd_1604_);
lean_ctor_set(v___x_1618_, 1, v_waiters_1605_);
lean_ctor_set(v___x_1618_, 2, v_capacity_1606_);
lean_ctor_set(v___x_1618_, 3, v_size_1607_);
lean_ctor_set(v___x_1618_, 4, v_buffer_1608_);
lean_ctor_set(v___x_1618_, 5, v_write_1609_);
lean_ctor_set(v___x_1618_, 6, v_read_1610_);
lean_ctor_set(v___x_1618_, 7, v_receivers_1611_);
lean_ctor_set(v___x_1618_, 8, v_nextId_1612_);
lean_ctor_set(v___x_1618_, 9, v_pos_1614_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*10, v_closed_1613_);
v___x_1619_ = lean_box(0);
lean_inc(v_a_1616_);
v___x_1620_ = lean_apply_3(v___f_1615_, v___x_1619_, v___x_1618_, v_a_1616_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object* v_snd_1621_, lean_object* v_waiters_1622_, lean_object* v_capacity_1623_, lean_object* v_size_1624_, lean_object* v_buffer_1625_, lean_object* v_write_1626_, lean_object* v_read_1627_, lean_object* v_receivers_1628_, lean_object* v_nextId_1629_, lean_object* v_closed_1630_, lean_object* v_pos_1631_, lean_object* v___f_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
uint8_t v_closed_boxed_1635_; lean_object* v_res_1636_; 
v_closed_boxed_1635_ = lean_unbox(v_closed_1630_);
v_res_1636_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1621_, v_waiters_1622_, v_capacity_1623_, v_size_1624_, v_buffer_1625_, v_write_1626_, v_read_1627_, v_receivers_1628_, v_nextId_1629_, v_closed_boxed_1635_, v_pos_1631_, v___f_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1633_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object* v_toApplicative_1637_, lean_object* v_inst_1638_, lean_object* v_toBind_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, uint8_t v___x_1642_, lean_object* v_inst_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_fst_1645_; 
v_fst_1645_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_fst_1645_);
if (lean_obj_tag(v_fst_1645_) == 1)
{
lean_object* v_snd_1646_; lean_object* v___f_1647_; lean_object* v___f_1648_; uint8_t v___x_1649_; 
v_snd_1646_ = lean_ctor_get(v_a_1644_, 1);
lean_inc(v_snd_1646_);
lean_dec_ref(v_a_1644_);
v___f_1647_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1647_, 0, v_toApplicative_1637_);
lean_closure_set(v___f_1647_, 1, v_fst_1645_);
lean_inc_ref(v___f_1647_);
lean_inc(v_toBind_1639_);
lean_inc(v_inst_1638_);
v___f_1648_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1648_, 0, v_inst_1638_);
lean_closure_set(v___f_1648_, 1, v_toBind_1639_);
lean_closure_set(v___f_1648_, 2, v___f_1647_);
v___x_1649_ = lean_unbox(v_snd_1646_);
lean_dec(v_snd_1646_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec_ref(v___f_1648_);
lean_dec(v_inst_1643_);
v___x_1650_ = lean_box(0);
v___x_1651_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1638_, v_toBind_1639_, v___f_1647_, v___x_1650_, v_a_1640_, v_a_1641_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; lean_object* v_producers_1653_; lean_object* v_waiters_1654_; lean_object* v_capacity_1655_; lean_object* v_size_1656_; lean_object* v_buffer_1657_; lean_object* v_write_1658_; lean_object* v_read_1659_; lean_object* v_receivers_1660_; lean_object* v_nextId_1661_; uint8_t v_closed_1662_; lean_object* v_pos_1663_; lean_object* v___x_1664_; 
v___x_1652_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_1640_);
v_producers_1653_ = lean_ctor_get(v___x_1652_, 0);
v_waiters_1654_ = lean_ctor_get(v___x_1652_, 1);
v_capacity_1655_ = lean_ctor_get(v___x_1652_, 2);
v_size_1656_ = lean_ctor_get(v___x_1652_, 3);
v_buffer_1657_ = lean_ctor_get(v___x_1652_, 4);
v_write_1658_ = lean_ctor_get(v___x_1652_, 5);
v_read_1659_ = lean_ctor_get(v___x_1652_, 6);
v_receivers_1660_ = lean_ctor_get(v___x_1652_, 7);
v_nextId_1661_ = lean_ctor_get(v___x_1652_, 8);
v_closed_1662_ = lean_ctor_get_uint8(v___x_1652_, sizeof(void*)*10);
v_pos_1663_ = lean_ctor_get(v___x_1652_, 9);
lean_inc_ref(v_producers_1653_);
v___x_1664_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1653_);
if (lean_obj_tag(v___x_1664_) == 1)
{
lean_object* v_val_1665_; lean_object* v_fst_1666_; lean_object* v_snd_1667_; lean_object* v___x_1668_; lean_object* v___f_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_inc(v_pos_1663_);
lean_inc(v_nextId_1661_);
lean_inc(v_receivers_1660_);
lean_inc(v_read_1659_);
lean_inc(v_write_1658_);
lean_inc_ref(v_buffer_1657_);
lean_inc(v_size_1656_);
lean_inc(v_capacity_1655_);
lean_inc_ref(v_waiters_1654_);
lean_dec_ref(v___x_1652_);
lean_dec_ref(v___f_1647_);
lean_dec(v_inst_1638_);
v_val_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v___x_1664_, 1);
v_fst_1666_ = lean_ctor_get(v_val_1665_, 0);
lean_inc(v_fst_1666_);
v_snd_1667_ = lean_ctor_get(v_val_1665_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_val_1665_);
v___x_1668_ = lean_box(v_closed_1662_);
lean_inc(v_a_1641_);
v___f_1669_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1669_, 0, v_snd_1667_);
lean_closure_set(v___f_1669_, 1, v_waiters_1654_);
lean_closure_set(v___f_1669_, 2, v_capacity_1655_);
lean_closure_set(v___f_1669_, 3, v_size_1656_);
lean_closure_set(v___f_1669_, 4, v_buffer_1657_);
lean_closure_set(v___f_1669_, 5, v_write_1658_);
lean_closure_set(v___f_1669_, 6, v_read_1659_);
lean_closure_set(v___f_1669_, 7, v_receivers_1660_);
lean_closure_set(v___f_1669_, 8, v_nextId_1661_);
lean_closure_set(v___f_1669_, 9, v___x_1668_);
lean_closure_set(v___f_1669_, 10, v_pos_1663_);
lean_closure_set(v___f_1669_, 11, v___f_1648_);
lean_closure_set(v___f_1669_, 12, v_a_1641_);
v___x_1670_ = lean_box(v___x_1642_);
v___x_1671_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1671_, 0, lean_box(0));
lean_closure_set(v___x_1671_, 1, v___x_1670_);
lean_closure_set(v___x_1671_, 2, v_fst_1666_);
v___x_1672_ = lean_apply_2(v_inst_1643_, lean_box(0), v___x_1671_);
v___x_1673_ = lean_apply_4(v_toBind_1639_, lean_box(0), lean_box(0), v___x_1672_, v___f_1669_);
return v___x_1673_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v___x_1664_);
lean_dec_ref(v___f_1648_);
lean_dec(v_inst_1643_);
v___x_1674_ = lean_box(0);
v___x_1675_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1638_, v_toBind_1639_, v___f_1647_, v___x_1674_, v___x_1652_, v_a_1641_);
return v___x_1675_;
}
}
}
else
{
lean_object* v_toPure_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v_fst_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_inst_1643_);
lean_dec_ref(v_a_1640_);
lean_dec(v_toBind_1639_);
lean_dec(v_inst_1638_);
v_toPure_1676_ = lean_ctor_get(v_toApplicative_1637_, 1);
lean_inc(v_toPure_1676_);
lean_dec_ref(v_toApplicative_1637_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_apply_2(v_toPure_1676_, lean_box(0), v___x_1677_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object* v_toApplicative_1679_, lean_object* v_inst_1680_, lean_object* v_toBind_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v___x_1684_, lean_object* v_inst_1685_, lean_object* v_a_1686_){
_start:
{
uint8_t v___x_789__boxed_1687_; lean_object* v_res_1688_; 
v___x_789__boxed_1687_ = lean_unbox(v___x_1684_);
v_res_1688_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1679_, v_inst_1680_, v_toBind_1681_, v_a_1682_, v_a_1683_, v___x_789__boxed_1687_, v_inst_1685_, v_a_1686_);
lean_dec(v_a_1683_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object* v_inst_1689_, lean_object* v_next_1690_, lean_object* v_toBind_1691_, lean_object* v___f_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1689_, v_a_1693_, v_next_1690_);
v___x_1695_ = lean_apply_4(v_toBind_1691_, lean_box(0), lean_box(0), v___x_1694_, v___f_1692_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object* v_a_1696_, lean_object* v_toApplicative_1697_, lean_object* v_inst_1698_, lean_object* v_toBind_1699_, lean_object* v_a_1700_, lean_object* v_inst_1701_, lean_object* v_next_1702_, lean_object* v_inst_1703_, uint8_t v_a_1704_){
_start:
{
if (v_a_1704_ == 0)
{
lean_object* v_capacity_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_capacity_1705_ = lean_ctor_get(v_a_1696_, 2);
lean_inc(v_capacity_1705_);
v___x_1706_ = 1;
v___x_1707_ = lean_box(v___x_1706_);
lean_inc(v_a_1700_);
lean_inc_n(v_toBind_1699_, 2);
lean_inc_n(v_inst_1698_, 2);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1708_, 0, v_toApplicative_1697_);
lean_closure_set(v___f_1708_, 1, v_inst_1698_);
lean_closure_set(v___f_1708_, 2, v_toBind_1699_);
lean_closure_set(v___f_1708_, 3, v_a_1696_);
lean_closure_set(v___f_1708_, 4, v_a_1700_);
lean_closure_set(v___f_1708_, 5, v___x_1707_);
lean_closure_set(v___f_1708_, 6, v_inst_1701_);
lean_inc(v_next_1702_);
v___f_1709_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1709_, 0, v_inst_1698_);
lean_closure_set(v___f_1709_, 1, v_next_1702_);
lean_closure_set(v___f_1709_, 2, v_toBind_1699_);
lean_closure_set(v___f_1709_, 3, v___f_1708_);
v___x_1710_ = lean_nat_mod(v_next_1702_, v_capacity_1705_);
lean_dec(v_capacity_1705_);
lean_dec(v_next_1702_);
v___x_1711_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1703_, v_inst_1698_, v___x_1710_, v_a_1700_);
v___x_1712_ = lean_apply_4(v_toBind_1699_, lean_box(0), lean_box(0), v___x_1711_, v___f_1709_);
return v___x_1712_;
}
else
{
lean_object* v_toPure_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v_inst_1703_);
lean_dec(v_next_1702_);
lean_dec(v_inst_1701_);
lean_dec(v_toBind_1699_);
lean_dec(v_inst_1698_);
lean_dec_ref(v_a_1696_);
v_toPure_1713_ = lean_ctor_get(v_toApplicative_1697_, 1);
lean_inc(v_toPure_1713_);
lean_dec_ref(v_toApplicative_1697_);
v___x_1714_ = lean_box(0);
v___x_1715_ = lean_apply_2(v_toPure_1713_, lean_box(0), v___x_1714_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object* v_a_1716_, lean_object* v_toApplicative_1717_, lean_object* v_inst_1718_, lean_object* v_toBind_1719_, lean_object* v_a_1720_, lean_object* v_inst_1721_, lean_object* v_next_1722_, lean_object* v_inst_1723_, lean_object* v_a_1724_){
_start:
{
uint8_t v_a_boxed_1725_; lean_object* v_res_1726_; 
v_a_boxed_1725_ = lean_unbox(v_a_1724_);
v_res_1726_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1716_, v_toApplicative_1717_, v_inst_1718_, v_toBind_1719_, v_a_1720_, v_inst_1721_, v_next_1722_, v_inst_1723_, v_a_boxed_1725_);
lean_dec(v_a_1720_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object* v_toApplicative_1727_, lean_object* v_inst_1728_, lean_object* v_toBind_1729_, lean_object* v_a_1730_, lean_object* v_inst_1731_, lean_object* v_next_1732_, lean_object* v_inst_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_inc_ref(v_inst_1733_);
lean_inc(v_a_1730_);
lean_inc(v_toBind_1729_);
lean_inc(v_inst_1728_);
v___f_1735_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_1735_, 0, v_a_1734_);
lean_closure_set(v___f_1735_, 1, v_toApplicative_1727_);
lean_closure_set(v___f_1735_, 2, v_inst_1728_);
lean_closure_set(v___f_1735_, 3, v_toBind_1729_);
lean_closure_set(v___f_1735_, 4, v_a_1730_);
lean_closure_set(v___f_1735_, 5, v_inst_1731_);
lean_closure_set(v___f_1735_, 6, v_next_1732_);
lean_closure_set(v___f_1735_, 7, v_inst_1733_);
v___x_1736_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_1733_, v_inst_1728_, v_a_1730_);
v___x_1737_ = lean_apply_4(v_toBind_1729_, lean_box(0), lean_box(0), v___x_1736_, v___f_1735_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed(lean_object* v_toApplicative_1738_, lean_object* v_inst_1739_, lean_object* v_toBind_1740_, lean_object* v_a_1741_, lean_object* v_inst_1742_, lean_object* v_next_1743_, lean_object* v_inst_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(v_toApplicative_1738_, v_inst_1739_, v_toBind_1740_, v_a_1741_, v_inst_1742_, v_next_1743_, v_inst_1744_, v_a_1745_);
lean_dec(v_a_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_inst_1749_, lean_object* v_next_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_toApplicative_1752_; lean_object* v_toBind_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_toApplicative_1752_ = lean_ctor_get(v_inst_1747_, 0);
lean_inc_ref(v_toApplicative_1752_);
v_toBind_1753_ = lean_ctor_get(v_inst_1747_, 1);
lean_inc_n(v_toBind_1753_, 2);
lean_inc_n(v_a_1751_, 2);
lean_inc(v_inst_1748_);
v___f_1754_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_1754_, 0, v_toApplicative_1752_);
lean_closure_set(v___f_1754_, 1, v_inst_1748_);
lean_closure_set(v___f_1754_, 2, v_toBind_1753_);
lean_closure_set(v___f_1754_, 3, v_a_1751_);
lean_closure_set(v___f_1754_, 4, v_inst_1749_);
lean_closure_set(v___f_1754_, 5, v_next_1750_);
lean_closure_set(v___f_1754_, 6, v_inst_1747_);
v___x_1755_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1755_, 0, lean_box(0));
lean_closure_set(v___x_1755_, 1, lean_box(0));
lean_closure_set(v___x_1755_, 2, v_a_1751_);
v___x_1756_ = lean_apply_2(v_inst_1748_, lean_box(0), v___x_1755_);
v___x_1757_ = lean_apply_4(v_toBind_1753_, lean_box(0), lean_box(0), v___x_1756_, v___f_1754_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___boxed(lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_next_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1758_, v_inst_1759_, v_inst_1760_, v_next_1761_, v_a_1762_);
lean_dec(v_a_1762_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object* v_m_1764_, lean_object* v_00_u03b1_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_next_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1766_, v_inst_1767_, v_inst_1768_, v_next_1769_, v_a_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___boxed(lean_object* v_m_1772_, lean_object* v_00_u03b1_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_next_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(v_m_1772_, v_00_u03b1_1773_, v_inst_1774_, v_inst_1775_, v_inst_1776_, v_next_1777_, v_a_1778_);
lean_dec(v_a_1778_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1783_; lean_object* v_capacity_1784_; lean_object* v_buffer_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1783_ = lean_st_ref_get(v_a_1781_);
v_capacity_1784_ = lean_ctor_get(v___x_1783_, 2);
lean_inc(v_capacity_1784_);
v_buffer_1785_ = lean_ctor_get(v___x_1783_, 4);
lean_inc_ref(v_buffer_1785_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_nat_mod(v_place_1780_, v_capacity_1784_);
lean_dec(v_capacity_1784_);
v___x_1787_ = lean_array_fget(v_buffer_1785_, v___x_1786_);
lean_dec(v___x_1786_);
lean_dec_ref(v_buffer_1785_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_1789_, lean_object* v_a_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_1789_, v_a_1790_);
lean_dec(v_a_1790_);
lean_dec(v_place_1789_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_1793_){
_start:
{
lean_object* v___x_1795_; lean_object* v_size_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = lean_st_ref_get(v_a_1793_);
v_size_1796_ = lean_ctor_get(v___x_1795_, 3);
lean_inc(v_size_1796_);
lean_dec(v___x_1795_);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_nat_dec_eq(v_size_1796_, v___x_1797_);
lean_dec(v_size_1796_);
v___x_1799_ = lean_box(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1801_);
lean_dec(v_a_1801_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_1804_, lean_object* v_next_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v_fst_1809_; lean_object* v_snd_1810_; lean_object* v_value_1813_; lean_object* v_pos_1814_; lean_object* v_remaining_1815_; uint8_t v___x_1816_; 
v___x_1807_ = lean_st_ref_take(v_slot_1804_);
v_value_1813_ = lean_ctor_get(v___x_1807_, 0);
v_pos_1814_ = lean_ctor_get(v___x_1807_, 1);
v_remaining_1815_ = lean_ctor_get(v___x_1807_, 2);
v___x_1816_ = lean_nat_dec_eq(v_next_1805_, v_pos_1814_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_box(v___x_1816_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v_fst_1809_ = v___x_1819_;
v_snd_1810_ = v___x_1807_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1838_; 
lean_inc(v_remaining_1815_);
lean_inc(v_pos_1814_);
lean_inc(v_value_1813_);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; lean_object* v_unused_1840_; lean_object* v_unused_1841_; 
v_unused_1839_ = lean_ctor_get(v___x_1807_, 2);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v___x_1807_, 1);
lean_dec(v_unused_1840_);
v_unused_1841_ = lean_ctor_get(v___x_1807_, 0);
lean_dec(v_unused_1841_);
v___x_1821_ = v___x_1807_;
v_isShared_1822_ = v_isSharedCheck_1838_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v___x_1807_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1838_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = lean_unsigned_to_nat(1u);
v___x_1824_ = lean_nat_dec_eq(v_remaining_1815_, v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1825_ = lean_box(v___x_1824_);
lean_inc(v_value_1813_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_value_1813_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_nat_sub(v_remaining_1815_, v___x_1823_);
lean_dec(v_remaining_1815_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 2, v___x_1827_);
v___x_1829_ = v___x_1821_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_value_1813_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_pos_1814_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
v_fst_1809_ = v___x_1826_;
v_snd_1810_ = v___x_1829_;
goto v___jp_1808_;
}
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec(v_remaining_1815_);
v___x_1831_ = lean_box(v___x_1816_);
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v_value_1813_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = lean_box(0);
v___x_1834_ = lean_unsigned_to_nat(0u);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 2, v___x_1834_);
lean_ctor_set(v___x_1821_, 0, v___x_1833_);
v___x_1836_ = v___x_1821_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_pos_1814_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
v_fst_1809_ = v___x_1832_;
v_snd_1810_ = v___x_1836_;
goto v___jp_1808_;
}
}
}
}
v___jp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_st_ref_put(v_slot_1804_, v_snd_1810_);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_fst_1809_);
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_1842_, lean_object* v_next_1843_, lean_object* v___y_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_1842_, v_next_1843_);
lean_dec(v_next_1843_);
lean_dec(v_slot_1842_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1924_; 
v___x_1849_ = lean_st_ref_get(v_a_1847_);
v___x_1850_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1847_);
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1924_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1924_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_unbox(v_a_1851_);
lean_dec(v_a_1851_);
if (v___x_1855_ == 0)
{
lean_object* v_capacity_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1919_; 
lean_del_object(v___x_1853_);
v_capacity_1856_ = lean_ctor_get(v___x_1849_, 2);
v___x_1857_ = 1;
v___x_1858_ = lean_nat_mod(v_next_1846_, v_capacity_1856_);
v___x_1859_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_1858_, v_a_1847_);
lean_dec(v___x_1858_);
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1919_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1919_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1918_; 
v___x_1864_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_1860_, v_next_1846_);
lean_dec(v_a_1860_);
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1918_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1918_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_fst_1869_; lean_object* v_snd_1870_; lean_object* v_st_1872_; lean_object* v___y_1873_; 
v_fst_1869_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_fst_1869_);
v_snd_1870_ = lean_ctor_get(v_a_1865_, 1);
lean_inc(v_snd_1870_);
lean_dec(v_a_1865_);
if (lean_obj_tag(v_fst_1869_) == 1)
{
uint8_t v___x_1878_; 
lean_del_object(v___x_1862_);
v___x_1878_ = lean_unbox(v_snd_1870_);
lean_dec(v_snd_1870_);
if (v___x_1878_ == 0)
{
v_st_1872_ = v___x_1849_;
v___y_1873_ = v_a_1847_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1879_; lean_object* v_producers_1880_; lean_object* v_waiters_1881_; lean_object* v_capacity_1882_; lean_object* v_size_1883_; lean_object* v_buffer_1884_; lean_object* v_write_1885_; lean_object* v_read_1886_; lean_object* v_receivers_1887_; lean_object* v_nextId_1888_; uint8_t v_closed_1889_; lean_object* v_pos_1890_; lean_object* v___x_1891_; 
v___x_1879_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_1849_);
v_producers_1880_ = lean_ctor_get(v___x_1879_, 0);
v_waiters_1881_ = lean_ctor_get(v___x_1879_, 1);
v_capacity_1882_ = lean_ctor_get(v___x_1879_, 2);
v_size_1883_ = lean_ctor_get(v___x_1879_, 3);
v_buffer_1884_ = lean_ctor_get(v___x_1879_, 4);
v_write_1885_ = lean_ctor_get(v___x_1879_, 5);
v_read_1886_ = lean_ctor_get(v___x_1879_, 6);
v_receivers_1887_ = lean_ctor_get(v___x_1879_, 7);
v_nextId_1888_ = lean_ctor_get(v___x_1879_, 8);
v_closed_1889_ = lean_ctor_get_uint8(v___x_1879_, sizeof(void*)*10);
v_pos_1890_ = lean_ctor_get(v___x_1879_, 9);
lean_inc_ref(v_producers_1880_);
v___x_1891_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1880_);
if (lean_obj_tag(v___x_1891_) == 1)
{
lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1903_; 
lean_inc(v_pos_1890_);
lean_inc(v_nextId_1888_);
lean_inc(v_receivers_1887_);
lean_inc(v_read_1886_);
lean_inc(v_write_1885_);
lean_inc_ref(v_buffer_1884_);
lean_inc(v_size_1883_);
lean_inc(v_capacity_1882_);
lean_inc_ref(v_waiters_1881_);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; lean_object* v_unused_1908_; lean_object* v_unused_1909_; lean_object* v_unused_1910_; lean_object* v_unused_1911_; lean_object* v_unused_1912_; lean_object* v_unused_1913_; 
v_unused_1904_ = lean_ctor_get(v___x_1879_, 9);
lean_dec(v_unused_1904_);
v_unused_1905_ = lean_ctor_get(v___x_1879_, 8);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v___x_1879_, 7);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v___x_1879_, 6);
lean_dec(v_unused_1907_);
v_unused_1908_ = lean_ctor_get(v___x_1879_, 5);
lean_dec(v_unused_1908_);
v_unused_1909_ = lean_ctor_get(v___x_1879_, 4);
lean_dec(v_unused_1909_);
v_unused_1910_ = lean_ctor_get(v___x_1879_, 3);
lean_dec(v_unused_1910_);
v_unused_1911_ = lean_ctor_get(v___x_1879_, 2);
lean_dec(v_unused_1911_);
v_unused_1912_ = lean_ctor_get(v___x_1879_, 1);
lean_dec(v_unused_1912_);
v_unused_1913_ = lean_ctor_get(v___x_1879_, 0);
lean_dec(v_unused_1913_);
v___x_1893_ = v___x_1879_;
v_isShared_1894_ = v_isSharedCheck_1903_;
goto v_resetjp_1892_;
}
else
{
lean_dec(v___x_1879_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1903_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_val_1895_; lean_object* v_fst_1896_; lean_object* v_snd_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v_val_1895_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_val_1895_);
lean_dec_ref_known(v___x_1891_, 1);
v_fst_1896_ = lean_ctor_get(v_val_1895_, 0);
lean_inc(v_fst_1896_);
v_snd_1897_ = lean_ctor_get(v_val_1895_, 1);
lean_inc(v_snd_1897_);
lean_dec(v_val_1895_);
v___x_1898_ = lean_box(v___x_1857_);
v___x_1899_ = lean_io_promise_resolve(v___x_1898_, v_fst_1896_);
lean_dec(v_fst_1896_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_snd_1897_);
v___x_1901_ = v___x_1893_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_snd_1897_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_waiters_1881_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_capacity_1882_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_size_1883_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_buffer_1884_);
lean_ctor_set(v_reuseFailAlloc_1902_, 5, v_write_1885_);
lean_ctor_set(v_reuseFailAlloc_1902_, 6, v_read_1886_);
lean_ctor_set(v_reuseFailAlloc_1902_, 7, v_receivers_1887_);
lean_ctor_set(v_reuseFailAlloc_1902_, 8, v_nextId_1888_);
lean_ctor_set(v_reuseFailAlloc_1902_, 9, v_pos_1890_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*10, v_closed_1889_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v_st_1872_ = v___x_1901_;
v___y_1873_ = v_a_1847_;
goto v___jp_1871_;
}
}
}
else
{
lean_dec(v___x_1891_);
v_st_1872_ = v___x_1879_;
v___y_1873_ = v_a_1847_;
goto v___jp_1871_;
}
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec(v_snd_1870_);
lean_dec(v_fst_1869_);
lean_del_object(v___x_1867_);
lean_dec(v___x_1849_);
v___x_1914_ = lean_box(0);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1914_);
v___x_1916_ = v___x_1862_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
v___jp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_st_ref_swap(v___y_1873_, v_st_1872_);
lean_dec(v___x_1874_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_fst_1869_);
v___x_1876_ = v___x_1867_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_fst_1869_);
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
lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_dec(v___x_1849_);
v___x_1920_ = lean_box(0);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1920_);
v___x_1922_ = v___x_1853_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_1925_, lean_object* v_a_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_1925_, v_a_1926_);
lean_dec(v_a_1926_);
lean_dec(v_next_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_a_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_fst_1932_; lean_object* v_snd_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1970_; 
v_fst_1932_ = lean_ctor_get(v_a_1929_, 0);
v_snd_1933_ = lean_ctor_get(v_a_1929_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_a_1929_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1935_ = v_a_1929_;
v_isShared_1936_ = v_isSharedCheck_1970_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_snd_1933_);
lean_inc(v_fst_1932_);
lean_dec(v_a_1929_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1970_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_size_1942_; lean_object* v_pos_1943_; uint8_t v___x_1944_; 
v_size_1942_ = lean_ctor_get(v_fst_1932_, 3);
v_pos_1943_ = lean_ctor_get(v_fst_1932_, 9);
v___x_1944_ = lean_nat_dec_lt(v_snd_1933_, v_pos_1943_);
if (v___x_1944_ == 0)
{
goto v___jp_1937_;
}
else
{
lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_nat_dec_lt(v___x_1945_, v_size_1942_);
if (v___x_1946_ == 0)
{
goto v___jp_1937_;
}
else
{
lean_object* v___x_1947_; 
lean_del_object(v___x_1935_);
v___x_1947_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_1933_, v___y_1930_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1961_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1961_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1961_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
if (lean_obj_tag(v_a_1948_) == 1)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec_ref_known(v_a_1948_, 1);
lean_del_object(v___x_1950_);
lean_dec(v_fst_1932_);
v___x_1952_ = lean_st_ref_get(v___y_1930_);
v___x_1953_ = lean_unsigned_to_nat(1u);
v___x_1954_ = lean_nat_add(v_snd_1933_, v___x_1953_);
lean_dec(v_snd_1933_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1952_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v_a_1929_ = v___x_1955_;
goto _start;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
lean_dec(v_a_1948_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_fst_1932_);
lean_ctor_set(v___x_1957_, 1, v_snd_1933_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1957_);
v___x_1959_ = v___x_1950_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_snd_1933_);
lean_dec(v_fst_1932_);
v_a_1962_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1947_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1947_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
v___jp_1937_:
{
lean_object* v___x_1939_; 
if (v_isShared_1936_ == 0)
{
v___x_1939_ = v___x_1935_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_fst_1932_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_snd_1933_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_a_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_1971_, v___y_1972_);
lean_dec(v___y_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_1975_, lean_object* v_k_1976_){
_start:
{
if (lean_obj_tag(v_t_1975_) == 0)
{
lean_object* v_k_1977_; lean_object* v_v_1978_; lean_object* v_l_1979_; lean_object* v_r_1980_; uint8_t v___x_1981_; 
v_k_1977_ = lean_ctor_get(v_t_1975_, 1);
v_v_1978_ = lean_ctor_get(v_t_1975_, 2);
v_l_1979_ = lean_ctor_get(v_t_1975_, 3);
v_r_1980_ = lean_ctor_get(v_t_1975_, 4);
v___x_1981_ = lean_nat_dec_lt(v_k_1976_, v_k_1977_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_nat_dec_eq(v_k_1976_, v_k_1977_);
if (v___x_1982_ == 0)
{
v_t_1975_ = v_r_1980_;
goto _start;
}
else
{
lean_object* v___x_1984_; 
lean_inc(v_v_1978_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v_v_1978_);
return v___x_1984_;
}
}
else
{
v_t_1975_ = v_l_1979_;
goto _start;
}
}
else
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_box(0);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_1987_, lean_object* v_k_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_1987_, v_k_1988_);
lean_dec(v_k_1988_);
lean_dec(v_t_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_1990_, lean_object* v_t_1991_){
_start:
{
if (lean_obj_tag(v_t_1991_) == 0)
{
lean_object* v_k_1992_; lean_object* v_v_1993_; lean_object* v_l_1994_; lean_object* v_r_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2650_; 
v_k_1992_ = lean_ctor_get(v_t_1991_, 1);
v_v_1993_ = lean_ctor_get(v_t_1991_, 2);
v_l_1994_ = lean_ctor_get(v_t_1991_, 3);
v_r_1995_ = lean_ctor_get(v_t_1991_, 4);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_t_1991_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v_t_1991_, 0);
lean_dec(v_unused_2651_);
v___x_1997_ = v_t_1991_;
v_isShared_1998_ = v_isSharedCheck_2650_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_r_1995_);
lean_inc(v_l_1994_);
lean_inc(v_v_1993_);
lean_inc(v_k_1992_);
lean_dec(v_t_1991_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2650_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_nat_dec_lt(v_k_1990_, v_k_1992_);
if (v___x_1999_ == 0)
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_nat_dec_eq(v_k_1990_, v_k_1992_);
if (v___x_2000_ == 0)
{
lean_object* v_impl_2001_; lean_object* v___x_2002_; 
v_impl_2001_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1990_, v_r_1995_);
v___x_2002_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2001_) == 0)
{
if (lean_obj_tag(v_l_1994_) == 0)
{
lean_object* v_size_2003_; lean_object* v_size_2004_; lean_object* v_k_2005_; lean_object* v_v_2006_; lean_object* v_l_2007_; lean_object* v_r_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v_size_2003_ = lean_ctor_get(v_impl_2001_, 0);
v_size_2004_ = lean_ctor_get(v_l_1994_, 0);
v_k_2005_ = lean_ctor_get(v_l_1994_, 1);
v_v_2006_ = lean_ctor_get(v_l_1994_, 2);
v_l_2007_ = lean_ctor_get(v_l_1994_, 3);
v_r_2008_ = lean_ctor_get(v_l_1994_, 4);
lean_inc(v_r_2008_);
v___x_2009_ = lean_unsigned_to_nat(3u);
v___x_2010_ = lean_nat_mul(v___x_2009_, v_size_2003_);
v___x_2011_ = lean_nat_dec_lt(v___x_2010_, v_size_2004_);
lean_dec(v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
lean_dec(v_r_2008_);
v___x_2012_ = lean_nat_add(v___x_2002_, v_size_2004_);
v___x_2013_ = lean_nat_add(v___x_2012_, v_size_2003_);
lean_dec(v___x_2012_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_impl_2001_);
lean_ctor_set(v___x_1997_, 0, v___x_2013_);
v___x_2015_ = v___x_1997_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_l_1994_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_impl_2001_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
else
{
lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2082_; 
lean_inc(v_l_2007_);
lean_inc(v_v_2006_);
lean_inc(v_k_2005_);
lean_inc(v_size_2004_);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; lean_object* v_unused_2084_; lean_object* v_unused_2085_; lean_object* v_unused_2086_; lean_object* v_unused_2087_; 
v_unused_2083_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2084_);
v_unused_2085_ = lean_ctor_get(v_l_1994_, 2);
lean_dec(v_unused_2085_);
v_unused_2086_ = lean_ctor_get(v_l_1994_, 1);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v_l_1994_, 0);
lean_dec(v_unused_2087_);
v___x_2018_ = v_l_1994_;
v_isShared_2019_ = v_isSharedCheck_2082_;
goto v_resetjp_2017_;
}
else
{
lean_dec(v_l_1994_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2082_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_size_2020_; lean_object* v_size_2021_; lean_object* v_k_2022_; lean_object* v_v_2023_; lean_object* v_l_2024_; lean_object* v_r_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_size_2020_ = lean_ctor_get(v_l_2007_, 0);
v_size_2021_ = lean_ctor_get(v_r_2008_, 0);
v_k_2022_ = lean_ctor_get(v_r_2008_, 1);
v_v_2023_ = lean_ctor_get(v_r_2008_, 2);
v_l_2024_ = lean_ctor_get(v_r_2008_, 3);
v_r_2025_ = lean_ctor_get(v_r_2008_, 4);
v___x_2026_ = lean_unsigned_to_nat(2u);
v___x_2027_ = lean_nat_mul(v___x_2026_, v_size_2020_);
v___x_2028_ = lean_nat_dec_lt(v_size_2021_, v___x_2027_);
lean_dec(v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2057_; 
lean_inc(v_r_2025_);
lean_inc(v_l_2024_);
lean_inc(v_v_2023_);
lean_inc(v_k_2022_);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_r_2008_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; lean_object* v_unused_2059_; lean_object* v_unused_2060_; lean_object* v_unused_2061_; lean_object* v_unused_2062_; 
v_unused_2058_ = lean_ctor_get(v_r_2008_, 4);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_r_2008_, 3);
lean_dec(v_unused_2059_);
v_unused_2060_ = lean_ctor_get(v_r_2008_, 2);
lean_dec(v_unused_2060_);
v_unused_2061_ = lean_ctor_get(v_r_2008_, 1);
lean_dec(v_unused_2061_);
v_unused_2062_ = lean_ctor_get(v_r_2008_, 0);
lean_dec(v_unused_2062_);
v___x_2030_ = v_r_2008_;
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v_r_2008_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2057_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___x_2045_; lean_object* v___y_2047_; 
v___x_2032_ = lean_nat_add(v___x_2002_, v_size_2004_);
lean_dec(v_size_2004_);
v___x_2033_ = lean_nat_add(v___x_2032_, v_size_2003_);
lean_dec(v___x_2032_);
v___x_2045_ = lean_nat_add(v___x_2002_, v_size_2020_);
if (lean_obj_tag(v_l_2024_) == 0)
{
lean_object* v_size_2055_; 
v_size_2055_ = lean_ctor_get(v_l_2024_, 0);
lean_inc(v_size_2055_);
v___y_2047_ = v_size_2055_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_unsigned_to_nat(0u);
v___y_2047_ = v___x_2056_;
goto v___jp_2046_;
}
v___jp_2034_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_nat_add(v___y_2035_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec(v___y_2035_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 4, v_impl_2001_);
lean_ctor_set(v___x_2030_, 3, v_r_2025_);
lean_ctor_set(v___x_2030_, 2, v_v_1993_);
lean_ctor_set(v___x_2030_, 1, v_k_1992_);
lean_ctor_set(v___x_2030_, 0, v___x_2038_);
v___x_2040_ = v___x_2030_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_r_2025_);
lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_impl_2001_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 4, v___x_2040_);
lean_ctor_set(v___x_2018_, 3, v___y_2036_);
lean_ctor_set(v___x_2018_, 2, v_v_2023_);
lean_ctor_set(v___x_2018_, 1, v_k_2022_);
lean_ctor_set(v___x_2018_, 0, v___x_2033_);
v___x_2042_ = v___x_2018_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_k_2022_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_v_2023_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v___y_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
v___jp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_nat_add(v___x_2045_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec(v___x_2045_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_l_2024_);
lean_ctor_set(v___x_1997_, 3, v_l_2007_);
lean_ctor_set(v___x_1997_, 2, v_v_2006_);
lean_ctor_set(v___x_1997_, 1, v_k_2005_);
lean_ctor_set(v___x_1997_, 0, v___x_2048_);
v___x_2050_ = v___x_1997_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_k_2005_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_v_2006_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_l_2007_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_l_2024_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_nat_add(v___x_2002_, v_size_2003_);
if (lean_obj_tag(v_r_2025_) == 0)
{
lean_object* v_size_2052_; 
v_size_2052_ = lean_ctor_get(v_r_2025_, 0);
lean_inc(v_size_2052_);
v___y_2035_ = v___x_2051_;
v___y_2036_ = v___x_2050_;
v___y_2037_ = v_size_2052_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_unsigned_to_nat(0u);
v___y_2035_ = v___x_2051_;
v___y_2036_ = v___x_2050_;
v___y_2037_ = v___x_2053_;
goto v___jp_2034_;
}
}
}
}
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
lean_del_object(v___x_1997_);
v___x_2063_ = lean_nat_add(v___x_2002_, v_size_2004_);
lean_dec(v_size_2004_);
v___x_2064_ = lean_nat_add(v___x_2063_, v_size_2003_);
lean_dec(v___x_2063_);
v___x_2065_ = lean_nat_add(v___x_2002_, v_size_2003_);
v___x_2066_ = lean_nat_add(v___x_2065_, v_size_2021_);
lean_dec(v___x_2065_);
lean_inc_ref(v_impl_2001_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 4, v_impl_2001_);
lean_ctor_set(v___x_2018_, 3, v_r_2008_);
lean_ctor_set(v___x_2018_, 2, v_v_1993_);
lean_ctor_set(v___x_2018_, 1, v_k_1992_);
lean_ctor_set(v___x_2018_, 0, v___x_2066_);
v___x_2068_ = v___x_2018_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_r_2008_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_impl_2001_);
v___x_2068_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_isSharedCheck_2075_ = !lean_is_exclusive(v_impl_2001_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; lean_object* v_unused_2077_; lean_object* v_unused_2078_; lean_object* v_unused_2079_; lean_object* v_unused_2080_; 
v_unused_2076_ = lean_ctor_get(v_impl_2001_, 4);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_impl_2001_, 3);
lean_dec(v_unused_2077_);
v_unused_2078_ = lean_ctor_get(v_impl_2001_, 2);
lean_dec(v_unused_2078_);
v_unused_2079_ = lean_ctor_get(v_impl_2001_, 1);
lean_dec(v_unused_2079_);
v_unused_2080_ = lean_ctor_get(v_impl_2001_, 0);
lean_dec(v_unused_2080_);
v___x_2070_ = v_impl_2001_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_dec(v_impl_2001_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v___x_2068_);
lean_ctor_set(v___x_2070_, 3, v_l_2007_);
lean_ctor_set(v___x_2070_, 2, v_v_2006_);
lean_ctor_set(v___x_2070_, 1, v_k_2005_);
lean_ctor_set(v___x_2070_, 0, v___x_2064_);
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_2005_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_2006_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_l_2007_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v___x_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v_size_2088_ = lean_ctor_get(v_impl_2001_, 0);
v___x_2089_ = lean_nat_add(v___x_2002_, v_size_2088_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_impl_2001_);
lean_ctor_set(v___x_1997_, 0, v___x_2089_);
v___x_2091_ = v___x_1997_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2092_, 3, v_l_1994_);
lean_ctor_set(v_reuseFailAlloc_2092_, 4, v_impl_2001_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
else
{
if (lean_obj_tag(v_l_1994_) == 0)
{
lean_object* v_l_2093_; 
v_l_2093_ = lean_ctor_get(v_l_1994_, 3);
if (lean_obj_tag(v_l_2093_) == 0)
{
lean_object* v_r_2094_; 
lean_inc_ref(v_l_2093_);
v_r_2094_ = lean_ctor_get(v_l_1994_, 4);
lean_inc(v_r_2094_);
if (lean_obj_tag(v_r_2094_) == 0)
{
lean_object* v_size_2095_; lean_object* v_k_2096_; lean_object* v_v_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2110_; 
v_size_2095_ = lean_ctor_get(v_l_1994_, 0);
v_k_2096_ = lean_ctor_get(v_l_1994_, 1);
v_v_2097_ = lean_ctor_get(v_l_1994_, 2);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; lean_object* v_unused_2112_; 
v_unused_2111_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2112_);
v___x_2099_ = v_l_1994_;
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_v_2097_);
lean_inc(v_k_2096_);
lean_inc(v_size_2095_);
lean_dec(v_l_1994_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_size_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v_size_2101_ = lean_ctor_get(v_r_2094_, 0);
v___x_2102_ = lean_nat_add(v___x_2002_, v_size_2095_);
lean_dec(v_size_2095_);
v___x_2103_ = lean_nat_add(v___x_2002_, v_size_2101_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 4, v_impl_2001_);
lean_ctor_set(v___x_2099_, 3, v_r_2094_);
lean_ctor_set(v___x_2099_, 2, v_v_1993_);
lean_ctor_set(v___x_2099_, 1, v_k_1992_);
lean_ctor_set(v___x_2099_, 0, v___x_2103_);
v___x_2105_ = v___x_2099_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_r_2094_);
lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_impl_2001_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v___x_2105_);
lean_ctor_set(v___x_1997_, 3, v_l_2093_);
lean_ctor_set(v___x_1997_, 2, v_v_2097_);
lean_ctor_set(v___x_1997_, 1, v_k_2096_);
lean_ctor_set(v___x_1997_, 0, v___x_2102_);
v___x_2107_ = v___x_1997_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_k_2096_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_v_2097_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_l_2093_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v___x_2105_);
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
lean_object* v_k_2113_; lean_object* v_v_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2125_; 
v_k_2113_ = lean_ctor_get(v_l_1994_, 1);
v_v_2114_ = lean_ctor_get(v_l_1994_, 2);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; lean_object* v_unused_2127_; lean_object* v_unused_2128_; 
v_unused_2126_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2126_);
v_unused_2127_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2127_);
v_unused_2128_ = lean_ctor_get(v_l_1994_, 0);
lean_dec(v_unused_2128_);
v___x_2116_ = v_l_1994_;
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
lean_dec(v_l_1994_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_unsigned_to_nat(3u);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 3, v_r_2094_);
lean_ctor_set(v___x_2116_, 2, v_v_1993_);
lean_ctor_set(v___x_2116_, 1, v_k_1992_);
lean_ctor_set(v___x_2116_, 0, v___x_2002_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v_r_2094_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_r_2094_);
v___x_2120_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2122_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v___x_2120_);
lean_ctor_set(v___x_1997_, 3, v_l_2093_);
lean_ctor_set(v___x_1997_, 2, v_v_2114_);
lean_ctor_set(v___x_1997_, 1, v_k_2113_);
lean_ctor_set(v___x_1997_, 0, v___x_2118_);
v___x_2122_ = v___x_1997_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2123_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2123_, 3, v_l_2093_);
lean_ctor_set(v_reuseFailAlloc_2123_, 4, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
else
{
lean_object* v_r_2129_; 
v_r_2129_ = lean_ctor_get(v_l_1994_, 4);
lean_inc(v_r_2129_);
if (lean_obj_tag(v_r_2129_) == 0)
{
lean_object* v_k_2130_; lean_object* v_v_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2154_; 
lean_inc(v_l_2093_);
v_k_2130_ = lean_ctor_get(v_l_1994_, 1);
v_v_2131_ = lean_ctor_get(v_l_1994_, 2);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; 
v_unused_2155_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_l_1994_, 0);
lean_dec(v_unused_2157_);
v___x_2133_ = v_l_1994_;
v_isShared_2134_ = v_isSharedCheck_2154_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_v_2131_);
lean_inc(v_k_2130_);
lean_dec(v_l_1994_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2154_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_k_2135_; lean_object* v_v_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2150_; 
v_k_2135_ = lean_ctor_get(v_r_2129_, 1);
v_v_2136_ = lean_ctor_get(v_r_2129_, 2);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_r_2129_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; lean_object* v_unused_2152_; lean_object* v_unused_2153_; 
v_unused_2151_ = lean_ctor_get(v_r_2129_, 4);
lean_dec(v_unused_2151_);
v_unused_2152_ = lean_ctor_get(v_r_2129_, 3);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_r_2129_, 0);
lean_dec(v_unused_2153_);
v___x_2138_ = v_r_2129_;
v_isShared_2139_ = v_isSharedCheck_2150_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_v_2136_);
lean_inc(v_k_2135_);
lean_dec(v_r_2129_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2150_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_unsigned_to_nat(3u);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 4, v_l_2093_);
lean_ctor_set(v___x_2138_, 3, v_l_2093_);
lean_ctor_set(v___x_2138_, 2, v_v_2131_);
lean_ctor_set(v___x_2138_, 1, v_k_2130_);
lean_ctor_set(v___x_2138_, 0, v___x_2002_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_k_2130_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_v_2131_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_l_2093_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_l_2093_);
v___x_2142_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_l_2093_);
lean_ctor_set(v___x_2133_, 2, v_v_1993_);
lean_ctor_set(v___x_2133_, 1, v_k_1992_);
lean_ctor_set(v___x_2133_, 0, v___x_2002_);
v___x_2144_ = v___x_2133_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2148_, 3, v_l_2093_);
lean_ctor_set(v_reuseFailAlloc_2148_, 4, v_l_2093_);
v___x_2144_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v___x_2144_);
lean_ctor_set(v___x_1997_, 3, v___x_2142_);
lean_ctor_set(v___x_1997_, 2, v_v_2136_);
lean_ctor_set(v___x_1997_, 1, v_k_2135_);
lean_ctor_set(v___x_1997_, 0, v___x_2140_);
v___x_2146_ = v___x_1997_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_k_2135_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_v_2136_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_unsigned_to_nat(2u);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_r_2129_);
lean_ctor_set(v___x_1997_, 0, v___x_2158_);
v___x_2160_ = v___x_1997_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_l_1994_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_r_2129_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v___x_2163_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_l_1994_);
lean_ctor_set(v___x_1997_, 0, v___x_2002_);
v___x_2163_ = v___x_1997_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_l_1994_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_l_1994_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_del_object(v___x_1997_);
lean_dec(v_v_1993_);
lean_dec(v_k_1992_);
if (lean_obj_tag(v_l_1994_) == 0)
{
if (lean_obj_tag(v_r_1995_) == 0)
{
lean_object* v_size_2165_; lean_object* v_k_2166_; lean_object* v_v_2167_; lean_object* v_l_2168_; lean_object* v_r_2169_; lean_object* v_size_2170_; lean_object* v_k_2171_; lean_object* v_v_2172_; lean_object* v_l_2173_; lean_object* v_r_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v_size_2165_ = lean_ctor_get(v_l_1994_, 0);
v_k_2166_ = lean_ctor_get(v_l_1994_, 1);
v_v_2167_ = lean_ctor_get(v_l_1994_, 2);
v_l_2168_ = lean_ctor_get(v_l_1994_, 3);
v_r_2169_ = lean_ctor_get(v_l_1994_, 4);
lean_inc(v_r_2169_);
v_size_2170_ = lean_ctor_get(v_r_1995_, 0);
v_k_2171_ = lean_ctor_get(v_r_1995_, 1);
v_v_2172_ = lean_ctor_get(v_r_1995_, 2);
v_l_2173_ = lean_ctor_get(v_r_1995_, 3);
lean_inc(v_l_2173_);
v_r_2174_ = lean_ctor_get(v_r_1995_, 4);
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_dec_lt(v_size_2165_, v_size_2170_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2312_; 
lean_inc(v_l_2168_);
lean_inc(v_v_2167_);
lean_inc(v_k_2166_);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; lean_object* v_unused_2316_; lean_object* v_unused_2317_; 
v_unused_2313_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_l_1994_, 2);
lean_dec(v_unused_2315_);
v_unused_2316_ = lean_ctor_get(v_l_1994_, 1);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_l_1994_, 0);
lean_dec(v_unused_2317_);
v___x_2178_ = v_l_1994_;
v_isShared_2179_ = v_isSharedCheck_2312_;
goto v_resetjp_2177_;
}
else
{
lean_dec(v_l_1994_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2312_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v_tree_2181_; 
v___x_2180_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2166_, v_v_2167_, v_l_2168_, v_r_2169_);
v_tree_2181_ = lean_ctor_get(v___x_2180_, 2);
if (lean_obj_tag(v_tree_2181_) == 0)
{
lean_object* v_k_2182_; lean_object* v_v_2183_; lean_object* v_size_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
lean_inc_ref(v_tree_2181_);
v_k_2182_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_k_2182_);
v_v_2183_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_v_2183_);
lean_dec_ref(v___x_2180_);
v_size_2184_ = lean_ctor_get(v_tree_2181_, 0);
v___x_2185_ = lean_unsigned_to_nat(3u);
v___x_2186_ = lean_nat_mul(v___x_2185_, v_size_2184_);
v___x_2187_ = lean_nat_dec_lt(v___x_2186_, v_size_2170_);
lean_dec(v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
lean_dec(v_l_2173_);
v___x_2188_ = lean_nat_add(v___x_2175_, v_size_2184_);
v___x_2189_ = lean_nat_add(v___x_2188_, v_size_2170_);
lean_dec(v___x_2188_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v_r_1995_);
lean_ctor_set(v___x_2178_, 3, v_tree_2181_);
lean_ctor_set(v___x_2178_, 2, v_v_2183_);
lean_ctor_set(v___x_2178_, 1, v_k_2182_);
lean_ctor_set(v___x_2178_, 0, v___x_2189_);
v___x_2191_ = v___x_2178_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_k_2182_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_v_2183_);
lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_tree_2181_);
lean_ctor_set(v_reuseFailAlloc_2192_, 4, v_r_1995_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
else
{
lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2247_; 
lean_inc(v_r_2174_);
lean_inc(v_v_2172_);
lean_inc(v_k_2171_);
lean_inc(v_size_2170_);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; lean_object* v_unused_2249_; lean_object* v_unused_2250_; lean_object* v_unused_2251_; lean_object* v_unused_2252_; 
v_unused_2248_ = lean_ctor_get(v_r_1995_, 4);
lean_dec(v_unused_2248_);
v_unused_2249_ = lean_ctor_get(v_r_1995_, 3);
lean_dec(v_unused_2249_);
v_unused_2250_ = lean_ctor_get(v_r_1995_, 2);
lean_dec(v_unused_2250_);
v_unused_2251_ = lean_ctor_get(v_r_1995_, 1);
lean_dec(v_unused_2251_);
v_unused_2252_ = lean_ctor_get(v_r_1995_, 0);
lean_dec(v_unused_2252_);
v___x_2194_ = v_r_1995_;
v_isShared_2195_ = v_isSharedCheck_2247_;
goto v_resetjp_2193_;
}
else
{
lean_dec(v_r_1995_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2247_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_size_2196_; lean_object* v_k_2197_; lean_object* v_v_2198_; lean_object* v_l_2199_; lean_object* v_r_2200_; lean_object* v_size_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_size_2196_ = lean_ctor_get(v_l_2173_, 0);
v_k_2197_ = lean_ctor_get(v_l_2173_, 1);
v_v_2198_ = lean_ctor_get(v_l_2173_, 2);
v_l_2199_ = lean_ctor_get(v_l_2173_, 3);
v_r_2200_ = lean_ctor_get(v_l_2173_, 4);
v_size_2201_ = lean_ctor_get(v_r_2174_, 0);
v___x_2202_ = lean_unsigned_to_nat(2u);
v___x_2203_ = lean_nat_mul(v___x_2202_, v_size_2201_);
v___x_2204_ = lean_nat_dec_lt(v_size_2196_, v___x_2203_);
lean_dec(v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2232_; 
lean_inc(v_r_2200_);
lean_inc(v_l_2199_);
lean_inc(v_v_2198_);
lean_inc(v_k_2197_);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_l_2173_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; lean_object* v_unused_2234_; lean_object* v_unused_2235_; lean_object* v_unused_2236_; lean_object* v_unused_2237_; 
v_unused_2233_ = lean_ctor_get(v_l_2173_, 4);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_l_2173_, 3);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_l_2173_, 2);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v_l_2173_, 1);
lean_dec(v_unused_2236_);
v_unused_2237_ = lean_ctor_get(v_l_2173_, 0);
lean_dec(v_unused_2237_);
v___x_2206_ = v_l_2173_;
v_isShared_2207_ = v_isSharedCheck_2232_;
goto v_resetjp_2205_;
}
else
{
lean_dec(v_l_2173_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2232_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2222_; 
v___x_2208_ = lean_nat_add(v___x_2175_, v_size_2184_);
v___x_2209_ = lean_nat_add(v___x_2208_, v_size_2170_);
lean_dec(v_size_2170_);
if (lean_obj_tag(v_l_2199_) == 0)
{
lean_object* v_size_2230_; 
v_size_2230_ = lean_ctor_get(v_l_2199_, 0);
lean_inc(v_size_2230_);
v___y_2222_ = v_size_2230_;
goto v___jp_2221_;
}
else
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_unsigned_to_nat(0u);
v___y_2222_ = v___x_2231_;
goto v___jp_2221_;
}
v___jp_2210_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = lean_nat_add(v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec(v___y_2212_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 4, v_r_2174_);
lean_ctor_set(v___x_2206_, 3, v_r_2200_);
lean_ctor_set(v___x_2206_, 2, v_v_2172_);
lean_ctor_set(v___x_2206_, 1, v_k_2171_);
lean_ctor_set(v___x_2206_, 0, v___x_2214_);
v___x_2216_ = v___x_2206_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_k_2171_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_v_2172_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v_r_2200_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v_r_2174_);
v___x_2216_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2218_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 4, v___x_2216_);
lean_ctor_set(v___x_2194_, 3, v___y_2211_);
lean_ctor_set(v___x_2194_, 2, v_v_2198_);
lean_ctor_set(v___x_2194_, 1, v_k_2197_);
lean_ctor_set(v___x_2194_, 0, v___x_2209_);
v___x_2218_ = v___x_2194_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_k_2197_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_v_2198_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v___y_2211_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
v___jp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_nat_add(v___x_2208_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec(v___x_2208_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v_l_2199_);
lean_ctor_set(v___x_2178_, 3, v_tree_2181_);
lean_ctor_set(v___x_2178_, 2, v_v_2183_);
lean_ctor_set(v___x_2178_, 1, v_k_2182_);
lean_ctor_set(v___x_2178_, 0, v___x_2223_);
v___x_2225_ = v___x_2178_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_2182_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_2183_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_tree_2181_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_l_2199_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_nat_add(v___x_2175_, v_size_2201_);
if (lean_obj_tag(v_r_2200_) == 0)
{
lean_object* v_size_2227_; 
v_size_2227_ = lean_ctor_get(v_r_2200_, 0);
lean_inc(v_size_2227_);
v___y_2211_ = v___x_2225_;
v___y_2212_ = v___x_2226_;
v___y_2213_ = v_size_2227_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_unsigned_to_nat(0u);
v___y_2211_ = v___x_2225_;
v___y_2212_ = v___x_2226_;
v___y_2213_ = v___x_2228_;
goto v___jp_2210_;
}
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2238_ = lean_nat_add(v___x_2175_, v_size_2184_);
v___x_2239_ = lean_nat_add(v___x_2238_, v_size_2170_);
lean_dec(v_size_2170_);
v___x_2240_ = lean_nat_add(v___x_2238_, v_size_2196_);
lean_dec(v___x_2238_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 4, v_l_2173_);
lean_ctor_set(v___x_2194_, 3, v_tree_2181_);
lean_ctor_set(v___x_2194_, 2, v_v_2183_);
lean_ctor_set(v___x_2194_, 1, v_k_2182_);
lean_ctor_set(v___x_2194_, 0, v___x_2240_);
v___x_2242_ = v___x_2194_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_k_2182_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_v_2183_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_tree_2181_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v_l_2173_);
v___x_2242_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
lean_object* v___x_2244_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v_r_2174_);
lean_ctor_set(v___x_2178_, 3, v___x_2242_);
lean_ctor_set(v___x_2178_, 2, v_v_2172_);
lean_ctor_set(v___x_2178_, 1, v_k_2171_);
lean_ctor_set(v___x_2178_, 0, v___x_2239_);
v___x_2244_ = v___x_2178_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_k_2171_);
lean_ctor_set(v_reuseFailAlloc_2245_, 2, v_v_2172_);
lean_ctor_set(v_reuseFailAlloc_2245_, 3, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2245_, 4, v_r_2174_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
}
else
{
lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2306_; 
lean_inc(v_r_2174_);
lean_inc(v_v_2172_);
lean_inc(v_k_2171_);
lean_inc(v_size_2170_);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; lean_object* v_unused_2308_; lean_object* v_unused_2309_; lean_object* v_unused_2310_; lean_object* v_unused_2311_; 
v_unused_2307_ = lean_ctor_get(v_r_1995_, 4);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_r_1995_, 3);
lean_dec(v_unused_2308_);
v_unused_2309_ = lean_ctor_get(v_r_1995_, 2);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_r_1995_, 1);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_r_1995_, 0);
lean_dec(v_unused_2311_);
v___x_2254_ = v_r_1995_;
v_isShared_2255_ = v_isSharedCheck_2306_;
goto v_resetjp_2253_;
}
else
{
lean_dec(v_r_1995_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2306_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
if (lean_obj_tag(v_l_2173_) == 0)
{
if (lean_obj_tag(v_r_2174_) == 0)
{
lean_object* v_k_2256_; lean_object* v_v_2257_; lean_object* v_size_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
lean_inc(v_tree_2181_);
v_k_2256_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_k_2256_);
v_v_2257_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_v_2257_);
lean_dec_ref(v___x_2180_);
v_size_2258_ = lean_ctor_get(v_l_2173_, 0);
v___x_2259_ = lean_nat_add(v___x_2175_, v_size_2170_);
lean_dec(v_size_2170_);
v___x_2260_ = lean_nat_add(v___x_2175_, v_size_2258_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 4, v_l_2173_);
lean_ctor_set(v___x_2254_, 3, v_tree_2181_);
lean_ctor_set(v___x_2254_, 2, v_v_2257_);
lean_ctor_set(v___x_2254_, 1, v_k_2256_);
lean_ctor_set(v___x_2254_, 0, v___x_2260_);
v___x_2262_ = v___x_2254_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_k_2256_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_v_2257_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_tree_2181_);
lean_ctor_set(v_reuseFailAlloc_2266_, 4, v_l_2173_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2264_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v_r_2174_);
lean_ctor_set(v___x_2178_, 3, v___x_2262_);
lean_ctor_set(v___x_2178_, 2, v_v_2172_);
lean_ctor_set(v___x_2178_, 1, v_k_2171_);
lean_ctor_set(v___x_2178_, 0, v___x_2259_);
v___x_2264_ = v___x_2178_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_k_2171_);
lean_ctor_set(v_reuseFailAlloc_2265_, 2, v_v_2172_);
lean_ctor_set(v_reuseFailAlloc_2265_, 3, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_r_2174_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
else
{
lean_object* v_k_2267_; lean_object* v_v_2268_; lean_object* v_k_2269_; lean_object* v_v_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_size_2170_);
v_k_2267_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_k_2267_);
v_v_2268_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_v_2268_);
lean_dec_ref(v___x_2180_);
v_k_2269_ = lean_ctor_get(v_l_2173_, 1);
v_v_2270_ = lean_ctor_get(v_l_2173_, 2);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_l_2173_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; lean_object* v_unused_2286_; lean_object* v_unused_2287_; 
v_unused_2285_ = lean_ctor_get(v_l_2173_, 4);
lean_dec(v_unused_2285_);
v_unused_2286_ = lean_ctor_get(v_l_2173_, 3);
lean_dec(v_unused_2286_);
v_unused_2287_ = lean_ctor_get(v_l_2173_, 0);
lean_dec(v_unused_2287_);
v___x_2272_ = v_l_2173_;
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_v_2270_);
lean_inc(v_k_2269_);
lean_dec(v_l_2173_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = lean_unsigned_to_nat(3u);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 4, v_r_2174_);
lean_ctor_set(v___x_2272_, 3, v_r_2174_);
lean_ctor_set(v___x_2272_, 2, v_v_2268_);
lean_ctor_set(v___x_2272_, 1, v_k_2267_);
lean_ctor_set(v___x_2272_, 0, v___x_2175_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_k_2267_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_v_2268_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v_r_2174_);
lean_ctor_set(v_reuseFailAlloc_2283_, 4, v_r_2174_);
v___x_2276_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 3, v_r_2174_);
lean_ctor_set(v___x_2254_, 0, v___x_2175_);
v___x_2278_ = v___x_2254_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_k_2171_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_v_2172_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_r_2174_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_r_2174_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v___x_2278_);
lean_ctor_set(v___x_2178_, 3, v___x_2276_);
lean_ctor_set(v___x_2178_, 2, v_v_2270_);
lean_ctor_set(v___x_2178_, 1, v_k_2269_);
lean_ctor_set(v___x_2178_, 0, v___x_2274_);
v___x_2280_ = v___x_2178_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_k_2269_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_v_2270_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2174_) == 0)
{
lean_object* v_k_2288_; lean_object* v_v_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
lean_dec(v_size_2170_);
v_k_2288_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_k_2288_);
v_v_2289_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_v_2289_);
lean_dec_ref(v___x_2180_);
v___x_2290_ = lean_unsigned_to_nat(3u);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 4, v_l_2173_);
lean_ctor_set(v___x_2254_, 2, v_v_2289_);
lean_ctor_set(v___x_2254_, 1, v_k_2288_);
lean_ctor_set(v___x_2254_, 0, v___x_2175_);
v___x_2292_ = v___x_2254_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_k_2288_);
lean_ctor_set(v_reuseFailAlloc_2296_, 2, v_v_2289_);
lean_ctor_set(v_reuseFailAlloc_2296_, 3, v_l_2173_);
lean_ctor_set(v_reuseFailAlloc_2296_, 4, v_l_2173_);
v___x_2292_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2294_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v_r_2174_);
lean_ctor_set(v___x_2178_, 3, v___x_2292_);
lean_ctor_set(v___x_2178_, 2, v_v_2172_);
lean_ctor_set(v___x_2178_, 1, v_k_2171_);
lean_ctor_set(v___x_2178_, 0, v___x_2290_);
v___x_2294_ = v___x_2178_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_k_2171_);
lean_ctor_set(v_reuseFailAlloc_2295_, 2, v_v_2172_);
lean_ctor_set(v_reuseFailAlloc_2295_, 3, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2295_, 4, v_r_2174_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
else
{
lean_object* v_k_2297_; lean_object* v_v_2298_; lean_object* v___x_2300_; 
v_k_2297_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_k_2297_);
v_v_2298_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_v_2298_);
lean_dec_ref(v___x_2180_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 3, v_r_2174_);
v___x_2300_ = v___x_2254_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_size_2170_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_k_2171_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_v_2172_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v_r_2174_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v_r_2174_);
v___x_2300_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2301_ = lean_unsigned_to_nat(2u);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 4, v___x_2300_);
lean_ctor_set(v___x_2178_, 3, v_r_2174_);
lean_ctor_set(v___x_2178_, 2, v_v_2298_);
lean_ctor_set(v___x_2178_, 1, v_k_2297_);
lean_ctor_set(v___x_2178_, 0, v___x_2301_);
v___x_2303_ = v___x_2178_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_k_2297_);
lean_ctor_set(v_reuseFailAlloc_2304_, 2, v_v_2298_);
lean_ctor_set(v_reuseFailAlloc_2304_, 3, v_r_2174_);
lean_ctor_set(v_reuseFailAlloc_2304_, 4, v___x_2300_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
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
lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2470_; 
lean_inc(v_r_2174_);
lean_inc(v_v_2172_);
lean_inc(v_k_2171_);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; lean_object* v_unused_2472_; lean_object* v_unused_2473_; lean_object* v_unused_2474_; lean_object* v_unused_2475_; 
v_unused_2471_ = lean_ctor_get(v_r_1995_, 4);
lean_dec(v_unused_2471_);
v_unused_2472_ = lean_ctor_get(v_r_1995_, 3);
lean_dec(v_unused_2472_);
v_unused_2473_ = lean_ctor_get(v_r_1995_, 2);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_r_1995_, 1);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v_r_1995_, 0);
lean_dec(v_unused_2475_);
v___x_2319_ = v_r_1995_;
v_isShared_2320_ = v_isSharedCheck_2470_;
goto v_resetjp_2318_;
}
else
{
lean_dec(v_r_1995_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2470_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v_tree_2322_; 
v___x_2321_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2171_, v_v_2172_, v_l_2173_, v_r_2174_);
v_tree_2322_ = lean_ctor_get(v___x_2321_, 2);
lean_inc(v_tree_2322_);
if (lean_obj_tag(v_tree_2322_) == 0)
{
lean_object* v_k_2323_; lean_object* v_v_2324_; lean_object* v_size_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; 
v_k_2323_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_k_2323_);
v_v_2324_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_v_2324_);
lean_dec_ref(v___x_2321_);
v_size_2325_ = lean_ctor_get(v_tree_2322_, 0);
v___x_2326_ = lean_unsigned_to_nat(3u);
v___x_2327_ = lean_nat_mul(v___x_2326_, v_size_2325_);
v___x_2328_ = lean_nat_dec_lt(v___x_2327_, v_size_2165_);
lean_dec(v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2332_; 
lean_dec(v_r_2169_);
v___x_2329_ = lean_nat_add(v___x_2175_, v_size_2165_);
v___x_2330_ = lean_nat_add(v___x_2329_, v_size_2325_);
lean_dec(v___x_2329_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v_tree_2322_);
lean_ctor_set(v___x_2319_, 3, v_l_1994_);
lean_ctor_set(v___x_2319_, 2, v_v_2324_);
lean_ctor_set(v___x_2319_, 1, v_k_2323_);
lean_ctor_set(v___x_2319_, 0, v___x_2330_);
v___x_2332_ = v___x_2319_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_k_2323_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_v_2324_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_l_1994_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_tree_2322_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
else
{
lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2399_; 
lean_inc(v_l_2168_);
lean_inc(v_v_2167_);
lean_inc(v_k_2166_);
lean_inc(v_size_2165_);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; lean_object* v_unused_2401_; lean_object* v_unused_2402_; lean_object* v_unused_2403_; lean_object* v_unused_2404_; 
v_unused_2400_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_l_1994_, 2);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_l_1994_, 1);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_l_1994_, 0);
lean_dec(v_unused_2404_);
v___x_2335_ = v_l_1994_;
v_isShared_2336_ = v_isSharedCheck_2399_;
goto v_resetjp_2334_;
}
else
{
lean_dec(v_l_1994_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2399_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v_size_2337_; lean_object* v_size_2338_; lean_object* v_k_2339_; lean_object* v_v_2340_; lean_object* v_l_2341_; lean_object* v_r_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_size_2337_ = lean_ctor_get(v_l_2168_, 0);
v_size_2338_ = lean_ctor_get(v_r_2169_, 0);
v_k_2339_ = lean_ctor_get(v_r_2169_, 1);
v_v_2340_ = lean_ctor_get(v_r_2169_, 2);
v_l_2341_ = lean_ctor_get(v_r_2169_, 3);
v_r_2342_ = lean_ctor_get(v_r_2169_, 4);
v___x_2343_ = lean_unsigned_to_nat(2u);
v___x_2344_ = lean_nat_mul(v___x_2343_, v_size_2337_);
v___x_2345_ = lean_nat_dec_lt(v_size_2338_, v___x_2344_);
lean_dec(v___x_2344_);
if (v___x_2345_ == 0)
{
lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2383_; 
lean_inc(v_r_2342_);
lean_inc(v_l_2341_);
lean_inc(v_v_2340_);
lean_inc(v_k_2339_);
lean_del_object(v___x_2335_);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_r_2169_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; lean_object* v_unused_2385_; lean_object* v_unused_2386_; lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2384_ = lean_ctor_get(v_r_2169_, 4);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_r_2169_, 3);
lean_dec(v_unused_2385_);
v_unused_2386_ = lean_ctor_get(v_r_2169_, 2);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_r_2169_, 1);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_r_2169_, 0);
lean_dec(v_unused_2388_);
v___x_2347_ = v_r_2169_;
v_isShared_2348_ = v_isSharedCheck_2383_;
goto v_resetjp_2346_;
}
else
{
lean_dec(v_r_2169_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2383_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___x_2371_; lean_object* v___y_2373_; 
v___x_2349_ = lean_nat_add(v___x_2175_, v_size_2165_);
lean_dec(v_size_2165_);
v___x_2350_ = lean_nat_add(v___x_2349_, v_size_2325_);
lean_dec(v___x_2349_);
v___x_2371_ = lean_nat_add(v___x_2175_, v_size_2337_);
if (lean_obj_tag(v_l_2341_) == 0)
{
lean_object* v_size_2381_; 
v_size_2381_ = lean_ctor_get(v_l_2341_, 0);
lean_inc(v_size_2381_);
v___y_2373_ = v_size_2381_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_unsigned_to_nat(0u);
v___y_2373_ = v___x_2382_;
goto v___jp_2372_;
}
v___jp_2351_:
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2355_ = lean_nat_add(v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
lean_inc_ref(v_tree_2322_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 4, v_tree_2322_);
lean_ctor_set(v___x_2347_, 3, v_r_2342_);
lean_ctor_set(v___x_2347_, 2, v_v_2324_);
lean_ctor_set(v___x_2347_, 1, v_k_2323_);
lean_ctor_set(v___x_2347_, 0, v___x_2355_);
v___x_2357_ = v___x_2347_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_k_2323_);
lean_ctor_set(v_reuseFailAlloc_2370_, 2, v_v_2324_);
lean_ctor_set(v_reuseFailAlloc_2370_, 3, v_r_2342_);
lean_ctor_set(v_reuseFailAlloc_2370_, 4, v_tree_2322_);
v___x_2357_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
v_isSharedCheck_2364_ = !lean_is_exclusive(v_tree_2322_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; lean_object* v_unused_2366_; lean_object* v_unused_2367_; lean_object* v_unused_2368_; lean_object* v_unused_2369_; 
v_unused_2365_ = lean_ctor_get(v_tree_2322_, 4);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_tree_2322_, 3);
lean_dec(v_unused_2366_);
v_unused_2367_ = lean_ctor_get(v_tree_2322_, 2);
lean_dec(v_unused_2367_);
v_unused_2368_ = lean_ctor_get(v_tree_2322_, 1);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_tree_2322_, 0);
lean_dec(v_unused_2369_);
v___x_2359_ = v_tree_2322_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_dec(v_tree_2322_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 4, v___x_2357_);
lean_ctor_set(v___x_2359_, 3, v___y_2352_);
lean_ctor_set(v___x_2359_, 2, v_v_2340_);
lean_ctor_set(v___x_2359_, 1, v_k_2339_);
lean_ctor_set(v___x_2359_, 0, v___x_2350_);
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_k_2339_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_v_2340_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v___y_2352_);
lean_ctor_set(v_reuseFailAlloc_2363_, 4, v___x_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
v___jp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = lean_nat_add(v___x_2371_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec(v___x_2371_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v_l_2341_);
lean_ctor_set(v___x_2319_, 3, v_l_2168_);
lean_ctor_set(v___x_2319_, 2, v_v_2167_);
lean_ctor_set(v___x_2319_, 1, v_k_2166_);
lean_ctor_set(v___x_2319_, 0, v___x_2374_);
v___x_2376_ = v___x_2319_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_k_2166_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_v_2167_);
lean_ctor_set(v_reuseFailAlloc_2380_, 3, v_l_2168_);
lean_ctor_set(v_reuseFailAlloc_2380_, 4, v_l_2341_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_nat_add(v___x_2175_, v_size_2325_);
if (lean_obj_tag(v_r_2342_) == 0)
{
lean_object* v_size_2378_; 
v_size_2378_ = lean_ctor_get(v_r_2342_, 0);
lean_inc(v_size_2378_);
v___y_2352_ = v___x_2376_;
v___y_2353_ = v___x_2377_;
v___y_2354_ = v_size_2378_;
goto v___jp_2351_;
}
else
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_unsigned_to_nat(0u);
v___y_2352_ = v___x_2376_;
v___y_2353_ = v___x_2377_;
v___y_2354_ = v___x_2379_;
goto v___jp_2351_;
}
}
}
}
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2389_ = lean_nat_add(v___x_2175_, v_size_2165_);
lean_dec(v_size_2165_);
v___x_2390_ = lean_nat_add(v___x_2389_, v_size_2325_);
lean_dec(v___x_2389_);
v___x_2391_ = lean_nat_add(v___x_2175_, v_size_2325_);
v___x_2392_ = lean_nat_add(v___x_2391_, v_size_2338_);
lean_dec(v___x_2391_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v_tree_2322_);
lean_ctor_set(v___x_2319_, 3, v_r_2169_);
lean_ctor_set(v___x_2319_, 2, v_v_2324_);
lean_ctor_set(v___x_2319_, 1, v_k_2323_);
lean_ctor_set(v___x_2319_, 0, v___x_2392_);
v___x_2394_ = v___x_2319_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_k_2323_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_v_2324_);
lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_r_2169_);
lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_tree_2322_);
v___x_2394_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2396_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 4, v___x_2394_);
lean_ctor_set(v___x_2335_, 0, v___x_2390_);
v___x_2396_ = v___x_2335_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_k_2166_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_v_2167_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_l_2168_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2168_) == 0)
{
lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2428_; 
lean_inc_ref(v_l_2168_);
lean_inc(v_v_2167_);
lean_inc(v_k_2166_);
lean_inc(v_size_2165_);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; lean_object* v_unused_2430_; lean_object* v_unused_2431_; lean_object* v_unused_2432_; lean_object* v_unused_2433_; 
v_unused_2429_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_l_1994_, 2);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_l_1994_, 1);
lean_dec(v_unused_2432_);
v_unused_2433_ = lean_ctor_get(v_l_1994_, 0);
lean_dec(v_unused_2433_);
v___x_2406_ = v_l_1994_;
v_isShared_2407_ = v_isSharedCheck_2428_;
goto v_resetjp_2405_;
}
else
{
lean_dec(v_l_1994_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2428_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
if (lean_obj_tag(v_r_2169_) == 0)
{
lean_object* v_k_2408_; lean_object* v_v_2409_; lean_object* v_size_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v_k_2408_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_k_2408_);
v_v_2409_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_v_2409_);
lean_dec_ref(v___x_2321_);
v_size_2410_ = lean_ctor_get(v_r_2169_, 0);
v___x_2411_ = lean_nat_add(v___x_2175_, v_size_2165_);
lean_dec(v_size_2165_);
v___x_2412_ = lean_nat_add(v___x_2175_, v_size_2410_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v_tree_2322_);
lean_ctor_set(v___x_2319_, 3, v_r_2169_);
lean_ctor_set(v___x_2319_, 2, v_v_2409_);
lean_ctor_set(v___x_2319_, 1, v_k_2408_);
lean_ctor_set(v___x_2319_, 0, v___x_2412_);
v___x_2414_ = v___x_2319_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_k_2408_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_v_2409_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_r_2169_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_tree_2322_);
v___x_2414_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v___x_2414_);
lean_ctor_set(v___x_2406_, 0, v___x_2411_);
v___x_2416_ = v___x_2406_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_k_2166_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_v_2167_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_l_2168_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
else
{
lean_object* v_k_2419_; lean_object* v_v_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_dec(v_size_2165_);
v_k_2419_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_k_2419_);
v_v_2420_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_v_2420_);
lean_dec_ref(v___x_2321_);
v___x_2421_ = lean_unsigned_to_nat(3u);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v_r_2169_);
lean_ctor_set(v___x_2319_, 3, v_r_2169_);
lean_ctor_set(v___x_2319_, 2, v_v_2420_);
lean_ctor_set(v___x_2319_, 1, v_k_2419_);
lean_ctor_set(v___x_2319_, 0, v___x_2175_);
v___x_2423_ = v___x_2319_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_k_2419_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_v_2420_);
lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_r_2169_);
lean_ctor_set(v_reuseFailAlloc_2427_, 4, v_r_2169_);
v___x_2423_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2425_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v___x_2423_);
lean_ctor_set(v___x_2406_, 0, v___x_2421_);
v___x_2425_ = v___x_2406_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_k_2166_);
lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_v_2167_);
lean_ctor_set(v_reuseFailAlloc_2426_, 3, v_l_2168_);
lean_ctor_set(v_reuseFailAlloc_2426_, 4, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2169_) == 0)
{
lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2458_; 
lean_inc(v_l_2168_);
lean_inc(v_v_2167_);
lean_inc(v_k_2166_);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_l_1994_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; lean_object* v_unused_2460_; lean_object* v_unused_2461_; lean_object* v_unused_2462_; lean_object* v_unused_2463_; 
v_unused_2459_ = lean_ctor_get(v_l_1994_, 4);
lean_dec(v_unused_2459_);
v_unused_2460_ = lean_ctor_get(v_l_1994_, 3);
lean_dec(v_unused_2460_);
v_unused_2461_ = lean_ctor_get(v_l_1994_, 2);
lean_dec(v_unused_2461_);
v_unused_2462_ = lean_ctor_get(v_l_1994_, 1);
lean_dec(v_unused_2462_);
v_unused_2463_ = lean_ctor_get(v_l_1994_, 0);
lean_dec(v_unused_2463_);
v___x_2435_ = v_l_1994_;
v_isShared_2436_ = v_isSharedCheck_2458_;
goto v_resetjp_2434_;
}
else
{
lean_dec(v_l_1994_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2458_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v_k_2437_; lean_object* v_v_2438_; lean_object* v_k_2439_; lean_object* v_v_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2454_; 
v_k_2437_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_k_2437_);
v_v_2438_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_v_2438_);
lean_dec_ref(v___x_2321_);
v_k_2439_ = lean_ctor_get(v_r_2169_, 1);
v_v_2440_ = lean_ctor_get(v_r_2169_, 2);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_r_2169_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; lean_object* v_unused_2456_; lean_object* v_unused_2457_; 
v_unused_2455_ = lean_ctor_get(v_r_2169_, 4);
lean_dec(v_unused_2455_);
v_unused_2456_ = lean_ctor_get(v_r_2169_, 3);
lean_dec(v_unused_2456_);
v_unused_2457_ = lean_ctor_get(v_r_2169_, 0);
lean_dec(v_unused_2457_);
v___x_2442_ = v_r_2169_;
v_isShared_2443_ = v_isSharedCheck_2454_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_v_2440_);
lean_inc(v_k_2439_);
lean_dec(v_r_2169_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2454_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = lean_unsigned_to_nat(3u);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 4, v_l_2168_);
lean_ctor_set(v___x_2442_, 3, v_l_2168_);
lean_ctor_set(v___x_2442_, 2, v_v_2167_);
lean_ctor_set(v___x_2442_, 1, v_k_2166_);
lean_ctor_set(v___x_2442_, 0, v___x_2175_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_k_2166_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v_v_2167_);
lean_ctor_set(v_reuseFailAlloc_2453_, 3, v_l_2168_);
lean_ctor_set(v_reuseFailAlloc_2453_, 4, v_l_2168_);
v___x_2446_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2448_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v_l_2168_);
lean_ctor_set(v___x_2319_, 3, v_l_2168_);
lean_ctor_set(v___x_2319_, 2, v_v_2438_);
lean_ctor_set(v___x_2319_, 1, v_k_2437_);
lean_ctor_set(v___x_2319_, 0, v___x_2175_);
v___x_2448_ = v___x_2319_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_k_2437_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_v_2438_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_l_2168_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_l_2168_);
v___x_2448_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2450_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 4, v___x_2448_);
lean_ctor_set(v___x_2435_, 3, v___x_2446_);
lean_ctor_set(v___x_2435_, 2, v_v_2440_);
lean_ctor_set(v___x_2435_, 1, v_k_2439_);
lean_ctor_set(v___x_2435_, 0, v___x_2444_);
v___x_2450_ = v___x_2435_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_k_2439_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_v_2440_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
}
else
{
lean_object* v_k_2464_; lean_object* v_v_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v_k_2464_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_k_2464_);
v_v_2465_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_v_2465_);
lean_dec_ref(v___x_2321_);
v___x_2466_ = lean_unsigned_to_nat(2u);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 4, v_r_2169_);
lean_ctor_set(v___x_2319_, 3, v_l_1994_);
lean_ctor_set(v___x_2319_, 2, v_v_2465_);
lean_ctor_set(v___x_2319_, 1, v_k_2464_);
lean_ctor_set(v___x_2319_, 0, v___x_2466_);
v___x_2468_ = v___x_2319_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_k_2464_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_v_2465_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_l_1994_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v_r_2169_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
}
}
else
{
return v_l_1994_;
}
}
else
{
return v_r_1995_;
}
}
}
else
{
lean_object* v_impl_2476_; lean_object* v___x_2477_; 
v_impl_2476_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_1990_, v_l_1994_);
v___x_2477_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2476_) == 0)
{
if (lean_obj_tag(v_r_1995_) == 0)
{
lean_object* v_size_2478_; lean_object* v_size_2479_; lean_object* v_k_2480_; lean_object* v_v_2481_; lean_object* v_l_2482_; lean_object* v_r_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v_size_2478_ = lean_ctor_get(v_impl_2476_, 0);
v_size_2479_ = lean_ctor_get(v_r_1995_, 0);
v_k_2480_ = lean_ctor_get(v_r_1995_, 1);
v_v_2481_ = lean_ctor_get(v_r_1995_, 2);
v_l_2482_ = lean_ctor_get(v_r_1995_, 3);
lean_inc(v_l_2482_);
v_r_2483_ = lean_ctor_get(v_r_1995_, 4);
v___x_2484_ = lean_unsigned_to_nat(3u);
v___x_2485_ = lean_nat_mul(v___x_2484_, v_size_2478_);
v___x_2486_ = lean_nat_dec_lt(v___x_2485_, v_size_2479_);
lean_dec(v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2490_; 
lean_dec(v_l_2482_);
v___x_2487_ = lean_nat_add(v___x_2477_, v_size_2478_);
v___x_2488_ = lean_nat_add(v___x_2487_, v_size_2479_);
lean_dec(v___x_2487_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 3, v_impl_2476_);
lean_ctor_set(v___x_1997_, 0, v___x_2488_);
v___x_2490_ = v___x_1997_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_impl_2476_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_r_1995_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
else
{
lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2555_; 
lean_inc(v_r_2483_);
lean_inc(v_v_2481_);
lean_inc(v_k_2480_);
lean_inc(v_size_2479_);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; lean_object* v_unused_2557_; lean_object* v_unused_2558_; lean_object* v_unused_2559_; lean_object* v_unused_2560_; 
v_unused_2556_ = lean_ctor_get(v_r_1995_, 4);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_r_1995_, 3);
lean_dec(v_unused_2557_);
v_unused_2558_ = lean_ctor_get(v_r_1995_, 2);
lean_dec(v_unused_2558_);
v_unused_2559_ = lean_ctor_get(v_r_1995_, 1);
lean_dec(v_unused_2559_);
v_unused_2560_ = lean_ctor_get(v_r_1995_, 0);
lean_dec(v_unused_2560_);
v___x_2493_ = v_r_1995_;
v_isShared_2494_ = v_isSharedCheck_2555_;
goto v_resetjp_2492_;
}
else
{
lean_dec(v_r_1995_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2555_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v_size_2495_; lean_object* v_k_2496_; lean_object* v_v_2497_; lean_object* v_l_2498_; lean_object* v_r_2499_; lean_object* v_size_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_size_2495_ = lean_ctor_get(v_l_2482_, 0);
v_k_2496_ = lean_ctor_get(v_l_2482_, 1);
v_v_2497_ = lean_ctor_get(v_l_2482_, 2);
v_l_2498_ = lean_ctor_get(v_l_2482_, 3);
v_r_2499_ = lean_ctor_get(v_l_2482_, 4);
v_size_2500_ = lean_ctor_get(v_r_2483_, 0);
v___x_2501_ = lean_unsigned_to_nat(2u);
v___x_2502_ = lean_nat_mul(v___x_2501_, v_size_2500_);
v___x_2503_ = lean_nat_dec_lt(v_size_2495_, v___x_2502_);
lean_dec(v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2531_; 
lean_inc(v_r_2499_);
lean_inc(v_l_2498_);
lean_inc(v_v_2497_);
lean_inc(v_k_2496_);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_l_2482_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; 
v_unused_2532_ = lean_ctor_get(v_l_2482_, 4);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v_l_2482_, 3);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_l_2482_, 2);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_l_2482_, 1);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_l_2482_, 0);
lean_dec(v_unused_2536_);
v___x_2505_ = v_l_2482_;
v_isShared_2506_ = v_isSharedCheck_2531_;
goto v_resetjp_2504_;
}
else
{
lean_dec(v_l_2482_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2531_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2521_; 
v___x_2507_ = lean_nat_add(v___x_2477_, v_size_2478_);
v___x_2508_ = lean_nat_add(v___x_2507_, v_size_2479_);
lean_dec(v_size_2479_);
if (lean_obj_tag(v_l_2498_) == 0)
{
lean_object* v_size_2529_; 
v_size_2529_ = lean_ctor_get(v_l_2498_, 0);
lean_inc(v_size_2529_);
v___y_2521_ = v_size_2529_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_unsigned_to_nat(0u);
v___y_2521_ = v___x_2530_;
goto v___jp_2520_;
}
v___jp_2509_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2513_ = lean_nat_add(v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec(v___y_2511_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 4, v_r_2483_);
lean_ctor_set(v___x_2505_, 3, v_r_2499_);
lean_ctor_set(v___x_2505_, 2, v_v_2481_);
lean_ctor_set(v___x_2505_, 1, v_k_2480_);
lean_ctor_set(v___x_2505_, 0, v___x_2513_);
v___x_2515_ = v___x_2505_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_k_2480_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_v_2481_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_r_2499_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_r_2483_);
v___x_2515_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2517_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 4, v___x_2515_);
lean_ctor_set(v___x_2493_, 3, v___y_2510_);
lean_ctor_set(v___x_2493_, 2, v_v_2497_);
lean_ctor_set(v___x_2493_, 1, v_k_2496_);
lean_ctor_set(v___x_2493_, 0, v___x_2508_);
v___x_2517_ = v___x_2493_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_k_2496_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_v_2497_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v___y_2510_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
v___jp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_nat_add(v___x_2507_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec(v___x_2507_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_l_2498_);
lean_ctor_set(v___x_1997_, 3, v_impl_2476_);
lean_ctor_set(v___x_1997_, 0, v___x_2522_);
v___x_2524_ = v___x_1997_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2522_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_impl_2476_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_l_2498_);
v___x_2524_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_nat_add(v___x_2477_, v_size_2500_);
if (lean_obj_tag(v_r_2499_) == 0)
{
lean_object* v_size_2526_; 
v_size_2526_ = lean_ctor_get(v_r_2499_, 0);
lean_inc(v_size_2526_);
v___y_2510_ = v___x_2524_;
v___y_2511_ = v___x_2525_;
v___y_2512_ = v_size_2526_;
goto v___jp_2509_;
}
else
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_unsigned_to_nat(0u);
v___y_2510_ = v___x_2524_;
v___y_2511_ = v___x_2525_;
v___y_2512_ = v___x_2527_;
goto v___jp_2509_;
}
}
}
}
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_del_object(v___x_1997_);
v___x_2537_ = lean_nat_add(v___x_2477_, v_size_2478_);
v___x_2538_ = lean_nat_add(v___x_2537_, v_size_2479_);
lean_dec(v_size_2479_);
v___x_2539_ = lean_nat_add(v___x_2537_, v_size_2495_);
lean_dec(v___x_2537_);
lean_inc_ref(v_impl_2476_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 4, v_l_2482_);
lean_ctor_set(v___x_2493_, 3, v_impl_2476_);
lean_ctor_set(v___x_2493_, 2, v_v_1993_);
lean_ctor_set(v___x_2493_, 1, v_k_1992_);
lean_ctor_set(v___x_2493_, 0, v___x_2539_);
v___x_2541_ = v___x_2493_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_impl_2476_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_l_2482_);
v___x_2541_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
v_isSharedCheck_2548_ = !lean_is_exclusive(v_impl_2476_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; lean_object* v_unused_2550_; lean_object* v_unused_2551_; lean_object* v_unused_2552_; lean_object* v_unused_2553_; 
v_unused_2549_ = lean_ctor_get(v_impl_2476_, 4);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v_impl_2476_, 3);
lean_dec(v_unused_2550_);
v_unused_2551_ = lean_ctor_get(v_impl_2476_, 2);
lean_dec(v_unused_2551_);
v_unused_2552_ = lean_ctor_get(v_impl_2476_, 1);
lean_dec(v_unused_2552_);
v_unused_2553_ = lean_ctor_get(v_impl_2476_, 0);
lean_dec(v_unused_2553_);
v___x_2543_ = v_impl_2476_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_dec(v_impl_2476_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 4, v_r_2483_);
lean_ctor_set(v___x_2543_, 3, v___x_2541_);
lean_ctor_set(v___x_2543_, 2, v_v_2481_);
lean_ctor_set(v___x_2543_, 1, v_k_2480_);
lean_ctor_set(v___x_2543_, 0, v___x_2538_);
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_k_2480_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_v_2481_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v_r_2483_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
v_size_2561_ = lean_ctor_get(v_impl_2476_, 0);
v___x_2562_ = lean_nat_add(v___x_2477_, v_size_2561_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 3, v_impl_2476_);
lean_ctor_set(v___x_1997_, 0, v___x_2562_);
v___x_2564_ = v___x_1997_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_impl_2476_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v_r_1995_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
if (lean_obj_tag(v_r_1995_) == 0)
{
lean_object* v_l_2566_; 
v_l_2566_ = lean_ctor_get(v_r_1995_, 3);
lean_inc(v_l_2566_);
if (lean_obj_tag(v_l_2566_) == 0)
{
lean_object* v_r_2567_; 
v_r_2567_ = lean_ctor_get(v_r_1995_, 4);
lean_inc(v_r_2567_);
if (lean_obj_tag(v_r_2567_) == 0)
{
lean_object* v_size_2568_; lean_object* v_k_2569_; lean_object* v_v_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2583_; 
v_size_2568_ = lean_ctor_get(v_r_1995_, 0);
v_k_2569_ = lean_ctor_get(v_r_1995_, 1);
v_v_2570_ = lean_ctor_get(v_r_1995_, 2);
v_isSharedCheck_2583_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; 
v_unused_2584_ = lean_ctor_get(v_r_1995_, 4);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_r_1995_, 3);
lean_dec(v_unused_2585_);
v___x_2572_ = v_r_1995_;
v_isShared_2573_ = v_isSharedCheck_2583_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_v_2570_);
lean_inc(v_k_2569_);
lean_inc(v_size_2568_);
lean_dec(v_r_1995_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2583_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_size_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v_size_2574_ = lean_ctor_get(v_l_2566_, 0);
v___x_2575_ = lean_nat_add(v___x_2477_, v_size_2568_);
lean_dec(v_size_2568_);
v___x_2576_ = lean_nat_add(v___x_2477_, v_size_2574_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 4, v_l_2566_);
lean_ctor_set(v___x_2572_, 3, v_impl_2476_);
lean_ctor_set(v___x_2572_, 2, v_v_1993_);
lean_ctor_set(v___x_2572_, 1, v_k_1992_);
lean_ctor_set(v___x_2572_, 0, v___x_2576_);
v___x_2578_ = v___x_2572_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2576_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_impl_2476_);
lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_l_2566_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_r_2567_);
lean_ctor_set(v___x_1997_, 3, v___x_2578_);
lean_ctor_set(v___x_1997_, 2, v_v_2570_);
lean_ctor_set(v___x_1997_, 1, v_k_2569_);
lean_ctor_set(v___x_1997_, 0, v___x_2575_);
v___x_2580_ = v___x_1997_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_k_2569_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_v_2570_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_r_2567_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v_k_2586_; lean_object* v_v_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2610_; 
v_k_2586_ = lean_ctor_get(v_r_1995_, 1);
v_v_2587_ = lean_ctor_get(v_r_1995_, 2);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; lean_object* v_unused_2612_; lean_object* v_unused_2613_; 
v_unused_2611_ = lean_ctor_get(v_r_1995_, 4);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v_r_1995_, 3);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v_r_1995_, 0);
lean_dec(v_unused_2613_);
v___x_2589_ = v_r_1995_;
v_isShared_2590_ = v_isSharedCheck_2610_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_v_2587_);
lean_inc(v_k_2586_);
lean_dec(v_r_1995_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2610_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_k_2591_; lean_object* v_v_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2606_; 
v_k_2591_ = lean_ctor_get(v_l_2566_, 1);
v_v_2592_ = lean_ctor_get(v_l_2566_, 2);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_l_2566_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; lean_object* v_unused_2608_; lean_object* v_unused_2609_; 
v_unused_2607_ = lean_ctor_get(v_l_2566_, 4);
lean_dec(v_unused_2607_);
v_unused_2608_ = lean_ctor_get(v_l_2566_, 3);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_l_2566_, 0);
lean_dec(v_unused_2609_);
v___x_2594_ = v_l_2566_;
v_isShared_2595_ = v_isSharedCheck_2606_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_v_2592_);
lean_inc(v_k_2591_);
lean_dec(v_l_2566_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2606_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = lean_unsigned_to_nat(3u);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 4, v_r_2567_);
lean_ctor_set(v___x_2594_, 3, v_r_2567_);
lean_ctor_set(v___x_2594_, 2, v_v_1993_);
lean_ctor_set(v___x_2594_, 1, v_k_1992_);
lean_ctor_set(v___x_2594_, 0, v___x_2477_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2605_, 3, v_r_2567_);
lean_ctor_set(v_reuseFailAlloc_2605_, 4, v_r_2567_);
v___x_2598_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2600_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 3, v_r_2567_);
lean_ctor_set(v___x_2589_, 0, v___x_2477_);
v___x_2600_ = v___x_2589_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_k_2586_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_v_2587_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_r_2567_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_r_2567_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v___x_2600_);
lean_ctor_set(v___x_1997_, 3, v___x_2598_);
lean_ctor_set(v___x_1997_, 2, v_v_2592_);
lean_ctor_set(v___x_1997_, 1, v_k_2591_);
lean_ctor_set(v___x_1997_, 0, v___x_2596_);
v___x_2602_ = v___x_1997_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_k_2591_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_v_2592_);
lean_ctor_set(v_reuseFailAlloc_2603_, 3, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2603_, 4, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2614_; 
v_r_2614_ = lean_ctor_get(v_r_1995_, 4);
lean_inc(v_r_2614_);
if (lean_obj_tag(v_r_2614_) == 0)
{
lean_object* v_k_2615_; lean_object* v_v_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2627_; 
v_k_2615_ = lean_ctor_get(v_r_1995_, 1);
v_v_2616_ = lean_ctor_get(v_r_1995_, 2);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; lean_object* v_unused_2629_; lean_object* v_unused_2630_; 
v_unused_2628_ = lean_ctor_get(v_r_1995_, 4);
lean_dec(v_unused_2628_);
v_unused_2629_ = lean_ctor_get(v_r_1995_, 3);
lean_dec(v_unused_2629_);
v_unused_2630_ = lean_ctor_get(v_r_1995_, 0);
lean_dec(v_unused_2630_);
v___x_2618_ = v_r_1995_;
v_isShared_2619_ = v_isSharedCheck_2627_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_v_2616_);
lean_inc(v_k_2615_);
lean_dec(v_r_1995_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2627_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = lean_unsigned_to_nat(3u);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 4, v_l_2566_);
lean_ctor_set(v___x_2618_, 2, v_v_1993_);
lean_ctor_set(v___x_2618_, 1, v_k_1992_);
lean_ctor_set(v___x_2618_, 0, v___x_2477_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2626_, 3, v_l_2566_);
lean_ctor_set(v_reuseFailAlloc_2626_, 4, v_l_2566_);
v___x_2622_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v_r_2614_);
lean_ctor_set(v___x_1997_, 3, v___x_2622_);
lean_ctor_set(v___x_1997_, 2, v_v_2616_);
lean_ctor_set(v___x_1997_, 1, v_k_2615_);
lean_ctor_set(v___x_1997_, 0, v___x_2620_);
v___x_2624_ = v___x_1997_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_k_2615_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_v_2616_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_r_2614_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_size_2631_; lean_object* v_k_2632_; lean_object* v_v_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2644_; 
v_size_2631_ = lean_ctor_get(v_r_1995_, 0);
v_k_2632_ = lean_ctor_get(v_r_1995_, 1);
v_v_2633_ = lean_ctor_get(v_r_1995_, 2);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_r_1995_);
if (v_isSharedCheck_2644_ == 0)
{
lean_object* v_unused_2645_; lean_object* v_unused_2646_; 
v_unused_2645_ = lean_ctor_get(v_r_1995_, 4);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_r_1995_, 3);
lean_dec(v_unused_2646_);
v___x_2635_ = v_r_1995_;
v_isShared_2636_ = v_isSharedCheck_2644_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_v_2633_);
lean_inc(v_k_2632_);
lean_inc(v_size_2631_);
lean_dec(v_r_1995_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2644_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 3, v_r_2614_);
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_size_2631_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_k_2632_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_v_2633_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v_r_2614_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_r_2614_);
v___x_2638_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = lean_unsigned_to_nat(2u);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 4, v___x_2638_);
lean_ctor_set(v___x_1997_, 3, v_r_2614_);
lean_ctor_set(v___x_1997_, 0, v___x_2639_);
v___x_2641_ = v___x_1997_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2642_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2642_, 3, v_r_2614_);
lean_ctor_set(v_reuseFailAlloc_2642_, 4, v___x_2638_);
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
}
else
{
lean_object* v___x_2648_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 3, v_r_1995_);
lean_ctor_set(v___x_1997_, 0, v___x_2477_);
v___x_2648_ = v___x_1997_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_k_1992_);
lean_ctor_set(v_reuseFailAlloc_2649_, 2, v_v_1993_);
lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_r_1995_);
lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_r_1995_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
else
{
return v_t_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2652_, lean_object* v_t_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2652_, v_t_2653_);
lean_dec(v_k_2652_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object* v_id_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; lean_object* v_receivers_2664_; lean_object* v___x_2665_; 
v___x_2663_ = lean_st_ref_get(v___y_2661_);
v_receivers_2664_ = lean_ctor_get(v___x_2663_, 7);
v___x_2665_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2664_, v_id_2660_);
if (lean_obj_tag(v___x_2665_) == 1)
{
lean_object* v_val_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v_val_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_val_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2663_);
lean_ctor_set(v___x_2667_, 1, v_val_2666_);
v___x_2668_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2667_, v___y_2661_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2698_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2698_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2698_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_fst_2673_; lean_object* v_producers_2674_; lean_object* v_waiters_2675_; lean_object* v_capacity_2676_; lean_object* v_size_2677_; lean_object* v_buffer_2678_; lean_object* v_write_2679_; lean_object* v_read_2680_; lean_object* v_receivers_2681_; lean_object* v_nextId_2682_; uint8_t v_closed_2683_; lean_object* v_pos_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2697_; 
v_fst_2673_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_fst_2673_);
lean_dec(v_a_2669_);
v_producers_2674_ = lean_ctor_get(v_fst_2673_, 0);
v_waiters_2675_ = lean_ctor_get(v_fst_2673_, 1);
v_capacity_2676_ = lean_ctor_get(v_fst_2673_, 2);
v_size_2677_ = lean_ctor_get(v_fst_2673_, 3);
v_buffer_2678_ = lean_ctor_get(v_fst_2673_, 4);
v_write_2679_ = lean_ctor_get(v_fst_2673_, 5);
v_read_2680_ = lean_ctor_get(v_fst_2673_, 6);
v_receivers_2681_ = lean_ctor_get(v_fst_2673_, 7);
v_nextId_2682_ = lean_ctor_get(v_fst_2673_, 8);
v_closed_2683_ = lean_ctor_get_uint8(v_fst_2673_, sizeof(void*)*10);
v_pos_2684_ = lean_ctor_get(v_fst_2673_, 9);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_fst_2673_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2686_ = v_fst_2673_;
v_isShared_2687_ = v_isSharedCheck_2697_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_pos_2684_);
lean_inc(v_nextId_2682_);
lean_inc(v_receivers_2681_);
lean_inc(v_read_2680_);
lean_inc(v_write_2679_);
lean_inc(v_buffer_2678_);
lean_inc(v_size_2677_);
lean_inc(v_capacity_2676_);
lean_inc(v_waiters_2675_);
lean_inc(v_producers_2674_);
lean_dec(v_fst_2673_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2697_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_id_2660_, v_receivers_2681_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 7, v___x_2688_);
v___x_2690_ = v___x_2686_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_producers_2674_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_waiters_2675_);
lean_ctor_set(v_reuseFailAlloc_2696_, 2, v_capacity_2676_);
lean_ctor_set(v_reuseFailAlloc_2696_, 3, v_size_2677_);
lean_ctor_set(v_reuseFailAlloc_2696_, 4, v_buffer_2678_);
lean_ctor_set(v_reuseFailAlloc_2696_, 5, v_write_2679_);
lean_ctor_set(v_reuseFailAlloc_2696_, 6, v_read_2680_);
lean_ctor_set(v_reuseFailAlloc_2696_, 7, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2696_, 8, v_nextId_2682_);
lean_ctor_set(v_reuseFailAlloc_2696_, 9, v_pos_2684_);
lean_ctor_set_uint8(v_reuseFailAlloc_2696_, sizeof(void*)*10, v_closed_2683_);
v___x_2690_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2691_ = lean_st_ref_swap(v___y_2661_, v___x_2690_);
lean_dec(v___x_2691_);
v___x_2692_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0));
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2692_);
v___x_2694_ = v___x_2671_;
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
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
v_a_2699_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2668_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2668_);
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
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_dec(v___x_2665_);
lean_dec(v___x_2663_);
v___x_2707_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1));
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object* v_id_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec(v_id_2709_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object* v_bd_2713_){
_start:
{
lean_object* v_state_2715_; lean_object* v_id_2716_; lean_object* v___f_2717_; lean_object* v___x_2718_; 
v_state_2715_ = lean_ctor_get(v_bd_2713_, 0);
lean_inc_ref(v_state_2715_);
v_id_2716_ = lean_ctor_get(v_bd_2713_, 1);
lean_inc(v_id_2716_);
lean_dec_ref(v_bd_2713_);
v___f_2717_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2717_, 0, v_id_2716_);
v___x_2718_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_2715_, v___f_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2743_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2743_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2743_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___y_2724_; 
if (lean_obj_tag(v_a_2719_) == 0)
{
lean_object* v_a_2729_; uint8_t v___x_2730_; 
v_a_2729_ = lean_ctor_get(v_a_2719_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v_a_2719_, 1);
v___x_2730_ = lean_unbox(v_a_2729_);
lean_dec(v_a_2729_);
switch(v___x_2730_)
{
case 0:
{
lean_object* v___x_2731_; 
v___x_2731_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_2724_ = v___x_2731_;
goto v___jp_2723_;
}
case 1:
{
lean_object* v___x_2732_; 
v___x_2732_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_2724_ = v___x_2732_;
goto v___jp_2723_;
}
default: 
{
lean_object* v___x_2733_; 
v___x_2733_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_2724_ = v___x_2733_;
goto v___jp_2723_;
}
}
}
else
{
lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2741_; 
lean_del_object(v___x_2721_);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2741_ == 0)
{
lean_object* v_unused_2742_; 
v_unused_2742_ = lean_ctor_get(v_a_2719_, 0);
lean_dec(v_unused_2742_);
v___x_2735_ = v_a_2719_;
v_isShared_2736_ = v_isSharedCheck_2741_;
goto v_resetjp_2734_;
}
else
{
lean_dec(v_a_2719_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2741_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2737_ = lean_box(0);
if (v_isShared_2736_ == 0)
{
lean_ctor_set_tag(v___x_2735_, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2737_);
v___x_2739_ = v___x_2735_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
v___jp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_inc_ref(v___y_2724_);
v___x_2725_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2724_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set_tag(v___x_2721_, 1);
lean_ctor_set(v___x_2721_, 0, v___x_2725_);
v___x_2727_ = v___x_2721_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
v_a_2744_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2718_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2718_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object* v_bd_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object* v_00_u03b1_2755_, lean_object* v_bd_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_bd_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(v_00_u03b1_2759_, v_bd_2760_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object* v_00_u03b1_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_a_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(v_00_u03b1_2767_, v_a_2768_);
lean_dec(v_a_2768_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object* v_00_u03b1_2771_, lean_object* v_place_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2772_, v_a_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2776_, lean_object* v_place_2777_, lean_object* v_a_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(v_00_u03b1_2776_, v_place_2777_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec(v_place_2777_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object* v_00_u03b1_2781_, lean_object* v_slot_2782_, lean_object* v_next_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2782_, v_next_2783_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_slot_2788_, lean_object* v_next_2789_, lean_object* v_a_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(v_00_u03b1_2787_, v_slot_2788_, v_next_2789_, v_a_2790_);
lean_dec(v_a_2790_);
lean_dec(v_next_2789_);
lean_dec(v_slot_2788_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object* v_00_u03b1_2793_, lean_object* v_next_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2794_, v_a_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object* v_00_u03b1_2798_, lean_object* v_next_2799_, lean_object* v_a_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(v_00_u03b1_2798_, v_next_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec(v_next_2799_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object* v_00_u03b4_2803_, lean_object* v_t_2804_, lean_object* v_k_2805_){
_start:
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2804_, v_k_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object* v_00_u03b4_2807_, lean_object* v_t_2808_, lean_object* v_k_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(v_00_u03b4_2807_, v_t_2808_, v_k_2809_);
lean_dec(v_k_2809_);
lean_dec(v_t_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2811_, lean_object* v_inst_2812_, lean_object* v_a_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_2813_, v___y_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2817_, lean_object* v_inst_2818_, lean_object* v_a_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2817_, v_inst_2818_, v_a_2819_, v___y_2820_);
lean_dec(v___y_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2823_, lean_object* v_k_2824_, lean_object* v_t_2825_, lean_object* v_h_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2824_, v_t_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2828_, lean_object* v_k_2829_, lean_object* v_t_2830_, lean_object* v_h_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2828_, v_k_2829_, v_t_2830_, v_h_2831_);
lean_dec(v_k_2829_);
return v_res_2832_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2833_, lean_object* v_y_2834_){
_start:
{
uint8_t v___x_2835_; 
v___x_2835_ = lean_nat_dec_lt(v_x_2833_, v_y_2834_);
if (v___x_2835_ == 0)
{
uint8_t v___x_2836_; 
v___x_2836_ = lean_nat_dec_eq(v_x_2833_, v_y_2834_);
if (v___x_2836_ == 0)
{
uint8_t v___x_2837_; 
v___x_2837_ = 2;
return v___x_2837_;
}
else
{
uint8_t v___x_2838_; 
v___x_2838_ = 1;
return v___x_2838_;
}
}
else
{
uint8_t v___x_2839_; 
v___x_2839_ = 0;
return v___x_2839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2840_, lean_object* v_y_2841_){
_start:
{
uint8_t v_res_2842_; lean_object* v_r_2843_; 
v_res_2842_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2840_, v_y_2841_);
lean_dec(v_y_2841_);
lean_dec(v_x_2840_);
v_r_2843_ = lean_box(v_res_2842_);
return v_r_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2844_){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_unsigned_to_nat(1u);
v___x_2846_ = lean_nat_add(v_x_2844_, v___x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2847_);
lean_dec(v_x_2847_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2849_, lean_object* v_receiverId_2850_, lean_object* v___f_2851_, lean_object* v_receivers_2852_, lean_object* v_s_2853_){
_start:
{
lean_object* v_producers_2854_; lean_object* v_waiters_2855_; lean_object* v_capacity_2856_; lean_object* v_size_2857_; lean_object* v_buffer_2858_; lean_object* v_write_2859_; lean_object* v_read_2860_; lean_object* v_nextId_2861_; uint8_t v_closed_2862_; lean_object* v_pos_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2873_; 
v_producers_2854_ = lean_ctor_get(v_s_2853_, 0);
v_waiters_2855_ = lean_ctor_get(v_s_2853_, 1);
v_capacity_2856_ = lean_ctor_get(v_s_2853_, 2);
v_size_2857_ = lean_ctor_get(v_s_2853_, 3);
v_buffer_2858_ = lean_ctor_get(v_s_2853_, 4);
v_write_2859_ = lean_ctor_get(v_s_2853_, 5);
v_read_2860_ = lean_ctor_get(v_s_2853_, 6);
v_nextId_2861_ = lean_ctor_get(v_s_2853_, 8);
v_closed_2862_ = lean_ctor_get_uint8(v_s_2853_, sizeof(void*)*10);
v_pos_2863_ = lean_ctor_get(v_s_2853_, 9);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_s_2853_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v_s_2853_, 7);
lean_dec(v_unused_2874_);
v___x_2865_ = v_s_2853_;
v_isShared_2866_ = v_isSharedCheck_2873_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_pos_2863_);
lean_inc(v_nextId_2861_);
lean_inc(v_read_2860_);
lean_inc(v_write_2859_);
lean_inc(v_buffer_2858_);
lean_inc(v_size_2857_);
lean_inc(v_capacity_2856_);
lean_inc(v_waiters_2855_);
lean_inc(v_producers_2854_);
lean_dec(v_s_2853_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2873_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2867_ = lean_box(0);
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2849_, v_receiverId_2850_, v___f_2851_, v_receivers_2852_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 7, v___x_2868_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_producers_2854_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v_waiters_2855_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_capacity_2856_);
lean_ctor_set(v_reuseFailAlloc_2872_, 3, v_size_2857_);
lean_ctor_set(v_reuseFailAlloc_2872_, 4, v_buffer_2858_);
lean_ctor_set(v_reuseFailAlloc_2872_, 5, v_write_2859_);
lean_ctor_set(v_reuseFailAlloc_2872_, 6, v_read_2860_);
lean_ctor_set(v_reuseFailAlloc_2872_, 7, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2872_, 8, v_nextId_2861_);
lean_ctor_set(v_reuseFailAlloc_2872_, 9, v_pos_2863_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, sizeof(void*)*10, v_closed_2862_);
v___x_2870_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; 
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2867_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
return v___x_2871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_toPure_2878_; lean_object* v___x_2879_; 
v_toPure_2878_ = lean_ctor_get(v_toApplicative_2875_, 1);
lean_inc(v_toPure_2878_);
lean_dec_ref(v_toApplicative_2875_);
v___x_2879_ = lean_apply_2(v_toPure_2878_, lean_box(0), v_a_2876_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2880_, lean_object* v_a_2881_, lean_object* v___f_2882_, lean_object* v_inst_2883_, lean_object* v_toBind_2884_, lean_object* v_a_2885_){
_start:
{
if (lean_obj_tag(v_a_2885_) == 1)
{
lean_object* v___f_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___f_2886_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2886_, 0, v_toApplicative_2880_);
lean_closure_set(v___f_2886_, 1, v_a_2885_);
lean_inc(v_a_2881_);
v___x_2887_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2887_, 0, lean_box(0));
lean_closure_set(v___x_2887_, 1, lean_box(0));
lean_closure_set(v___x_2887_, 2, lean_box(0));
lean_closure_set(v___x_2887_, 3, v_a_2881_);
lean_closure_set(v___x_2887_, 4, v___f_2882_);
v___x_2888_ = lean_apply_2(v_inst_2883_, lean_box(0), v___x_2887_);
v___x_2889_ = lean_apply_4(v_toBind_2884_, lean_box(0), lean_box(0), v___x_2888_, v___f_2886_);
return v___x_2889_;
}
else
{
lean_object* v_toPure_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec(v_a_2885_);
lean_dec(v_toBind_2884_);
lean_dec(v_inst_2883_);
lean_dec_ref(v___f_2882_);
v_toPure_2890_ = lean_ctor_get(v_toApplicative_2880_, 1);
lean_inc(v_toPure_2890_);
lean_dec_ref(v_toApplicative_2880_);
v___x_2891_ = lean_box(0);
v___x_2892_ = lean_apply_2(v_toPure_2890_, lean_box(0), v___x_2891_);
return v___x_2892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_2893_, lean_object* v_a_2894_, lean_object* v___f_2895_, lean_object* v_inst_2896_, lean_object* v_toBind_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(v_toApplicative_2893_, v_a_2894_, v___f_2895_, v_inst_2896_, v_toBind_2897_, v_a_2898_);
lean_dec(v_a_2894_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2900_, lean_object* v_receiverId_2901_, lean_object* v___f_2902_, lean_object* v___f_2903_, lean_object* v_toApplicative_2904_, lean_object* v_a_2905_, lean_object* v_inst_2906_, lean_object* v_toBind_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_receivers_2911_; lean_object* v___x_2912_; 
v_receivers_2911_ = lean_ctor_get(v_a_2910_, 7);
lean_inc_n(v_receivers_2911_, 2);
lean_dec_ref(v_a_2910_);
lean_inc(v_receiverId_2901_);
v___x_2912_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2900_, v_receivers_2911_, v_receiverId_2901_);
if (lean_obj_tag(v___x_2912_) == 1)
{
lean_object* v_val_2913_; lean_object* v___f_2914_; lean_object* v___f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_val_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_val_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v___f_2914_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2914_, 0, v___f_2902_);
lean_closure_set(v___f_2914_, 1, v_receiverId_2901_);
lean_closure_set(v___f_2914_, 2, v___f_2903_);
lean_closure_set(v___f_2914_, 3, v_receivers_2911_);
lean_inc(v_toBind_2907_);
lean_inc(v_inst_2906_);
lean_inc(v_a_2905_);
v___f_2915_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2915_, 0, v_toApplicative_2904_);
lean_closure_set(v___f_2915_, 1, v_a_2905_);
lean_closure_set(v___f_2915_, 2, v___f_2914_);
lean_closure_set(v___f_2915_, 3, v_inst_2906_);
lean_closure_set(v___f_2915_, 4, v_toBind_2907_);
v___x_2916_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2908_, v_inst_2906_, v_inst_2909_, v_val_2913_, v_a_2905_);
v___x_2917_ = lean_apply_4(v_toBind_2907_, lean_box(0), lean_box(0), v___x_2916_, v___f_2915_);
return v___x_2917_;
}
else
{
lean_object* v_toPure_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec(v___x_2912_);
lean_dec(v_receivers_2911_);
lean_dec(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
lean_dec(v_toBind_2907_);
lean_dec(v_inst_2906_);
lean_dec_ref(v___f_2903_);
lean_dec_ref(v___f_2902_);
lean_dec(v_receiverId_2901_);
v_toPure_2918_ = lean_ctor_get(v_toApplicative_2904_, 1);
lean_inc(v_toPure_2918_);
lean_dec_ref(v_toApplicative_2904_);
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_apply_2(v_toPure_2918_, lean_box(0), v___x_2919_);
return v___x_2920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object* v___f_2921_, lean_object* v_receiverId_2922_, lean_object* v___f_2923_, lean_object* v___f_2924_, lean_object* v_toApplicative_2925_, lean_object* v_a_2926_, lean_object* v_inst_2927_, lean_object* v_toBind_2928_, lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(v___f_2921_, v_receiverId_2922_, v___f_2923_, v___f_2924_, v_toApplicative_2925_, v_a_2926_, v_inst_2927_, v_toBind_2928_, v_inst_2929_, v_inst_2930_, v_a_2931_);
lean_dec(v_a_2926_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_receiverId_2938_, lean_object* v_a_2939_){
_start:
{
lean_object* v_toApplicative_2940_; lean_object* v_toBind_2941_; lean_object* v___f_2942_; lean_object* v___f_2943_; lean_object* v___f_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_toApplicative_2940_ = lean_ctor_get(v_inst_2935_, 0);
lean_inc_ref(v_toApplicative_2940_);
v_toBind_2941_ = lean_ctor_get(v_inst_2935_, 1);
lean_inc_n(v_toBind_2941_, 2);
v___f_2942_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_2943_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_inst_2936_);
lean_inc_n(v_a_2939_, 2);
v___f_2944_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_2944_, 0, v___f_2942_);
lean_closure_set(v___f_2944_, 1, v_receiverId_2938_);
lean_closure_set(v___f_2944_, 2, v___f_2942_);
lean_closure_set(v___f_2944_, 3, v___f_2943_);
lean_closure_set(v___f_2944_, 4, v_toApplicative_2940_);
lean_closure_set(v___f_2944_, 5, v_a_2939_);
lean_closure_set(v___f_2944_, 6, v_inst_2936_);
lean_closure_set(v___f_2944_, 7, v_toBind_2941_);
lean_closure_set(v___f_2944_, 8, v_inst_2935_);
lean_closure_set(v___f_2944_, 9, v_inst_2937_);
v___x_2945_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2945_, 0, lean_box(0));
lean_closure_set(v___x_2945_, 1, lean_box(0));
lean_closure_set(v___x_2945_, 2, v_a_2939_);
v___x_2946_ = lean_apply_2(v_inst_2936_, lean_box(0), v___x_2945_);
v___x_2947_ = lean_apply_4(v_toBind_2941_, lean_box(0), lean_box(0), v___x_2946_, v___f_2944_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_inst_2950_, lean_object* v_receiverId_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2948_, v_inst_2949_, v_inst_2950_, v_receiverId_2951_, v_a_2952_);
lean_dec(v_a_2952_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_2954_, lean_object* v_00_u03b1_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_receiverId_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_2956_, v_inst_2957_, v_inst_2958_, v_receiverId_2959_, v_a_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object* v_m_2962_, lean_object* v_00_u03b1_2963_, lean_object* v_inst_2964_, lean_object* v_inst_2965_, lean_object* v_inst_2966_, lean_object* v_receiverId_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(v_m_2962_, v_00_u03b1_2963_, v_inst_2964_, v_inst_2965_, v_inst_2966_, v_receiverId_2967_, v_a_2968_);
lean_dec(v_a_2968_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_2970_, lean_object* v_t_2971_){
_start:
{
if (lean_obj_tag(v_t_2971_) == 0)
{
lean_object* v_size_2972_; lean_object* v_k_2973_; lean_object* v_v_2974_; lean_object* v_l_2975_; lean_object* v_r_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2995_; 
v_size_2972_ = lean_ctor_get(v_t_2971_, 0);
v_k_2973_ = lean_ctor_get(v_t_2971_, 1);
v_v_2974_ = lean_ctor_get(v_t_2971_, 2);
v_l_2975_ = lean_ctor_get(v_t_2971_, 3);
v_r_2976_ = lean_ctor_get(v_t_2971_, 4);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_t_2971_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2978_ = v_t_2971_;
v_isShared_2979_ = v_isSharedCheck_2995_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_r_2976_);
lean_inc(v_l_2975_);
lean_inc(v_v_2974_);
lean_inc(v_k_2973_);
lean_inc(v_size_2972_);
lean_dec(v_t_2971_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2995_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
uint8_t v___x_2980_; 
v___x_2980_ = lean_nat_dec_lt(v_k_2970_, v_k_2973_);
if (v___x_2980_ == 0)
{
uint8_t v___x_2981_; 
v___x_2981_ = lean_nat_dec_eq(v_k_2970_, v_k_2973_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2982_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2970_, v_r_2976_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 4, v___x_2982_);
v___x_2984_ = v___x_2978_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_size_2972_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_k_2973_);
lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_v_2974_);
lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_l_2975_);
lean_ctor_set(v_reuseFailAlloc_2985_, 4, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
lean_dec(v_k_2973_);
v___x_2986_ = lean_unsigned_to_nat(1u);
v___x_2987_ = lean_nat_add(v_v_2974_, v___x_2986_);
lean_dec(v_v_2974_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 2, v___x_2987_);
lean_ctor_set(v___x_2978_, 1, v_k_2970_);
v___x_2989_ = v___x_2978_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_size_2972_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_k_2970_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v_l_2975_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_r_2976_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2991_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_2970_, v_l_2975_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 3, v___x_2991_);
v___x_2993_ = v___x_2978_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_size_2972_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_k_2973_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_v_2974_);
lean_ctor_set(v_reuseFailAlloc_2994_, 3, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2994_, 4, v_r_2976_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_dec(v_k_2970_);
return v_t_2971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_2996_, lean_object* v_next_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v_fst_3001_; lean_object* v_snd_3002_; lean_object* v_value_3004_; lean_object* v_pos_3005_; lean_object* v_remaining_3006_; uint8_t v___x_3007_; 
v___x_2999_ = lean_st_ref_take(v_slot_2996_);
v_value_3004_ = lean_ctor_get(v___x_2999_, 0);
v_pos_3005_ = lean_ctor_get(v___x_2999_, 1);
v_remaining_3006_ = lean_ctor_get(v___x_2999_, 2);
v___x_3007_ = lean_nat_dec_eq(v_next_2997_, v_pos_3005_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_box(v___x_3007_);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3008_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v_fst_3001_ = v___x_3010_;
v_snd_3002_ = v___x_2999_;
goto v___jp_3000_;
}
else
{
lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3029_; 
lean_inc(v_remaining_3006_);
lean_inc(v_pos_3005_);
lean_inc(v_value_3004_);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; lean_object* v_unused_3031_; lean_object* v_unused_3032_; 
v_unused_3030_ = lean_ctor_get(v___x_2999_, 2);
lean_dec(v_unused_3030_);
v_unused_3031_ = lean_ctor_get(v___x_2999_, 1);
lean_dec(v_unused_3031_);
v_unused_3032_ = lean_ctor_get(v___x_2999_, 0);
lean_dec(v_unused_3032_);
v___x_3012_ = v___x_2999_;
v_isShared_3013_ = v_isSharedCheck_3029_;
goto v_resetjp_3011_;
}
else
{
lean_dec(v___x_2999_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3029_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3014_ = lean_unsigned_to_nat(1u);
v___x_3015_ = lean_nat_dec_eq(v_remaining_3006_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3016_ = lean_box(v___x_3015_);
lean_inc(v_value_3004_);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v_value_3004_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = lean_nat_sub(v_remaining_3006_, v___x_3014_);
lean_dec(v_remaining_3006_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 2, v___x_3018_);
v___x_3020_ = v___x_3012_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_value_3004_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_pos_3005_);
lean_ctor_set(v_reuseFailAlloc_3021_, 2, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
v_fst_3001_ = v___x_3017_;
v_snd_3002_ = v___x_3020_;
goto v___jp_3000_;
}
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
lean_dec(v_remaining_3006_);
v___x_3022_ = lean_box(v___x_3007_);
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_value_3004_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_box(0);
v___x_3025_ = lean_unsigned_to_nat(0u);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 2, v___x_3025_);
lean_ctor_set(v___x_3012_, 0, v___x_3024_);
v___x_3027_ = v___x_3012_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_pos_3005_);
lean_ctor_set(v_reuseFailAlloc_3028_, 2, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
v_fst_3001_ = v___x_3023_;
v_snd_3002_ = v___x_3027_;
goto v___jp_3000_;
}
}
}
}
v___jp_3000_:
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_st_ref_put(v_slot_2996_, v_snd_3002_);
return v_fst_3001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_3033_, lean_object* v_next_3034_, lean_object* v___y_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3033_, v_next_3034_);
lean_dec(v_next_3034_);
lean_dec(v_slot_3033_);
return v_res_3036_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; lean_object* v_size_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3039_ = lean_st_ref_get(v_a_3037_);
v_size_3040_ = lean_ctor_get(v___x_3039_, 3);
lean_inc(v_size_3040_);
lean_dec(v___x_3039_);
v___x_3041_ = lean_unsigned_to_nat(0u);
v___x_3042_ = lean_nat_dec_eq(v_size_3040_, v___x_3041_);
lean_dec(v_size_3040_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_3043_, lean_object* v___y_3044_){
_start:
{
uint8_t v_res_3045_; lean_object* v_r_3046_; 
v_res_3045_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3043_);
lean_dec(v_a_3043_);
v_r_3046_ = lean_box(v_res_3045_);
return v_r_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v_capacity_3051_; lean_object* v_buffer_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3050_ = lean_st_ref_get(v_a_3048_);
v_capacity_3051_ = lean_ctor_get(v___x_3050_, 2);
lean_inc(v_capacity_3051_);
v_buffer_3052_ = lean_ctor_get(v___x_3050_, 4);
lean_inc_ref(v_buffer_3052_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_nat_mod(v_place_3047_, v_capacity_3051_);
lean_dec(v_capacity_3051_);
v___x_3054_ = lean_array_fget(v_buffer_3052_, v___x_3053_);
lean_dec(v___x_3053_);
lean_dec_ref(v_buffer_3052_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_3055_, lean_object* v_a_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3055_, v_a_3056_);
lean_dec(v_a_3056_);
lean_dec(v_place_3055_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = lean_st_ref_get(v_a_3060_);
v___x_3063_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3060_);
if (v___x_3063_ == 0)
{
lean_object* v_capacity_3064_; uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v_fst_3069_; lean_object* v_snd_3070_; lean_object* v_st_3072_; lean_object* v___y_3073_; 
v_capacity_3064_ = lean_ctor_get(v___x_3062_, 2);
v___x_3065_ = 1;
v___x_3066_ = lean_nat_mod(v_next_3059_, v_capacity_3064_);
v___x_3067_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_3066_, v_a_3060_);
lean_dec(v___x_3066_);
v___x_3068_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_3067_, v_next_3059_);
lean_dec(v___x_3067_);
v_fst_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_fst_3069_);
v_snd_3070_ = lean_ctor_get(v___x_3068_, 1);
lean_inc(v_snd_3070_);
lean_dec_ref(v___x_3068_);
if (lean_obj_tag(v_fst_3069_) == 1)
{
uint8_t v___x_3075_; 
v___x_3075_ = lean_unbox(v_snd_3070_);
lean_dec(v_snd_3070_);
if (v___x_3075_ == 0)
{
v_st_3072_ = v___x_3062_;
v___y_3073_ = v_a_3060_;
goto v___jp_3071_;
}
else
{
lean_object* v___x_3076_; lean_object* v_producers_3077_; lean_object* v_waiters_3078_; lean_object* v_capacity_3079_; lean_object* v_size_3080_; lean_object* v_buffer_3081_; lean_object* v_write_3082_; lean_object* v_read_3083_; lean_object* v_receivers_3084_; lean_object* v_nextId_3085_; uint8_t v_closed_3086_; lean_object* v_pos_3087_; lean_object* v___x_3088_; 
v___x_3076_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_3062_);
v_producers_3077_ = lean_ctor_get(v___x_3076_, 0);
v_waiters_3078_ = lean_ctor_get(v___x_3076_, 1);
v_capacity_3079_ = lean_ctor_get(v___x_3076_, 2);
v_size_3080_ = lean_ctor_get(v___x_3076_, 3);
v_buffer_3081_ = lean_ctor_get(v___x_3076_, 4);
v_write_3082_ = lean_ctor_get(v___x_3076_, 5);
v_read_3083_ = lean_ctor_get(v___x_3076_, 6);
v_receivers_3084_ = lean_ctor_get(v___x_3076_, 7);
v_nextId_3085_ = lean_ctor_get(v___x_3076_, 8);
v_closed_3086_ = lean_ctor_get_uint8(v___x_3076_, sizeof(void*)*10);
v_pos_3087_ = lean_ctor_get(v___x_3076_, 9);
lean_inc_ref(v_producers_3077_);
v___x_3088_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3077_);
if (lean_obj_tag(v___x_3088_) == 1)
{
lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3100_; 
lean_inc(v_pos_3087_);
lean_inc(v_nextId_3085_);
lean_inc(v_receivers_3084_);
lean_inc(v_read_3083_);
lean_inc(v_write_3082_);
lean_inc_ref(v_buffer_3081_);
lean_inc(v_size_3080_);
lean_inc(v_capacity_3079_);
lean_inc_ref(v_waiters_3078_);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; lean_object* v_unused_3102_; lean_object* v_unused_3103_; lean_object* v_unused_3104_; lean_object* v_unused_3105_; lean_object* v_unused_3106_; lean_object* v_unused_3107_; lean_object* v_unused_3108_; lean_object* v_unused_3109_; lean_object* v_unused_3110_; 
v_unused_3101_ = lean_ctor_get(v___x_3076_, 9);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v___x_3076_, 8);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v___x_3076_, 7);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v___x_3076_, 6);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v___x_3076_, 5);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v___x_3076_, 4);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v___x_3076_, 3);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v___x_3076_, 2);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v___x_3076_, 1);
lean_dec(v_unused_3109_);
v_unused_3110_ = lean_ctor_get(v___x_3076_, 0);
lean_dec(v_unused_3110_);
v___x_3090_ = v___x_3076_;
v_isShared_3091_ = v_isSharedCheck_3100_;
goto v_resetjp_3089_;
}
else
{
lean_dec(v___x_3076_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3100_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v_val_3092_; lean_object* v_fst_3093_; lean_object* v_snd_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v_val_3092_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v___x_3088_, 1);
v_fst_3093_ = lean_ctor_get(v_val_3092_, 0);
lean_inc(v_fst_3093_);
v_snd_3094_ = lean_ctor_get(v_val_3092_, 1);
lean_inc(v_snd_3094_);
lean_dec(v_val_3092_);
v___x_3095_ = lean_box(v___x_3065_);
v___x_3096_ = lean_io_promise_resolve(v___x_3095_, v_fst_3093_);
lean_dec(v_fst_3093_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v_snd_3094_);
v___x_3098_ = v___x_3090_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_snd_3094_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_waiters_3078_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_capacity_3079_);
lean_ctor_set(v_reuseFailAlloc_3099_, 3, v_size_3080_);
lean_ctor_set(v_reuseFailAlloc_3099_, 4, v_buffer_3081_);
lean_ctor_set(v_reuseFailAlloc_3099_, 5, v_write_3082_);
lean_ctor_set(v_reuseFailAlloc_3099_, 6, v_read_3083_);
lean_ctor_set(v_reuseFailAlloc_3099_, 7, v_receivers_3084_);
lean_ctor_set(v_reuseFailAlloc_3099_, 8, v_nextId_3085_);
lean_ctor_set(v_reuseFailAlloc_3099_, 9, v_pos_3087_);
lean_ctor_set_uint8(v_reuseFailAlloc_3099_, sizeof(void*)*10, v_closed_3086_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
v_st_3072_ = v___x_3098_;
v___y_3073_ = v_a_3060_;
goto v___jp_3071_;
}
}
}
else
{
lean_dec(v___x_3088_);
v_st_3072_ = v___x_3076_;
v___y_3073_ = v_a_3060_;
goto v___jp_3071_;
}
}
}
else
{
lean_object* v___x_3111_; 
lean_dec(v_snd_3070_);
lean_dec(v_fst_3069_);
lean_dec(v___x_3062_);
v___x_3111_ = lean_box(0);
return v___x_3111_;
}
v___jp_3071_:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_st_ref_swap(v___y_3073_, v_st_3072_);
lean_dec(v___x_3074_);
return v_fst_3069_;
}
}
else
{
lean_object* v___x_3112_; 
lean_dec(v___x_3062_);
v___x_3112_ = lean_box(0);
return v___x_3112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_3113_, lean_object* v_a_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3113_, v_a_3114_);
lean_dec(v_a_3114_);
lean_dec(v_next_3113_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v___x_3120_; lean_object* v_receivers_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_st_ref_get(v_a_3118_);
v_receivers_3121_ = lean_ctor_get(v___x_3120_, 7);
lean_inc(v_receivers_3121_);
lean_dec(v___x_3120_);
v___x_3122_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3121_, v_receiverId_3117_);
if (lean_obj_tag(v___x_3122_) == 1)
{
lean_object* v_val_3123_; lean_object* v___x_3124_; 
v_val_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_val_3123_);
lean_dec_ref_known(v___x_3122_, 1);
v___x_3124_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_3123_, v_a_3118_);
lean_dec(v_val_3123_);
if (lean_obj_tag(v___x_3124_) == 1)
{
lean_object* v___x_3125_; lean_object* v_producers_3126_; lean_object* v_waiters_3127_; lean_object* v_capacity_3128_; lean_object* v_size_3129_; lean_object* v_buffer_3130_; lean_object* v_write_3131_; lean_object* v_read_3132_; lean_object* v_nextId_3133_; uint8_t v_closed_3134_; lean_object* v_pos_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3144_; 
v___x_3125_ = lean_st_ref_take(v_a_3118_);
v_producers_3126_ = lean_ctor_get(v___x_3125_, 0);
v_waiters_3127_ = lean_ctor_get(v___x_3125_, 1);
v_capacity_3128_ = lean_ctor_get(v___x_3125_, 2);
v_size_3129_ = lean_ctor_get(v___x_3125_, 3);
v_buffer_3130_ = lean_ctor_get(v___x_3125_, 4);
v_write_3131_ = lean_ctor_get(v___x_3125_, 5);
v_read_3132_ = lean_ctor_get(v___x_3125_, 6);
v_nextId_3133_ = lean_ctor_get(v___x_3125_, 8);
v_closed_3134_ = lean_ctor_get_uint8(v___x_3125_, sizeof(void*)*10);
v_pos_3135_ = lean_ctor_get(v___x_3125_, 9);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v___x_3125_, 7);
lean_dec(v_unused_3145_);
v___x_3137_ = v___x_3125_;
v_isShared_3138_ = v_isSharedCheck_3144_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_pos_3135_);
lean_inc(v_nextId_3133_);
lean_inc(v_read_3132_);
lean_inc(v_write_3131_);
lean_inc(v_buffer_3130_);
lean_inc(v_size_3129_);
lean_inc(v_capacity_3128_);
lean_inc(v_waiters_3127_);
lean_inc(v_producers_3126_);
lean_dec(v___x_3125_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3144_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3117_, v_receivers_3121_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 7, v___x_3139_);
v___x_3141_ = v___x_3137_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_producers_3126_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_waiters_3127_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_capacity_3128_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_size_3129_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_buffer_3130_);
lean_ctor_set(v_reuseFailAlloc_3143_, 5, v_write_3131_);
lean_ctor_set(v_reuseFailAlloc_3143_, 6, v_read_3132_);
lean_ctor_set(v_reuseFailAlloc_3143_, 7, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3143_, 8, v_nextId_3133_);
lean_ctor_set(v_reuseFailAlloc_3143_, 9, v_pos_3135_);
lean_ctor_set_uint8(v_reuseFailAlloc_3143_, sizeof(void*)*10, v_closed_3134_);
v___x_3141_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_st_ref_put(v_a_3118_, v___x_3141_);
return v___x_3124_;
}
}
}
else
{
lean_object* v___x_3146_; 
lean_dec(v___x_3124_);
lean_dec(v_receivers_3121_);
lean_dec(v_receiverId_3117_);
v___x_3146_ = lean_box(0);
return v___x_3146_;
}
}
else
{
lean_object* v___x_3147_; 
lean_dec(v___x_3122_);
lean_dec(v_receivers_3121_);
lean_dec(v_receiverId_3117_);
v___x_3147_ = lean_box(0);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3148_, lean_object* v_a_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3148_, v_a_3149_);
lean_dec(v_a_3149_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3152_, v___y_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3156_, v___y_3157_);
lean_dec(v___y_3157_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3160_){
_start:
{
lean_object* v_state_3162_; lean_object* v_id_3163_; lean_object* v___f_3164_; lean_object* v___x_3165_; 
v_state_3162_ = lean_ctor_get(v_ch_3160_, 0);
lean_inc_ref(v_state_3162_);
v_id_3163_ = lean_ctor_get(v_ch_3160_, 1);
lean_inc(v_id_3163_);
lean_dec_ref(v_ch_3160_);
v___f_3164_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3164_, 0, v_id_3163_);
v___x_3165_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3162_, v___f_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3166_, lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3166_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3169_, lean_object* v_ch_3170_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3170_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3173_, lean_object* v_ch_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3173_, v_ch_3174_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3177_, lean_object* v_receiverId_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3178_, v_a_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3182_, lean_object* v_receiverId_3183_, lean_object* v_a_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3182_, v_receiverId_3183_, v_a_3184_);
lean_dec(v_a_3184_);
return v_res_3186_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3187_, lean_object* v_a_3188_){
_start:
{
uint8_t v___x_3190_; 
v___x_3190_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3188_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3191_, lean_object* v_a_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v_res_3194_; lean_object* v_r_3195_; 
v_res_3194_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3191_, v_a_3192_);
lean_dec(v_a_3192_);
v_r_3195_ = lean_box(v_res_3194_);
return v_r_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3196_, lean_object* v_place_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3197_, v_a_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3201_, lean_object* v_place_3202_, lean_object* v_a_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3201_, v_place_3202_, v_a_3203_);
lean_dec(v_a_3203_);
lean_dec(v_place_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3206_, lean_object* v_slot_3207_, lean_object* v_next_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3207_, v_next_3208_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3212_, lean_object* v_slot_3213_, lean_object* v_next_3214_, lean_object* v_a_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3212_, v_slot_3213_, v_next_3214_, v_a_3215_);
lean_dec(v_a_3215_);
lean_dec(v_next_3214_);
lean_dec(v_slot_3213_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3218_, lean_object* v_next_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3219_, v_a_3220_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3223_, lean_object* v_next_3224_, lean_object* v_a_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3223_, v_next_3224_, v_a_3225_);
lean_dec(v_a_3225_);
lean_dec(v_next_3224_);
return v_res_3227_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3228_, lean_object* v_t_3229_){
_start:
{
if (lean_obj_tag(v_t_3229_) == 0)
{
lean_object* v_k_3230_; lean_object* v_l_3231_; lean_object* v_r_3232_; uint8_t v___x_3233_; 
v_k_3230_ = lean_ctor_get(v_t_3229_, 1);
v_l_3231_ = lean_ctor_get(v_t_3229_, 3);
v_r_3232_ = lean_ctor_get(v_t_3229_, 4);
v___x_3233_ = lean_nat_dec_lt(v_k_3228_, v_k_3230_);
if (v___x_3233_ == 0)
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_nat_dec_eq(v_k_3228_, v_k_3230_);
if (v___x_3234_ == 0)
{
v_t_3229_ = v_r_3232_;
goto _start;
}
else
{
return v___x_3234_;
}
}
else
{
v_t_3229_ = v_l_3231_;
goto _start;
}
}
else
{
uint8_t v___x_3237_; 
v___x_3237_ = 0;
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3238_, lean_object* v_t_3239_){
_start:
{
uint8_t v_res_3240_; lean_object* v_r_3241_; 
v_res_3240_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3238_, v_t_3239_);
lean_dec(v_t_3239_);
lean_dec(v_k_3238_);
v_r_3241_ = lean_box(v_res_3240_);
return v_r_3241_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = lean_box(0);
v___x_3243_ = lean_task_pure(v___x_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3244_, lean_object* v___f_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v___x_3248_; lean_object* v_receivers_3249_; uint8_t v___x_3250_; 
v___x_3248_ = lean_st_ref_get(v___y_3246_);
v_receivers_3249_ = lean_ctor_get(v___x_3248_, 7);
lean_inc(v_receivers_3249_);
lean_dec(v___x_3248_);
v___x_3250_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3244_, v_receivers_3249_);
lean_dec(v_receivers_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref(v___f_3245_);
lean_dec(v_id_3244_);
v___x_3251_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3244_, v___y_3246_);
if (lean_obj_tag(v___x_3252_) == 1)
{
lean_object* v___x_3253_; 
lean_dec_ref(v___f_3245_);
v___x_3253_ = lean_task_pure(v___x_3252_);
return v___x_3253_;
}
else
{
lean_object* v___x_3254_; uint8_t v_closed_3255_; 
lean_dec(v___x_3252_);
v___x_3254_ = lean_st_ref_get(v___y_3246_);
v_closed_3255_ = lean_ctor_get_uint8(v___x_3254_, sizeof(void*)*10);
lean_dec(v___x_3254_);
if (v_closed_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v_producers_3258_; lean_object* v_waiters_3259_; lean_object* v_capacity_3260_; lean_object* v_size_3261_; lean_object* v_buffer_3262_; lean_object* v_write_3263_; lean_object* v_read_3264_; lean_object* v_receivers_3265_; lean_object* v_nextId_3266_; uint8_t v_closed_3267_; lean_object* v_pos_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3282_; 
v___x_3256_ = lean_io_promise_new();
v___x_3257_ = lean_st_ref_take(v___y_3246_);
v_producers_3258_ = lean_ctor_get(v___x_3257_, 0);
v_waiters_3259_ = lean_ctor_get(v___x_3257_, 1);
v_capacity_3260_ = lean_ctor_get(v___x_3257_, 2);
v_size_3261_ = lean_ctor_get(v___x_3257_, 3);
v_buffer_3262_ = lean_ctor_get(v___x_3257_, 4);
v_write_3263_ = lean_ctor_get(v___x_3257_, 5);
v_read_3264_ = lean_ctor_get(v___x_3257_, 6);
v_receivers_3265_ = lean_ctor_get(v___x_3257_, 7);
v_nextId_3266_ = lean_ctor_get(v___x_3257_, 8);
v_closed_3267_ = lean_ctor_get_uint8(v___x_3257_, sizeof(void*)*10);
v_pos_3268_ = lean_ctor_get(v___x_3257_, 9);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3270_ = v___x_3257_;
v_isShared_3271_ = v_isSharedCheck_3282_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_pos_3268_);
lean_inc(v_nextId_3266_);
lean_inc(v_receivers_3265_);
lean_inc(v_read_3264_);
lean_inc(v_write_3263_);
lean_inc(v_buffer_3262_);
lean_inc(v_size_3261_);
lean_inc(v_capacity_3260_);
lean_inc(v_waiters_3259_);
lean_inc(v_producers_3258_);
lean_dec(v___x_3257_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3282_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3272_ = lean_box(0);
lean_inc(v___x_3256_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3256_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = l_Std_Queue_enqueue___redArg(v___x_3273_, v_waiters_3259_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 1, v___x_3274_);
v___x_3276_ = v___x_3270_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_producers_3258_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v_capacity_3260_);
lean_ctor_set(v_reuseFailAlloc_3281_, 3, v_size_3261_);
lean_ctor_set(v_reuseFailAlloc_3281_, 4, v_buffer_3262_);
lean_ctor_set(v_reuseFailAlloc_3281_, 5, v_write_3263_);
lean_ctor_set(v_reuseFailAlloc_3281_, 6, v_read_3264_);
lean_ctor_set(v_reuseFailAlloc_3281_, 7, v_receivers_3265_);
lean_ctor_set(v_reuseFailAlloc_3281_, 8, v_nextId_3266_);
lean_ctor_set(v_reuseFailAlloc_3281_, 9, v_pos_3268_);
lean_ctor_set_uint8(v_reuseFailAlloc_3281_, sizeof(void*)*10, v_closed_3267_);
v___x_3276_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3277_ = lean_st_ref_put(v___y_3246_, v___x_3276_);
v___x_3278_ = lean_io_promise_result_opt(v___x_3256_);
lean_dec(v___x_3256_);
v___x_3279_ = lean_unsigned_to_nat(0u);
v___x_3280_ = lean_io_bind_task(v___x_3278_, v___f_3245_, v___x_3279_, v_closed_3255_);
return v___x_3280_;
}
}
}
else
{
lean_object* v___x_3283_; 
lean_dec_ref(v___f_3245_);
v___x_3283_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3284_, lean_object* v___f_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3284_, v___f_3285_, v___y_3286_);
lean_dec(v___y_3286_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3289_, lean_object* v_res_3290_){
_start:
{
if (lean_obj_tag(v_res_3290_) == 0)
{
lean_dec_ref(v_ch_3289_);
goto v___jp_3292_;
}
else
{
lean_object* v_val_3294_; uint8_t v___x_3295_; 
v_val_3294_ = lean_ctor_get(v_res_3290_, 0);
v___x_3295_ = lean_unbox(v_val_3294_);
if (v___x_3295_ == 0)
{
lean_dec_ref(v_ch_3289_);
goto v___jp_3292_;
}
else
{
lean_object* v___x_3296_; 
v___x_3296_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3289_);
return v___x_3296_;
}
}
v___jp_3292_:
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3297_, lean_object* v_res_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3297_, v_res_3298_);
lean_dec(v_res_3298_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3301_){
_start:
{
lean_object* v_state_3303_; lean_object* v_id_3304_; lean_object* v___f_3305_; lean_object* v___f_3306_; lean_object* v___x_3307_; 
v_state_3303_ = lean_ctor_get(v_ch_3301_, 0);
lean_inc_ref(v_state_3303_);
v_id_3304_ = lean_ctor_get(v_ch_3301_, 1);
lean_inc(v_id_3304_);
v___f_3305_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3305_, 0, v_ch_3301_);
v___f_3306_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3306_, 0, v_id_3304_);
lean_closure_set(v___f_3306_, 1, v___f_3305_);
v___x_3307_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3303_, v___f_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3308_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3311_, lean_object* v_ch_3312_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3312_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3315_, lean_object* v_ch_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3315_, v_ch_3316_);
return v_res_3318_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3319_, lean_object* v_k_3320_, lean_object* v_t_3321_){
_start:
{
uint8_t v___x_3322_; 
v___x_3322_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3320_, v_t_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3323_, lean_object* v_k_3324_, lean_object* v_t_3325_){
_start:
{
uint8_t v_res_3326_; lean_object* v_r_3327_; 
v_res_3326_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3323_, v_k_3324_, v_t_3325_);
lean_dec(v_t_3325_);
lean_dec(v_k_3324_);
v_r_3327_ = lean_box(v_res_3326_);
return v_r_3327_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_task_pure(v___x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3330_, lean_object* v_ch_3331_, lean_object* v_prio_3332_, lean_object* v_x_3333_){
_start:
{
if (lean_obj_tag(v_x_3333_) == 0)
{
lean_object* v___x_3335_; 
lean_dec(v_prio_3332_);
lean_dec_ref(v_ch_3331_);
lean_dec_ref(v_f_3330_);
v___x_3335_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3335_;
}
else
{
lean_object* v_val_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_val_3336_ = lean_ctor_get(v_x_3333_, 0);
lean_inc(v_val_3336_);
lean_dec_ref_known(v_x_3333_, 1);
lean_inc_ref(v_f_3330_);
v___x_3337_ = lean_apply_2(v_f_3330_, v_val_3336_, lean_box(0));
v___x_3338_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3330_, v_ch_3331_, v_prio_3332_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3339_, lean_object* v_ch_3340_, lean_object* v_prio_3341_, lean_object* v_x_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3339_, v_ch_3340_, v_prio_3341_, v_x_3342_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3345_, lean_object* v_ch_3346_, lean_object* v_prio_3347_){
_start:
{
lean_object* v___f_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; 
lean_inc(v_prio_3347_);
lean_inc_ref(v_ch_3346_);
v___f_3349_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3349_, 0, v_f_3345_);
lean_closure_set(v___f_3349_, 1, v_ch_3346_);
lean_closure_set(v___f_3349_, 2, v_prio_3347_);
v___x_3350_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3346_);
v___x_3351_ = 0;
v___x_3352_ = lean_io_bind_task(v___x_3350_, v___f_3349_, v_prio_3347_, v___x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3353_, lean_object* v_ch_3354_, lean_object* v_prio_3355_, lean_object* v_a_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3353_, v_ch_3354_, v_prio_3355_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3358_, lean_object* v_f_3359_, lean_object* v_ch_3360_, lean_object* v_prio_3361_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3359_, v_ch_3360_, v_prio_3361_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3364_, lean_object* v_f_3365_, lean_object* v_ch_3366_, lean_object* v_prio_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3364_, v_f_3365_, v_ch_3366_, v_prio_3367_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3370_, lean_object* v_val_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_pos_3373_; lean_object* v_toPure_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_pos_3373_ = lean_ctor_get(v_a_3372_, 1);
v_toPure_3374_ = lean_ctor_get(v_toApplicative_3370_, 1);
lean_inc(v_toPure_3374_);
lean_dec_ref(v_toApplicative_3370_);
v___x_3375_ = lean_nat_dec_eq(v_pos_3373_, v_val_3371_);
v___x_3376_ = lean_box(v___x_3375_);
v___x_3377_ = lean_apply_2(v_toPure_3374_, lean_box(0), v___x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3378_, lean_object* v_val_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3378_, v_val_3379_, v_a_3380_);
lean_dec_ref(v_a_3380_);
lean_dec(v_val_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3382_, lean_object* v_toBind_3383_, lean_object* v___f_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3386_, 0, lean_box(0));
lean_closure_set(v___x_3386_, 1, lean_box(0));
lean_closure_set(v___x_3386_, 2, v_a_3385_);
v___x_3387_ = lean_apply_2(v_inst_3382_, lean_box(0), v___x_3386_);
v___x_3388_ = lean_apply_4(v_toBind_3383_, lean_box(0), lean_box(0), v___x_3387_, v___f_3384_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3389_, lean_object* v_receiverId_3390_, lean_object* v_toApplicative_3391_, lean_object* v_inst_3392_, lean_object* v_toBind_3393_, lean_object* v_inst_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
uint8_t v_closed_3397_; 
v_closed_3397_ = lean_ctor_get_uint8(v_a_3396_, sizeof(void*)*10);
if (v_closed_3397_ == 0)
{
lean_object* v_capacity_3398_; lean_object* v_size_3399_; lean_object* v_receivers_3400_; lean_object* v___x_3401_; 
v_capacity_3398_ = lean_ctor_get(v_a_3396_, 2);
lean_inc(v_capacity_3398_);
v_size_3399_ = lean_ctor_get(v_a_3396_, 3);
lean_inc(v_size_3399_);
v_receivers_3400_ = lean_ctor_get(v_a_3396_, 7);
lean_inc(v_receivers_3400_);
lean_dec_ref(v_a_3396_);
v___x_3401_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3389_, v_receivers_3400_, v_receiverId_3390_);
if (lean_obj_tag(v___x_3401_) == 1)
{
lean_object* v_val_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v_val_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_val_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v___x_3403_ = lean_unsigned_to_nat(0u);
v___x_3404_ = lean_nat_dec_eq(v_size_3399_, v___x_3403_);
lean_dec(v_size_3399_);
if (v___x_3404_ == 0)
{
lean_object* v___f_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
lean_inc(v_val_3402_);
v___f_3405_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3405_, 0, v_toApplicative_3391_);
lean_closure_set(v___f_3405_, 1, v_val_3402_);
lean_inc(v_toBind_3393_);
lean_inc(v_inst_3392_);
v___f_3406_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3406_, 0, v_inst_3392_);
lean_closure_set(v___f_3406_, 1, v_toBind_3393_);
lean_closure_set(v___f_3406_, 2, v___f_3405_);
v___x_3407_ = lean_nat_mod(v_val_3402_, v_capacity_3398_);
lean_dec(v_capacity_3398_);
lean_dec(v_val_3402_);
v___x_3408_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3394_, v_inst_3392_, v___x_3407_, v_a_3395_);
v___x_3409_ = lean_apply_4(v_toBind_3393_, lean_box(0), lean_box(0), v___x_3408_, v___f_3406_);
return v___x_3409_;
}
else
{
lean_object* v_toPure_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_dec(v_val_3402_);
lean_dec(v_capacity_3398_);
lean_dec_ref(v_inst_3394_);
lean_dec(v_toBind_3393_);
lean_dec(v_inst_3392_);
v_toPure_3410_ = lean_ctor_get(v_toApplicative_3391_, 1);
lean_inc(v_toPure_3410_);
lean_dec_ref(v_toApplicative_3391_);
v___x_3411_ = lean_box(v_closed_3397_);
v___x_3412_ = lean_apply_2(v_toPure_3410_, lean_box(0), v___x_3411_);
return v___x_3412_;
}
}
else
{
lean_object* v_toPure_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_dec(v___x_3401_);
lean_dec(v_size_3399_);
lean_dec(v_capacity_3398_);
lean_dec_ref(v_inst_3394_);
lean_dec(v_toBind_3393_);
lean_dec(v_inst_3392_);
v_toPure_3413_ = lean_ctor_get(v_toApplicative_3391_, 1);
lean_inc(v_toPure_3413_);
lean_dec_ref(v_toApplicative_3391_);
v___x_3414_ = lean_box(v_closed_3397_);
v___x_3415_ = lean_apply_2(v_toPure_3413_, lean_box(0), v___x_3414_);
return v___x_3415_;
}
}
else
{
lean_object* v_toPure_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref(v_a_3396_);
lean_dec_ref(v_inst_3394_);
lean_dec(v_toBind_3393_);
lean_dec(v_inst_3392_);
lean_dec(v_receiverId_3390_);
lean_dec_ref(v___f_3389_);
v_toPure_3416_ = lean_ctor_get(v_toApplicative_3391_, 1);
lean_inc(v_toPure_3416_);
lean_dec_ref(v_toApplicative_3391_);
v___x_3417_ = lean_box(v_closed_3397_);
v___x_3418_ = lean_apply_2(v_toPure_3416_, lean_box(0), v___x_3417_);
return v___x_3418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object* v___f_3419_, lean_object* v_receiverId_3420_, lean_object* v_toApplicative_3421_, lean_object* v_inst_3422_, lean_object* v_toBind_3423_, lean_object* v_inst_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(v___f_3419_, v_receiverId_3420_, v_toApplicative_3421_, v_inst_3422_, v_toBind_3423_, v_inst_3424_, v_a_3425_, v_a_3426_);
lean_dec(v_a_3425_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3428_, lean_object* v_inst_3429_, lean_object* v_receiverId_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v_toApplicative_3432_; lean_object* v_toBind_3433_; lean_object* v___f_3434_; lean_object* v___f_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v_toApplicative_3432_ = lean_ctor_get(v_inst_3428_, 0);
lean_inc_ref(v_toApplicative_3432_);
v_toBind_3433_ = lean_ctor_get(v_inst_3428_, 1);
lean_inc_n(v_toBind_3433_, 2);
v___f_3434_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3431_, 2);
lean_inc(v_inst_3429_);
v___f_3435_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3435_, 0, v___f_3434_);
lean_closure_set(v___f_3435_, 1, v_receiverId_3430_);
lean_closure_set(v___f_3435_, 2, v_toApplicative_3432_);
lean_closure_set(v___f_3435_, 3, v_inst_3429_);
lean_closure_set(v___f_3435_, 4, v_toBind_3433_);
lean_closure_set(v___f_3435_, 5, v_inst_3428_);
lean_closure_set(v___f_3435_, 6, v_a_3431_);
v___x_3436_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3436_, 0, lean_box(0));
lean_closure_set(v___x_3436_, 1, lean_box(0));
lean_closure_set(v___x_3436_, 2, v_a_3431_);
v___x_3437_ = lean_apply_2(v_inst_3429_, lean_box(0), v___x_3436_);
v___x_3438_ = lean_apply_4(v_toBind_3433_, lean_box(0), lean_box(0), v___x_3437_, v___f_3435_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object* v_inst_3439_, lean_object* v_inst_3440_, lean_object* v_receiverId_3441_, lean_object* v_a_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(v_inst_3439_, v_inst_3440_, v_receiverId_3441_, v_a_3442_);
lean_dec(v_a_3442_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3444_, lean_object* v_00_u03b1_3445_, lean_object* v_inst_3446_, lean_object* v_inst_3447_, lean_object* v_inst_3448_, lean_object* v_inst_3449_, lean_object* v_receiverId_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_toApplicative_3452_; lean_object* v_toBind_3453_; lean_object* v___f_3454_; lean_object* v___f_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_toApplicative_3452_ = lean_ctor_get(v_inst_3446_, 0);
lean_inc_ref(v_toApplicative_3452_);
v_toBind_3453_ = lean_ctor_get(v_inst_3446_, 1);
lean_inc_n(v_toBind_3453_, 2);
v___f_3454_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3451_, 2);
lean_inc(v_inst_3447_);
v___f_3455_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3455_, 0, v___f_3454_);
lean_closure_set(v___f_3455_, 1, v_receiverId_3450_);
lean_closure_set(v___f_3455_, 2, v_toApplicative_3452_);
lean_closure_set(v___f_3455_, 3, v_inst_3447_);
lean_closure_set(v___f_3455_, 4, v_toBind_3453_);
lean_closure_set(v___f_3455_, 5, v_inst_3446_);
lean_closure_set(v___f_3455_, 6, v_a_3451_);
v___x_3456_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3456_, 0, lean_box(0));
lean_closure_set(v___x_3456_, 1, lean_box(0));
lean_closure_set(v___x_3456_, 2, v_a_3451_);
v___x_3457_ = lean_apply_2(v_inst_3447_, lean_box(0), v___x_3456_);
v___x_3458_ = lean_apply_4(v_toBind_3453_, lean_box(0), lean_box(0), v___x_3457_, v___f_3455_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3459_, lean_object* v_00_u03b1_3460_, lean_object* v_inst_3461_, lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_receiverId_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3459_, v_00_u03b1_3460_, v_inst_3461_, v_inst_3462_, v_inst_3463_, v_inst_3464_, v_receiverId_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec(v_inst_3464_);
lean_dec(v_inst_3463_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3470_, lean_object* v_lose_3471_){
_start:
{
lean_object* v_finished_3473_; lean_object* v_promise_3474_; lean_object* v___x_3475_; uint8_t v___y_3477_; uint8_t v___x_3485_; 
v_finished_3473_ = lean_ctor_get(v_w_3470_, 0);
v_promise_3474_ = lean_ctor_get(v_w_3470_, 1);
v___x_3475_ = lean_st_ref_take(v_finished_3473_);
v___x_3485_ = lean_unbox(v___x_3475_);
lean_dec(v___x_3475_);
if (v___x_3485_ == 0)
{
uint8_t v___x_3486_; 
v___x_3486_ = 1;
v___y_3477_ = v___x_3486_;
goto v___jp_3476_;
}
else
{
uint8_t v___x_3487_; 
v___x_3487_ = 0;
v___y_3477_ = v___x_3487_;
goto v___jp_3476_;
}
v___jp_3476_:
{
uint8_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3478_ = 1;
v___x_3479_ = lean_box(v___x_3478_);
v___x_3480_ = lean_st_ref_put(v_finished_3473_, v___x_3479_);
if (v___y_3477_ == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_apply_1(v_lose_3471_, lean_box(0));
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; 
lean_dec_ref(v_lose_3471_);
v___x_3482_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3483_ = lean_io_promise_resolve(v___x_3482_, v_promise_3474_);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
return v___x_3484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3488_, lean_object* v_lose_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3488_, v_lose_3489_);
lean_dec_ref(v_w_3488_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3492_, lean_object* v_w_3493_, lean_object* v_lose_3494_){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3493_, v_lose_3494_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3497_, lean_object* v_w_3498_, lean_object* v_lose_3499_, lean_object* v___y_3500_){
_start:
{
lean_object* v_res_3501_; 
v_res_3501_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3497_, v_w_3498_, v_lose_3499_);
lean_dec_ref(v_w_3498_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v___x_3505_; lean_object* v_receivers_3506_; lean_object* v___x_3507_; 
v___x_3505_ = lean_st_ref_get(v_a_3503_);
v_receivers_3506_ = lean_ctor_get(v___x_3505_, 7);
lean_inc(v_receivers_3506_);
lean_dec(v___x_3505_);
v___x_3507_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3506_, v_receiverId_3502_);
if (lean_obj_tag(v___x_3507_) == 1)
{
lean_object* v_val_3508_; lean_object* v___x_3509_; 
v_val_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_val_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___x_3509_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3508_, v_a_3503_);
lean_dec(v_val_3508_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3542_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3542_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3542_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
if (lean_obj_tag(v_a_3510_) == 1)
{
lean_object* v___x_3514_; lean_object* v_producers_3515_; lean_object* v_waiters_3516_; lean_object* v_capacity_3517_; lean_object* v_size_3518_; lean_object* v_buffer_3519_; lean_object* v_write_3520_; lean_object* v_read_3521_; lean_object* v_nextId_3522_; uint8_t v_closed_3523_; lean_object* v_pos_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3536_; 
v___x_3514_ = lean_st_ref_take(v_a_3503_);
v_producers_3515_ = lean_ctor_get(v___x_3514_, 0);
v_waiters_3516_ = lean_ctor_get(v___x_3514_, 1);
v_capacity_3517_ = lean_ctor_get(v___x_3514_, 2);
v_size_3518_ = lean_ctor_get(v___x_3514_, 3);
v_buffer_3519_ = lean_ctor_get(v___x_3514_, 4);
v_write_3520_ = lean_ctor_get(v___x_3514_, 5);
v_read_3521_ = lean_ctor_get(v___x_3514_, 6);
v_nextId_3522_ = lean_ctor_get(v___x_3514_, 8);
v_closed_3523_ = lean_ctor_get_uint8(v___x_3514_, sizeof(void*)*10);
v_pos_3524_ = lean_ctor_get(v___x_3514_, 9);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; 
v_unused_3537_ = lean_ctor_get(v___x_3514_, 7);
lean_dec(v_unused_3537_);
v___x_3526_ = v___x_3514_;
v_isShared_3527_ = v_isSharedCheck_3536_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_pos_3524_);
lean_inc(v_nextId_3522_);
lean_inc(v_read_3521_);
lean_inc(v_write_3520_);
lean_inc(v_buffer_3519_);
lean_inc(v_size_3518_);
lean_inc(v_capacity_3517_);
lean_inc(v_waiters_3516_);
lean_inc(v_producers_3515_);
lean_dec(v___x_3514_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3536_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3528_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3502_, v_receivers_3506_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 7, v___x_3528_);
v___x_3530_ = v___x_3526_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_producers_3515_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_waiters_3516_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v_capacity_3517_);
lean_ctor_set(v_reuseFailAlloc_3535_, 3, v_size_3518_);
lean_ctor_set(v_reuseFailAlloc_3535_, 4, v_buffer_3519_);
lean_ctor_set(v_reuseFailAlloc_3535_, 5, v_write_3520_);
lean_ctor_set(v_reuseFailAlloc_3535_, 6, v_read_3521_);
lean_ctor_set(v_reuseFailAlloc_3535_, 7, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3535_, 8, v_nextId_3522_);
lean_ctor_set(v_reuseFailAlloc_3535_, 9, v_pos_3524_);
lean_ctor_set_uint8(v_reuseFailAlloc_3535_, sizeof(void*)*10, v_closed_3523_);
v___x_3530_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3531_ = lean_st_ref_put(v_a_3503_, v___x_3530_);
if (v_isShared_3513_ == 0)
{
v___x_3533_ = v___x_3512_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3510_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v___x_3538_; lean_object* v___x_3540_; 
lean_dec(v_a_3510_);
lean_dec(v_receivers_3506_);
lean_dec(v_receiverId_3502_);
v___x_3538_ = lean_box(0);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3538_);
v___x_3540_ = v___x_3512_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
lean_dec(v_receivers_3506_);
lean_dec(v_receiverId_3502_);
return v___x_3509_;
}
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v___x_3507_);
lean_dec(v_receivers_3506_);
lean_dec(v_receiverId_3502_);
v___x_3543_ = lean_box(0);
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3545_, lean_object* v_a_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3545_, v_a_3546_);
lean_dec(v_a_3546_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3549_, lean_object* v_w_3550_, lean_object* v_lose_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_finished_3554_; lean_object* v_promise_3555_; lean_object* v___x_3556_; uint8_t v___y_3558_; uint8_t v___x_3582_; 
v_finished_3554_ = lean_ctor_get(v_w_3550_, 0);
v_promise_3555_ = lean_ctor_get(v_w_3550_, 1);
v___x_3556_ = lean_st_ref_take(v_finished_3554_);
v___x_3582_ = lean_unbox(v___x_3556_);
lean_dec(v___x_3556_);
if (v___x_3582_ == 0)
{
uint8_t v___x_3583_; 
v___x_3583_ = 1;
v___y_3558_ = v___x_3583_;
goto v___jp_3557_;
}
else
{
uint8_t v___x_3584_; 
v___x_3584_ = 0;
v___y_3558_ = v___x_3584_;
goto v___jp_3557_;
}
v___jp_3557_:
{
uint8_t v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3559_ = 1;
v___x_3560_ = lean_box(v___x_3559_);
v___x_3561_ = lean_st_ref_put(v_finished_3554_, v___x_3560_);
if (v___y_3558_ == 0)
{
lean_object* v___x_3562_; 
lean_dec(v___x_3549_);
lean_inc(v___y_3552_);
v___x_3562_ = lean_apply_2(v_lose_3551_, v___y_3552_, lean_box(0));
return v___x_3562_;
}
else
{
lean_object* v___x_3563_; 
lean_dec_ref(v_lose_3551_);
v___x_3563_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3549_, v___y_3552_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3573_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3566_ = v___x_3563_;
v_isShared_3567_ = v_isSharedCheck_3573_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3573_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_a_3564_);
v___x_3569_ = lean_io_promise_resolve(v___x_3568_, v_promise_3555_);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3569_);
v___x_3571_ = v___x_3566_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
v_a_3574_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3563_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3563_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3585_, lean_object* v_w_3586_, lean_object* v_lose_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3585_, v_w_3586_, v_lose_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v_w_3586_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3591_, lean_object* v___x_3592_, lean_object* v_w_3593_, lean_object* v_lose_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; 
v___x_3597_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3592_, v_w_3593_, v_lose_3594_, v___y_3595_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3598_, lean_object* v___x_3599_, lean_object* v_w_3600_, lean_object* v_lose_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3598_, v___x_3599_, v_w_3600_, v_lose_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v_w_3600_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3605_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3608_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3611_, lean_object* v___f_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; uint8_t v_closed_3616_; 
v___x_3615_ = lean_st_ref_get(v___y_3613_);
v_closed_3616_ = lean_ctor_get_uint8(v___x_3615_, sizeof(void*)*10);
if (v_closed_3616_ == 0)
{
lean_object* v_capacity_3617_; lean_object* v_size_3618_; lean_object* v_receivers_3619_; lean_object* v___x_3620_; 
v_capacity_3617_ = lean_ctor_get(v___x_3615_, 2);
lean_inc(v_capacity_3617_);
v_size_3618_ = lean_ctor_get(v___x_3615_, 3);
lean_inc(v_size_3618_);
v_receivers_3619_ = lean_ctor_get(v___x_3615_, 7);
lean_inc(v_receivers_3619_);
lean_dec(v___x_3615_);
v___x_3620_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3619_, v_id_3611_);
lean_dec(v_receivers_3619_);
if (lean_obj_tag(v___x_3620_) == 1)
{
lean_object* v_val_3621_; lean_object* v___x_3622_; uint8_t v___x_3623_; 
v_val_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_val_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = lean_unsigned_to_nat(0u);
v___x_3623_ = lean_nat_dec_eq(v_size_3618_, v___x_3622_);
lean_dec(v_size_3618_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = lean_nat_mod(v_val_3621_, v_capacity_3617_);
lean_dec(v_capacity_3617_);
v___x_3625_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3624_, v___y_3613_);
lean_dec(v___x_3624_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3627_; lean_object* v_pos_3628_; uint8_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
v___x_3627_ = lean_st_ref_get(v_a_3626_);
lean_dec(v_a_3626_);
v_pos_3628_ = lean_ctor_get(v___x_3627_, 1);
lean_inc(v_pos_3628_);
lean_dec(v___x_3627_);
v___x_3629_ = lean_nat_dec_eq(v_pos_3628_, v_val_3621_);
lean_dec(v_val_3621_);
lean_dec(v_pos_3628_);
v___x_3630_ = lean_box(v___x_3629_);
lean_inc(v___y_3613_);
v___x_3631_ = lean_apply_3(v___f_3612_, v___x_3630_, v___y_3613_, lean_box(0));
return v___x_3631_;
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_val_3621_);
lean_dec_ref(v___f_3612_);
v_a_3632_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3625_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3625_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
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
lean_object* v___x_3640_; lean_object* v___x_3641_; 
lean_dec(v_val_3621_);
lean_dec(v_capacity_3617_);
v___x_3640_ = lean_box(v_closed_3616_);
lean_inc(v___y_3613_);
v___x_3641_ = lean_apply_3(v___f_3612_, v___x_3640_, v___y_3613_, lean_box(0));
return v___x_3641_;
}
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
lean_dec(v___x_3620_);
lean_dec(v_size_3618_);
lean_dec(v_capacity_3617_);
v___x_3642_ = lean_box(v_closed_3616_);
lean_inc(v___y_3613_);
v___x_3643_ = lean_apply_3(v___f_3612_, v___x_3642_, v___y_3613_, lean_box(0));
return v___x_3643_;
}
}
else
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
lean_dec(v___x_3615_);
v___x_3644_ = lean_box(v_closed_3616_);
lean_inc(v___y_3613_);
v___x_3645_ = lean_apply_3(v___f_3612_, v___x_3644_, v___y_3613_, lean_box(0));
return v___x_3645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3646_, lean_object* v___f_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3646_, v___f_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec(v_id_3646_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v_producers_3655_; lean_object* v_waiters_3656_; lean_object* v_capacity_3657_; lean_object* v_size_3658_; lean_object* v_buffer_3659_; lean_object* v_write_3660_; lean_object* v_read_3661_; lean_object* v_receivers_3662_; lean_object* v_nextId_3663_; uint8_t v_closed_3664_; lean_object* v_pos_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3688_; 
v___x_3654_ = lean_st_ref_get(v___y_3652_);
v_producers_3655_ = lean_ctor_get(v___x_3654_, 0);
v_waiters_3656_ = lean_ctor_get(v___x_3654_, 1);
v_capacity_3657_ = lean_ctor_get(v___x_3654_, 2);
v_size_3658_ = lean_ctor_get(v___x_3654_, 3);
v_buffer_3659_ = lean_ctor_get(v___x_3654_, 4);
v_write_3660_ = lean_ctor_get(v___x_3654_, 5);
v_read_3661_ = lean_ctor_get(v___x_3654_, 6);
v_receivers_3662_ = lean_ctor_get(v___x_3654_, 7);
v_nextId_3663_ = lean_ctor_get(v___x_3654_, 8);
v_closed_3664_ = lean_ctor_get_uint8(v___x_3654_, sizeof(void*)*10);
v_pos_3665_ = lean_ctor_get(v___x_3654_, 9);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3667_ = v___x_3654_;
v_isShared_3668_ = v_isSharedCheck_3688_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_pos_3665_);
lean_inc(v_nextId_3663_);
lean_inc(v_receivers_3662_);
lean_inc(v_read_3661_);
lean_inc(v_write_3660_);
lean_inc(v_buffer_3659_);
lean_inc(v_size_3658_);
lean_inc(v_capacity_3657_);
lean_inc(v_waiters_3656_);
lean_inc(v_producers_3655_);
lean_dec(v___x_3654_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3688_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; 
v___x_3669_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3656_);
if (lean_obj_tag(v___x_3669_) == 1)
{
lean_object* v_val_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3685_; 
v_val_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3685_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_val_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3685_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v_fst_3674_; lean_object* v_snd_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
v_fst_3674_ = lean_ctor_get(v_val_3670_, 0);
lean_inc(v_fst_3674_);
v_snd_3675_ = lean_ctor_get(v_val_3670_, 1);
lean_inc(v_snd_3675_);
lean_dec(v_val_3670_);
v___x_3676_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3674_, v_____do__lift_3651_);
lean_dec(v_fst_3674_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 1, v_snd_3675_);
v___x_3678_ = v___x_3667_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_producers_3655_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_snd_3675_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_capacity_3657_);
lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_size_3658_);
lean_ctor_set(v_reuseFailAlloc_3684_, 4, v_buffer_3659_);
lean_ctor_set(v_reuseFailAlloc_3684_, 5, v_write_3660_);
lean_ctor_set(v_reuseFailAlloc_3684_, 6, v_read_3661_);
lean_ctor_set(v_reuseFailAlloc_3684_, 7, v_receivers_3662_);
lean_ctor_set(v_reuseFailAlloc_3684_, 8, v_nextId_3663_);
lean_ctor_set(v_reuseFailAlloc_3684_, 9, v_pos_3665_);
lean_ctor_set_uint8(v_reuseFailAlloc_3684_, sizeof(void*)*10, v_closed_3664_);
v___x_3678_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3679_ = lean_box(0);
v___x_3680_ = lean_st_ref_swap(v___y_3652_, v___x_3678_);
lean_dec(v___x_3680_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set_tag(v___x_3672_, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3679_);
v___x_3682_ = v___x_3672_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3679_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_dec(v___x_3669_);
lean_del_object(v___x_3667_);
lean_dec(v_pos_3665_);
lean_dec(v_nextId_3663_);
lean_dec(v_receivers_3662_);
lean_dec(v_read_3661_);
lean_dec(v_write_3660_);
lean_dec_ref(v_buffer_3659_);
lean_dec(v_size_3658_);
lean_dec(v_capacity_3657_);
lean_dec_ref(v_producers_3655_);
v___x_3686_ = lean_box(0);
v___x_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
return v___x_3687_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
uint8_t v_____do__lift_3763__boxed_3692_; lean_object* v_res_3693_; 
v_____do__lift_3763__boxed_3692_ = lean_unbox(v_____do__lift_3689_);
v_res_3693_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3763__boxed_3692_, v___y_3690_);
lean_dec(v___y_3690_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3694_, lean_object* v___f_3695_, lean_object* v_id_3696_, uint8_t v_____do__lift_3697_, lean_object* v___y_3698_){
_start:
{
if (v_____do__lift_3697_ == 0)
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v_producers_3702_; lean_object* v_waiters_3703_; lean_object* v_capacity_3704_; lean_object* v_size_3705_; lean_object* v_buffer_3706_; lean_object* v_write_3707_; lean_object* v_read_3708_; lean_object* v_receivers_3709_; lean_object* v_nextId_3710_; uint8_t v_closed_3711_; lean_object* v_pos_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v_id_3696_);
v___x_3700_ = lean_io_promise_new();
v___x_3701_ = lean_st_ref_take(v___y_3698_);
v_producers_3702_ = lean_ctor_get(v___x_3701_, 0);
v_waiters_3703_ = lean_ctor_get(v___x_3701_, 1);
v_capacity_3704_ = lean_ctor_get(v___x_3701_, 2);
v_size_3705_ = lean_ctor_get(v___x_3701_, 3);
v_buffer_3706_ = lean_ctor_get(v___x_3701_, 4);
v_write_3707_ = lean_ctor_get(v___x_3701_, 5);
v_read_3708_ = lean_ctor_get(v___x_3701_, 6);
v_receivers_3709_ = lean_ctor_get(v___x_3701_, 7);
v_nextId_3710_ = lean_ctor_get(v___x_3701_, 8);
v_closed_3711_ = lean_ctor_get_uint8(v___x_3701_, sizeof(void*)*10);
v_pos_3712_ = lean_ctor_get(v___x_3701_, 9);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3714_ = v___x_3701_;
v_isShared_3715_ = v_isSharedCheck_3726_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_pos_3712_);
lean_inc(v_nextId_3710_);
lean_inc(v_receivers_3709_);
lean_inc(v_read_3708_);
lean_inc(v_write_3707_);
lean_inc(v_buffer_3706_);
lean_inc(v_size_3705_);
lean_inc(v_capacity_3704_);
lean_inc(v_waiters_3703_);
lean_inc(v_producers_3702_);
lean_dec(v___x_3701_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3726_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v_waiter_3694_);
lean_inc(v___x_3700_);
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3700_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = l_Std_Queue_enqueue___redArg(v___x_3717_, v_waiters_3703_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 1, v___x_3718_);
v___x_3720_ = v___x_3714_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_producers_3702_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_capacity_3704_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_size_3705_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_buffer_3706_);
lean_ctor_set(v_reuseFailAlloc_3725_, 5, v_write_3707_);
lean_ctor_set(v_reuseFailAlloc_3725_, 6, v_read_3708_);
lean_ctor_set(v_reuseFailAlloc_3725_, 7, v_receivers_3709_);
lean_ctor_set(v_reuseFailAlloc_3725_, 8, v_nextId_3710_);
lean_ctor_set(v_reuseFailAlloc_3725_, 9, v_pos_3712_);
lean_ctor_set_uint8(v_reuseFailAlloc_3725_, sizeof(void*)*10, v_closed_3711_);
v___x_3720_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3721_ = lean_st_ref_put(v___y_3698_, v___x_3720_);
v___x_3722_ = lean_io_promise_result_opt(v___x_3700_);
lean_dec(v___x_3700_);
v___x_3723_ = lean_unsigned_to_nat(0u);
v___x_3724_ = l_EIO_chainTask___redArg(v___x_3722_, v___f_3695_, v___x_3723_, v_____do__lift_3697_);
return v___x_3724_;
}
}
}
else
{
lean_object* v___x_3727_; lean_object* v_lose_3728_; lean_object* v___x_3729_; 
lean_dec_ref(v___f_3695_);
v___x_3727_ = lean_box(v_____do__lift_3697_);
v_lose_3728_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3728_, 0, v___x_3727_);
v___x_3729_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3696_, v_waiter_3694_, v_lose_3728_, v___y_3698_);
lean_dec_ref(v_waiter_3694_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3730_, lean_object* v___f_3731_, lean_object* v_id_3732_, lean_object* v_____do__lift_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
uint8_t v_____do__lift_3821__boxed_3736_; lean_object* v_res_3737_; 
v_____do__lift_3821__boxed_3736_ = lean_unbox(v_____do__lift_3733_);
v_res_3737_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3730_, v___f_3731_, v_id_3732_, v_____do__lift_3821__boxed_3736_, v___y_3734_);
lean_dec(v___y_3734_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3740_, lean_object* v_ch_3741_, lean_object* v_res_x3f_3742_){
_start:
{
if (lean_obj_tag(v_res_x3f_3742_) == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
lean_dec_ref(v_ch_3741_);
lean_dec_ref(v_waiter_3740_);
v___x_3744_ = lean_box(0);
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
else
{
lean_object* v_val_3746_; uint8_t v___x_3747_; 
v_val_3746_ = lean_ctor_get(v_res_x3f_3742_, 0);
v___x_3747_ = lean_unbox(v_val_3746_);
if (v___x_3747_ == 0)
{
lean_object* v___f_3748_; lean_object* v___x_3749_; 
lean_dec_ref(v_ch_3741_);
v___f_3748_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3749_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3740_, v___f_3748_);
lean_dec_ref(v_waiter_3740_);
return v___x_3749_;
}
else
{
lean_object* v___x_3750_; 
v___x_3750_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3741_, v_waiter_3740_);
return v___x_3750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3751_, lean_object* v_ch_3752_, lean_object* v_res_x3f_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3751_, v_ch_3752_, v_res_x3f_3753_);
lean_dec(v_res_x3f_3753_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3756_, lean_object* v_waiter_3757_){
_start:
{
lean_object* v_state_3759_; lean_object* v_id_3760_; lean_object* v___f_3761_; lean_object* v___f_3762_; lean_object* v___f_3763_; lean_object* v___x_3764_; 
v_state_3759_ = lean_ctor_get(v_ch_3756_, 0);
lean_inc_ref(v_state_3759_);
v_id_3760_ = lean_ctor_get(v_ch_3756_, 1);
lean_inc_n(v_id_3760_, 2);
lean_inc_ref(v_waiter_3757_);
v___f_3761_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3761_, 0, v_waiter_3757_);
lean_closure_set(v___f_3761_, 1, v_ch_3756_);
v___f_3762_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3762_, 0, v_waiter_3757_);
lean_closure_set(v___f_3762_, 1, v___f_3761_);
lean_closure_set(v___f_3762_, 2, v_id_3760_);
v___f_3763_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3763_, 0, v_id_3760_);
lean_closure_set(v___f_3763_, 1, v___f_3762_);
v___x_3764_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3759_, v___f_3763_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3765_, lean_object* v_waiter_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3765_, v_waiter_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3769_, lean_object* v_ch_3770_, lean_object* v_waiter_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3770_, v_waiter_3771_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3774_, lean_object* v_ch_3775_, lean_object* v_waiter_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3774_, v_ch_3775_, v_waiter_3776_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3779_, lean_object* v_receiverId_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v___x_3783_; 
v___x_3783_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3780_, v_a_3781_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3784_, lean_object* v_receiverId_3785_, lean_object* v_a_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3784_, v_receiverId_3785_, v_a_3786_);
lean_dec(v_a_3786_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3789_, lean_object* v_x_3790_){
_start:
{
if (lean_obj_tag(v_x_3790_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3800_; 
v_a_3792_ = lean_ctor_get(v_x_3790_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_x_3790_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3794_ = v_x_3790_;
v_isShared_3795_ = v_isSharedCheck_3800_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v_x_3790_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3800_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3798_; 
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
return v___x_3798_;
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3813_; 
v_a_3801_ = lean_ctor_get(v_x_3790_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_x_3790_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3803_ = v_x_3790_;
v_isShared_3804_ = v_isSharedCheck_3813_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v_x_3790_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3813_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v_capacity_3805_; lean_object* v_buffer_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3810_; 
v_capacity_3805_ = lean_ctor_get(v_a_3801_, 2);
lean_inc(v_capacity_3805_);
v_buffer_3806_ = lean_ctor_get(v_a_3801_, 4);
lean_inc_ref(v_buffer_3806_);
lean_dec(v_a_3801_);
v___x_3807_ = lean_nat_mod(v_place_3789_, v_capacity_3805_);
lean_dec(v_capacity_3805_);
v___x_3808_ = lean_array_fget(v_buffer_3806_, v___x_3807_);
lean_dec(v___x_3807_);
lean_dec_ref(v_buffer_3806_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 0, v___x_3808_);
v___x_3810_ = v___x_3803_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3811_; 
v___x_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
return v___x_3811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3814_, lean_object* v_x_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3814_, v_x_3815_);
lean_dec(v_place_3814_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v___f_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___f_3821_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3821_, 0, v_place_3818_);
v___x_3822_ = lean_unsigned_to_nat(0u);
v___x_3823_ = 0;
v___x_3824_ = lean_st_ref_get(v_a_3819_);
v___x_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
v___x_3827_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3822_, v___x_3823_, v___x_3826_, v___f_3821_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3828_, lean_object* v_a_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3828_, v_a_3829_);
lean_dec(v_a_3829_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3832_, lean_object* v_place_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3833_, v_a_3834_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3837_, lean_object* v_place_3838_, lean_object* v_a_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3837_, v_place_3838_, v_a_3839_);
lean_dec(v_a_3839_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v___y_3842_){
_start:
{
if (lean_obj_tag(v___y_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
v_a_3843_ = lean_ctor_get(v___y_3842_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___y_3842_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___y_3842_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___y_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3859_; 
v_a_3851_ = lean_ctor_get(v___y_3842_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___y_3842_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3853_ = v___y_3842_;
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___y_3842_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v_fst_3855_; lean_object* v___x_3857_; 
v_fst_3855_ = lean_ctor_get(v_a_3851_, 0);
lean_inc(v_fst_3855_);
lean_dec(v_a_3851_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v_fst_3855_);
v___x_3857_ = v___x_3853_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_fst_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_mutex_3860_, lean_object* v_x_3861_){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_io_basemutex_unlock(v_mutex_3860_);
v___x_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
v___x_3865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_3866_, lean_object* v_x_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_mutex_3866_, v_x_3867_);
lean_dec(v_x_3867_);
lean_dec(v_mutex_3866_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_k_3870_, lean_object* v_ref_3871_, lean_object* v_x_3872_){
_start:
{
if (lean_obj_tag(v_x_3872_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3882_; 
lean_dec(v_ref_3871_);
lean_dec_ref(v_k_3870_);
v_a_3874_ = lean_ctor_get(v_x_3872_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v_x_3872_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3876_ = v_x_3872_;
v_isShared_3877_ = v_isSharedCheck_3882_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v_x_3872_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3882_;
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
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
lean_object* v___x_3880_; 
v___x_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
return v___x_3880_;
}
}
}
else
{
lean_object* v___x_3883_; 
lean_dec_ref_known(v_x_3872_, 1);
v___x_3883_ = lean_apply_2(v_k_3870_, v_ref_3871_, lean_box(0));
return v___x_3883_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_k_3884_, lean_object* v_ref_3885_, lean_object* v_x_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_k_3884_, v_ref_3885_, v_x_3886_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v_mutex_3889_, lean_object* v___f_3890_){
_start:
{
lean_object* v___x_3892_; uint8_t v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = 0;
v___x_3894_ = lean_io_basemutex_lock(v_mutex_3889_);
v___x_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
v___x_3896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
v___x_3897_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3892_, v___x_3893_, v___x_3896_, v___f_3890_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_3898_, lean_object* v___f_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(v_mutex_3898_, v___f_3899_);
lean_dec(v_mutex_3898_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_3903_, lean_object* v_k_3904_){
_start:
{
lean_object* v_ref_3906_; lean_object* v_mutex_3907_; lean_object* v___f_3908_; lean_object* v___f_3909_; lean_object* v___f_3910_; lean_object* v___f_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; lean_object* v___x_3914_; lean_object* v___y_3916_; 
v_ref_3906_ = lean_ctor_get(v_mutex_3903_, 0);
lean_inc(v_ref_3906_);
v_mutex_3907_ = lean_ctor_get(v_mutex_3903_, 1);
lean_inc_n(v_mutex_3907_, 2);
lean_dec_ref(v_mutex_3903_);
v___f_3908_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___f_3909_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3909_, 0, v_mutex_3907_);
v___f_3910_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_3910_, 0, v_k_3904_);
lean_closure_set(v___f_3910_, 1, v_ref_3906_);
v___f_3911_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_3911_, 0, v_mutex_3907_);
lean_closure_set(v___f_3911_, 1, v___f_3910_);
v___x_3912_ = lean_unsigned_to_nat(0u);
v___x_3913_ = 0;
v___x_3914_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_3911_, v___f_3909_, v___x_3912_, v___x_3913_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3918_; 
v_a_3918_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3914_, 1);
if (lean_obj_tag(v_a_3918_) == 0)
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
v_a_3919_ = lean_ctor_get(v_a_3918_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_a_3918_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v_a_3918_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v_a_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
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
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
v___y_3916_ = v___x_3924_;
goto v___jp_3915_;
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3935_; 
v_a_3927_ = lean_ctor_get(v_a_3918_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_a_3918_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3929_ = v_a_3918_;
v_isShared_3930_ = v_isSharedCheck_3935_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v_a_3918_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3935_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v_fst_3931_; lean_object* v___x_3933_; 
v_fst_3931_ = lean_ctor_get(v_a_3927_, 0);
lean_inc(v_fst_3931_);
lean_dec(v_a_3927_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 0, v_fst_3931_);
v___x_3933_ = v___x_3929_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_fst_3931_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
v___y_3916_ = v___x_3933_;
goto v___jp_3915_;
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3944_; 
v_a_3936_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3938_ = v___x_3914_;
v_isShared_3939_ = v_isSharedCheck_3944_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3914_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3944_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3940_ = lean_task_map(v___f_3908_, v_a_3936_, v___x_3912_, v___x_3913_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3940_);
v___x_3942_ = v___x_3938_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
v___jp_3915_:
{
lean_object* v___x_3917_; 
v___x_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___y_3916_);
return v___x_3917_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_3945_, lean_object* v_k_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3945_, v_k_3946_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_3949_, lean_object* v_00_u03b2_3950_, lean_object* v_mutex_3951_, lean_object* v_k_3952_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_3951_, v_k_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_3955_, lean_object* v_00_u03b2_3956_, lean_object* v_mutex_3957_, lean_object* v_k_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_3955_, v_00_u03b2_3956_, v_mutex_3957_, v_k_3958_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_3965_, lean_object* v_capacity_3966_, lean_object* v_size_3967_, lean_object* v_buffer_3968_, lean_object* v_write_3969_, lean_object* v_read_3970_, lean_object* v_receivers_3971_, lean_object* v_nextId_3972_, uint8_t v_closed_3973_, lean_object* v_pos_3974_, lean_object* v___y_3975_, lean_object* v_x_3976_){
_start:
{
if (lean_obj_tag(v_x_3976_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3986_; 
lean_dec(v_pos_3974_);
lean_dec(v_nextId_3972_);
lean_dec(v_receivers_3971_);
lean_dec(v_read_3970_);
lean_dec(v_write_3969_);
lean_dec_ref(v_buffer_3968_);
lean_dec(v_size_3967_);
lean_dec(v_capacity_3966_);
lean_dec_ref(v_producers_3965_);
v_a_3978_ = lean_ctor_get(v_x_3976_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_x_3976_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3980_ = v_x_3976_;
v_isShared_3981_ = v_isSharedCheck_3986_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v_x_3976_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3986_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; 
v___x_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
return v___x_3984_;
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_a_3987_ = lean_ctor_get(v_x_3976_, 0);
lean_inc(v_a_3987_);
lean_dec_ref_known(v_x_3976_, 1);
v___x_3988_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3988_, 0, v_producers_3965_);
lean_ctor_set(v___x_3988_, 1, v_a_3987_);
lean_ctor_set(v___x_3988_, 2, v_capacity_3966_);
lean_ctor_set(v___x_3988_, 3, v_size_3967_);
lean_ctor_set(v___x_3988_, 4, v_buffer_3968_);
lean_ctor_set(v___x_3988_, 5, v_write_3969_);
lean_ctor_set(v___x_3988_, 6, v_read_3970_);
lean_ctor_set(v___x_3988_, 7, v_receivers_3971_);
lean_ctor_set(v___x_3988_, 8, v_nextId_3972_);
lean_ctor_set(v___x_3988_, 9, v_pos_3974_);
lean_ctor_set_uint8(v___x_3988_, sizeof(void*)*10, v_closed_3973_);
v___x_3989_ = lean_st_ref_swap(v___y_3975_, v___x_3988_);
lean_dec(v___x_3989_);
v___x_3990_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_3990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_3991_, lean_object* v_capacity_3992_, lean_object* v_size_3993_, lean_object* v_buffer_3994_, lean_object* v_write_3995_, lean_object* v_read_3996_, lean_object* v_receivers_3997_, lean_object* v_nextId_3998_, lean_object* v_closed_3999_, lean_object* v_pos_4000_, lean_object* v___y_4001_, lean_object* v_x_4002_, lean_object* v___y_4003_){
_start:
{
uint8_t v_closed_boxed_4004_; lean_object* v_res_4005_; 
v_closed_boxed_4004_ = lean_unbox(v_closed_3999_);
v_res_4005_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_3991_, v_capacity_3992_, v_size_3993_, v_buffer_3994_, v_write_3995_, v_read_3996_, v_receivers_3997_, v_nextId_3998_, v_closed_boxed_4004_, v_pos_4000_, v___y_4001_, v_x_4002_);
lean_dec(v___y_4001_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_4006_){
_start:
{
if (lean_obj_tag(v_x_4006_) == 0)
{
lean_object* v___x_4008_; 
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v_x_4006_);
return v___x_4008_;
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4018_; 
v_a_4009_ = lean_ctor_get(v_x_4006_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v_x_4006_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4011_ = v_x_4006_;
v_isShared_4012_ = v_isSharedCheck_4018_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v_x_4006_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4018_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4013_ = l_List_reverse___redArg(v_a_4009_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4013_);
v___x_4015_ = v___x_4011_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4013_);
v___x_4015_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_4019_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_4022_, lean_object* v___x_4023_, lean_object* v_x_4024_){
_start:
{
if (lean_obj_tag(v_x_4024_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4034_; 
lean_dec(v___x_4023_);
lean_dec(v_a_4022_);
v_a_4026_ = lean_ctor_get(v_x_4024_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_x_4024_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4028_ = v_x_4024_;
v_isShared_4029_ = v_isSharedCheck_4034_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v_x_4024_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4034_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4032_; 
v___x_4032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4051_; 
v_a_4035_ = lean_ctor_get(v_x_4024_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_x_4024_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4037_ = v_x_4024_;
v_isShared_4038_ = v_isSharedCheck_4051_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v_x_4024_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4051_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
uint8_t v___x_4039_; 
v___x_4039_ = l_List_isEmpty___redArg(v_a_4022_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4042_; 
lean_dec(v___x_4023_);
v___x_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4040_, 0, v_a_4035_);
lean_ctor_set(v___x_4040_, 1, v_a_4022_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v___x_4040_);
v___x_4042_ = v___x_4037_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4043_; 
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
return v___x_4043_;
}
}
else
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
lean_dec(v_a_4022_);
v___x_4045_ = l_List_reverse___redArg(v_a_4035_);
v___x_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4023_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v___x_4046_);
v___x_4048_ = v___x_4037_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4046_);
v___x_4048_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; 
v___x_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_4052_, lean_object* v___x_4053_, lean_object* v_x_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_4052_, v___x_4053_, v_x_4054_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_4057_){
_start:
{
uint8_t v___y_4060_; 
if (lean_obj_tag(v_x_4057_) == 0)
{
lean_object* v___x_4064_; 
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v_x_4057_);
return v___x_4064_;
}
else
{
lean_object* v_a_4065_; uint8_t v___x_4066_; 
v_a_4065_ = lean_ctor_get(v_x_4057_, 0);
lean_inc(v_a_4065_);
lean_dec_ref_known(v_x_4057_, 1);
v___x_4066_ = lean_unbox(v_a_4065_);
lean_dec(v_a_4065_);
if (v___x_4066_ == 0)
{
uint8_t v___x_4067_; 
v___x_4067_ = 1;
v___y_4060_ = v___x_4067_;
goto v___jp_4059_;
}
else
{
uint8_t v___x_4068_; 
v___x_4068_ = 0;
v___y_4060_ = v___x_4068_;
goto v___jp_4059_;
}
}
v___jp_4059_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4061_ = lean_box(v___y_4060_);
v___x_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
return v___x_4063_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4069_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_4072_, lean_object* v_x_4073_, lean_object* v_head_4074_, lean_object* v_x_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4072_, v_x_4073_, v_head_4074_, v_x_4075_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_4084_, lean_object* v_x_4085_){
_start:
{
if (lean_obj_tag(v_x_4084_) == 0)
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4087_, 0, v_x_4085_);
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
else
{
lean_object* v_head_4089_; lean_object* v_tail_4090_; lean_object* v_waiter_4091_; lean_object* v___f_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v_head_4089_ = lean_ctor_get(v_x_4084_, 0);
lean_inc(v_head_4089_);
v_tail_4090_ = lean_ctor_get(v_x_4084_, 1);
lean_inc(v_tail_4090_);
lean_dec_ref_known(v_x_4084_, 2);
v_waiter_4091_ = lean_ctor_get(v_head_4089_, 1);
lean_inc(v_waiter_4091_);
v___f_4092_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4092_, 0, v_tail_4090_);
lean_closure_set(v___f_4092_, 1, v_x_4085_);
lean_closure_set(v___f_4092_, 2, v_head_4089_);
v___x_4093_ = lean_unsigned_to_nat(0u);
v___x_4094_ = 0;
if (lean_obj_tag(v_waiter_4091_) == 0)
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v___x_4096_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4093_, v___x_4094_, v___x_4095_, v___f_4092_);
return v___x_4096_;
}
else
{
lean_object* v_val_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4110_; 
v_val_4097_ = lean_ctor_get(v_waiter_4091_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v_waiter_4091_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4099_ = v_waiter_4091_;
v_isShared_4100_ = v_isSharedCheck_4110_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_val_4097_);
lean_dec(v_waiter_4091_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4110_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v_finished_4101_; lean_object* v___f_4102_; lean_object* v___x_4103_; lean_object* v___x_4105_; 
v_finished_4101_ = lean_ctor_get(v_val_4097_, 0);
lean_inc(v_finished_4101_);
lean_dec(v_val_4097_);
v___f_4102_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
v___x_4103_ = lean_st_ref_get(v_finished_4101_);
lean_dec(v_finished_4101_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4103_);
v___x_4105_ = v___x_4099_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4103_);
v___x_4105_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
v___x_4107_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4093_, v___x_4094_, v___x_4106_, v___f_4102_);
v___x_4108_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4093_, v___x_4094_, v___x_4107_, v___f_4092_);
return v___x_4108_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_4111_, lean_object* v_x_4112_, lean_object* v_head_4113_, lean_object* v_x_4114_){
_start:
{
if (lean_obj_tag(v_x_4114_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v_head_4113_);
lean_dec(v_x_4112_);
lean_dec(v_tail_4111_);
v_a_4116_ = lean_ctor_get(v_x_4114_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_x_4114_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4118_ = v_x_4114_;
v_isShared_4119_ = v_isSharedCheck_4124_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v_x_4114_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4124_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4116_);
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
}
else
{
lean_object* v_a_4125_; uint8_t v___x_4126_; 
v_a_4125_ = lean_ctor_get(v_x_4114_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v_x_4114_, 1);
v___x_4126_ = lean_unbox(v_a_4125_);
lean_dec(v_a_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; 
lean_dec_ref(v_head_4113_);
v___x_4127_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4111_, v_x_4112_);
return v___x_4127_;
}
else
{
lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4128_, 0, v_head_4113_);
lean_ctor_set(v___x_4128_, 1, v_x_4112_);
v___x_4129_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4111_, v___x_4128_);
return v___x_4129_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_4130_, lean_object* v_x_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4130_, v_x_4131_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v___x_4134_, lean_object* v_eList_4135_, lean_object* v___f_4136_, lean_object* v_x_4137_){
_start:
{
if (lean_obj_tag(v_x_4137_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4147_; 
lean_dec_ref(v___f_4136_);
lean_dec(v_eList_4135_);
lean_dec(v___x_4134_);
v_a_4139_ = lean_ctor_get(v_x_4137_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v_x_4137_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4141_ = v_x_4137_;
v_isShared_4142_ = v_isSharedCheck_4147_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v_x_4137_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4147_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
lean_object* v___x_4145_; 
v___x_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
return v___x_4145_;
}
}
}
else
{
lean_object* v_a_4148_; lean_object* v___f_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v_a_4148_ = lean_ctor_get(v_x_4137_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v_x_4137_, 1);
lean_inc(v___x_4134_);
v___f_4149_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4149_, 0, v_a_4148_);
lean_closure_set(v___f_4149_, 1, v___x_4134_);
v___x_4150_ = lean_unsigned_to_nat(0u);
v___x_4151_ = 0;
v___x_4152_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4135_, v___x_4134_);
v___x_4153_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4150_, v___x_4151_, v___x_4152_, v___f_4136_);
v___x_4154_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4150_, v___x_4151_, v___x_4153_, v___f_4149_);
return v___x_4154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v___x_4155_, lean_object* v_eList_4156_, lean_object* v___f_4157_, lean_object* v_x_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v___x_4155_, v_eList_4156_, v___f_4157_, v_x_4158_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_eList_4165_; lean_object* v_dList_4166_; lean_object* v___f_4167_; lean_object* v___x_4168_; lean_object* v___f_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v_eList_4165_ = lean_ctor_get(v_q_4162_, 0);
lean_inc(v_eList_4165_);
v_dList_4166_ = lean_ctor_get(v_q_4162_, 1);
lean_inc(v_dList_4166_);
lean_dec_ref(v_q_4162_);
v___f_4167_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4168_ = lean_box(0);
v___f_4169_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4169_, 0, v___x_4168_);
lean_closure_set(v___f_4169_, 1, v_eList_4165_);
lean_closure_set(v___f_4169_, 2, v___f_4167_);
v___x_4170_ = lean_unsigned_to_nat(0u);
v___x_4171_ = 0;
v___x_4172_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4166_, v___x_4168_);
v___x_4173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4170_, v___x_4171_, v___x_4172_, v___f_4167_);
v___x_4174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4170_, v___x_4171_, v___x_4173_, v___f_4169_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4175_, v___y_4176_);
lean_dec(v___y_4176_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4179_, lean_object* v_x_4180_){
_start:
{
if (lean_obj_tag(v_x_4180_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4190_; 
v_a_4182_ = lean_ctor_get(v_x_4180_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_x_4180_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4184_ = v_x_4180_;
v_isShared_4185_ = v_isSharedCheck_4190_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v_x_4180_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4190_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4188_; 
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
}
}
else
{
lean_object* v_a_4191_; lean_object* v_producers_4192_; lean_object* v_waiters_4193_; lean_object* v_capacity_4194_; lean_object* v_size_4195_; lean_object* v_buffer_4196_; lean_object* v_write_4197_; lean_object* v_read_4198_; lean_object* v_receivers_4199_; lean_object* v_nextId_4200_; uint8_t v_closed_4201_; lean_object* v_pos_4202_; lean_object* v___x_4203_; lean_object* v___f_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v_a_4191_ = lean_ctor_get(v_x_4180_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v_x_4180_, 1);
v_producers_4192_ = lean_ctor_get(v_a_4191_, 0);
lean_inc_ref(v_producers_4192_);
v_waiters_4193_ = lean_ctor_get(v_a_4191_, 1);
lean_inc_ref(v_waiters_4193_);
v_capacity_4194_ = lean_ctor_get(v_a_4191_, 2);
lean_inc(v_capacity_4194_);
v_size_4195_ = lean_ctor_get(v_a_4191_, 3);
lean_inc(v_size_4195_);
v_buffer_4196_ = lean_ctor_get(v_a_4191_, 4);
lean_inc_ref(v_buffer_4196_);
v_write_4197_ = lean_ctor_get(v_a_4191_, 5);
lean_inc(v_write_4197_);
v_read_4198_ = lean_ctor_get(v_a_4191_, 6);
lean_inc(v_read_4198_);
v_receivers_4199_ = lean_ctor_get(v_a_4191_, 7);
lean_inc(v_receivers_4199_);
v_nextId_4200_ = lean_ctor_get(v_a_4191_, 8);
lean_inc(v_nextId_4200_);
v_closed_4201_ = lean_ctor_get_uint8(v_a_4191_, sizeof(void*)*10);
v_pos_4202_ = lean_ctor_get(v_a_4191_, 9);
lean_inc(v_pos_4202_);
lean_dec(v_a_4191_);
v___x_4203_ = lean_box(v_closed_4201_);
lean_inc(v___y_4179_);
v___f_4204_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4204_, 0, v_producers_4192_);
lean_closure_set(v___f_4204_, 1, v_capacity_4194_);
lean_closure_set(v___f_4204_, 2, v_size_4195_);
lean_closure_set(v___f_4204_, 3, v_buffer_4196_);
lean_closure_set(v___f_4204_, 4, v_write_4197_);
lean_closure_set(v___f_4204_, 5, v_read_4198_);
lean_closure_set(v___f_4204_, 6, v_receivers_4199_);
lean_closure_set(v___f_4204_, 7, v_nextId_4200_);
lean_closure_set(v___f_4204_, 8, v___x_4203_);
lean_closure_set(v___f_4204_, 9, v_pos_4202_);
lean_closure_set(v___f_4204_, 10, v___y_4179_);
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = 0;
v___x_4207_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4193_, v___y_4179_);
v___x_4208_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4205_, v___x_4206_, v___x_4207_, v___f_4204_);
return v___x_4208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4209_, lean_object* v_x_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4209_, v_x_4210_);
lean_dec(v___y_4209_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4213_){
_start:
{
lean_object* v___f_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
lean_inc(v___y_4213_);
v___f_4215_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4215_, 0, v___y_4213_);
v___x_4216_ = lean_unsigned_to_nat(0u);
v___x_4217_ = 0;
v___x_4218_ = lean_st_ref_get(v___y_4213_);
v___x_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4218_);
v___x_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
v___x_4221_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4216_, v___x_4217_, v___x_4220_, v___f_4215_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4222_);
lean_dec(v___y_4222_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4225_, lean_object* v_waiter_4226_){
_start:
{
lean_object* v_val_4229_; lean_object* v___x_4231_; 
v___x_4231_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4225_, v_waiter_4226_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4231_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
lean_ctor_set_tag(v___x_4234_, 1);
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
v_val_4229_ = v___x_4237_;
goto v___jp_4228_;
}
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
v_a_4240_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4231_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4231_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
lean_ctor_set_tag(v___x_4242_, 0);
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
v_val_4229_ = v___x_4245_;
goto v___jp_4228_;
}
}
}
v___jp_4228_:
{
lean_object* v___x_4230_; 
v___x_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4230_, 0, v_val_4229_);
return v___x_4230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4248_, lean_object* v_waiter_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4248_, v_waiter_4249_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4252_){
_start:
{
if (lean_obj_tag(v_x_4252_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4262_; 
v_a_4254_ = lean_ctor_get(v_x_4252_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_x_4252_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4256_ = v_x_4252_;
v_isShared_4257_ = v_isSharedCheck_4262_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v_x_4252_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4262_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4259_; 
if (v_isShared_4257_ == 0)
{
v___x_4259_ = v___x_4256_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4254_);
v___x_4259_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4260_; 
v___x_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4259_);
return v___x_4260_;
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4272_; 
v_a_4263_ = lean_ctor_get(v_x_4252_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_x_4252_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4265_ = v_x_4252_;
v_isShared_4266_ = v_isSharedCheck_4272_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v_x_4252_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4272_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4267_; lean_object* v___x_4269_; 
v___x_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4267_, 0, v_a_4263_);
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
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4273_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4276_, lean_object* v_x_4277_){
_start:
{
if (lean_obj_tag(v_x_4277_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref(v_x_4276_);
v_a_4279_ = lean_ctor_get(v_x_4277_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v_x_4277_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4281_ = v_x_4277_;
v_isShared_4282_ = v_isSharedCheck_4287_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v_x_4277_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4287_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
lean_object* v___x_4285_; 
v___x_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4284_);
return v___x_4285_;
}
}
}
else
{
lean_object* v___x_4288_; 
lean_dec_ref_known(v_x_4277_, 1);
v___x_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4288_, 0, v_x_4276_);
return v___x_4288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4289_, lean_object* v_x_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4289_, v_x_4290_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4295_, lean_object* v_receiverId_4296_, lean_object* v_receivers_4297_, lean_object* v_x_4298_){
_start:
{
if (lean_obj_tag(v_x_4298_) == 0)
{
lean_object* v___x_4300_; 
lean_dec(v_receivers_4297_);
lean_dec(v_receiverId_4296_);
v___x_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4300_, 0, v_x_4298_);
return v___x_4300_;
}
else
{
lean_object* v_a_4301_; 
v_a_4301_ = lean_ctor_get(v_x_4298_, 0);
if (lean_obj_tag(v_a_4301_) == 1)
{
lean_object* v___f_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v_producers_4306_; lean_object* v_waiters_4307_; lean_object* v_capacity_4308_; lean_object* v_size_4309_; lean_object* v_buffer_4310_; lean_object* v_write_4311_; lean_object* v_read_4312_; lean_object* v_nextId_4313_; uint8_t v_closed_4314_; lean_object* v_pos_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4326_; 
v___f_4302_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4302_, 0, v_x_4298_);
v___x_4303_ = lean_unsigned_to_nat(0u);
v___x_4304_ = 0;
v___x_4305_ = lean_st_ref_take(v_a_4295_);
v_producers_4306_ = lean_ctor_get(v___x_4305_, 0);
v_waiters_4307_ = lean_ctor_get(v___x_4305_, 1);
v_capacity_4308_ = lean_ctor_get(v___x_4305_, 2);
v_size_4309_ = lean_ctor_get(v___x_4305_, 3);
v_buffer_4310_ = lean_ctor_get(v___x_4305_, 4);
v_write_4311_ = lean_ctor_get(v___x_4305_, 5);
v_read_4312_ = lean_ctor_get(v___x_4305_, 6);
v_nextId_4313_ = lean_ctor_get(v___x_4305_, 8);
v_closed_4314_ = lean_ctor_get_uint8(v___x_4305_, sizeof(void*)*10);
v_pos_4315_ = lean_ctor_get(v___x_4305_, 9);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; 
v_unused_4327_ = lean_ctor_get(v___x_4305_, 7);
lean_dec(v_unused_4327_);
v___x_4317_ = v___x_4305_;
v_isShared_4318_ = v_isSharedCheck_4326_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_pos_4315_);
lean_inc(v_nextId_4313_);
lean_inc(v_read_4312_);
lean_inc(v_write_4311_);
lean_inc(v_buffer_4310_);
lean_inc(v_size_4309_);
lean_inc(v_capacity_4308_);
lean_inc(v_waiters_4307_);
lean_inc(v_producers_4306_);
lean_dec(v___x_4305_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4326_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4319_; lean_object* v___x_4321_; 
v___x_4319_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4296_, v_receivers_4297_);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 7, v___x_4319_);
v___x_4321_ = v___x_4317_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_producers_4306_);
lean_ctor_set(v_reuseFailAlloc_4325_, 1, v_waiters_4307_);
lean_ctor_set(v_reuseFailAlloc_4325_, 2, v_capacity_4308_);
lean_ctor_set(v_reuseFailAlloc_4325_, 3, v_size_4309_);
lean_ctor_set(v_reuseFailAlloc_4325_, 4, v_buffer_4310_);
lean_ctor_set(v_reuseFailAlloc_4325_, 5, v_write_4311_);
lean_ctor_set(v_reuseFailAlloc_4325_, 6, v_read_4312_);
lean_ctor_set(v_reuseFailAlloc_4325_, 7, v___x_4319_);
lean_ctor_set(v_reuseFailAlloc_4325_, 8, v_nextId_4313_);
lean_ctor_set(v_reuseFailAlloc_4325_, 9, v_pos_4315_);
lean_ctor_set_uint8(v_reuseFailAlloc_4325_, sizeof(void*)*10, v_closed_4314_);
v___x_4321_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4322_ = lean_st_ref_put(v_a_4295_, v___x_4321_);
v___x_4323_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4324_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4303_, v___x_4304_, v___x_4323_, v___f_4302_);
return v___x_4324_;
}
}
}
else
{
lean_object* v___x_4328_; 
lean_dec_ref_known(v_x_4298_, 1);
lean_dec(v_receivers_4297_);
lean_dec(v_receiverId_4296_);
v___x_4328_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4328_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4329_, lean_object* v_receiverId_4330_, lean_object* v_receivers_4331_, lean_object* v_x_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4329_, v_receiverId_4330_, v_receivers_4331_, v_x_4332_);
lean_dec(v_a_4329_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4335_){
_start:
{
if (lean_obj_tag(v_x_4335_) == 0)
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4345_; 
v_a_4337_ = lean_ctor_get(v_x_4335_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v_x_4335_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4339_ = v_x_4335_;
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v_x_4335_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4345_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
lean_object* v___x_4343_; 
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
return v___x_4343_;
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4358_; 
v_a_4346_ = lean_ctor_get(v_x_4335_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v_x_4335_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4348_ = v_x_4335_;
v_isShared_4349_ = v_isSharedCheck_4358_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v_x_4335_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4358_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v_size_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4355_; 
v_size_4350_ = lean_ctor_get(v_a_4346_, 3);
lean_inc(v_size_4350_);
lean_dec(v_a_4346_);
v___x_4351_ = lean_unsigned_to_nat(0u);
v___x_4352_ = lean_nat_dec_eq(v_size_4350_, v___x_4351_);
lean_dec(v_size_4350_);
v___x_4353_ = lean_box(v___x_4352_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 0, v___x_4353_);
v___x_4355_ = v___x_4348_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4353_);
v___x_4355_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
lean_object* v___x_4356_; 
v___x_4356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4355_);
return v___x_4356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4359_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4363_){
_start:
{
lean_object* v___f_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___f_4365_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4366_ = lean_unsigned_to_nat(0u);
v___x_4367_ = 0;
v___x_4368_ = lean_st_ref_get(v_a_4363_);
v___x_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
v___x_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4369_);
v___x_4371_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4366_, v___x_4367_, v___x_4370_, v___f_4365_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4372_);
lean_dec(v_a_4372_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4375_, lean_object* v_next_4376_){
_start:
{
lean_object* v___x_4378_; lean_object* v_fst_4380_; lean_object* v_snd_4381_; lean_object* v_value_4385_; lean_object* v_pos_4386_; lean_object* v_remaining_4387_; uint8_t v___x_4388_; 
v___x_4378_ = lean_st_ref_take(v_slot_4375_);
v_value_4385_ = lean_ctor_get(v___x_4378_, 0);
v_pos_4386_ = lean_ctor_get(v___x_4378_, 1);
v_remaining_4387_ = lean_ctor_get(v___x_4378_, 2);
v___x_4388_ = lean_nat_dec_eq(v_next_4376_, v_pos_4386_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4389_ = lean_box(0);
v___x_4390_ = lean_box(v___x_4388_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v_fst_4380_ = v___x_4391_;
v_snd_4381_ = v___x_4378_;
goto v___jp_4379_;
}
else
{
lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4410_; 
lean_inc(v_remaining_4387_);
lean_inc(v_pos_4386_);
lean_inc(v_value_4385_);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4410_ == 0)
{
lean_object* v_unused_4411_; lean_object* v_unused_4412_; lean_object* v_unused_4413_; 
v_unused_4411_ = lean_ctor_get(v___x_4378_, 2);
lean_dec(v_unused_4411_);
v_unused_4412_ = lean_ctor_get(v___x_4378_, 1);
lean_dec(v_unused_4412_);
v_unused_4413_ = lean_ctor_get(v___x_4378_, 0);
lean_dec(v_unused_4413_);
v___x_4393_ = v___x_4378_;
v_isShared_4394_ = v_isSharedCheck_4410_;
goto v_resetjp_4392_;
}
else
{
lean_dec(v___x_4378_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4410_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; uint8_t v___x_4396_; 
v___x_4395_ = lean_unsigned_to_nat(1u);
v___x_4396_ = lean_nat_dec_eq(v_remaining_4387_, v___x_4395_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4401_; 
v___x_4397_ = lean_box(v___x_4396_);
lean_inc(v_value_4385_);
v___x_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4398_, 0, v_value_4385_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = lean_nat_sub(v_remaining_4387_, v___x_4395_);
lean_dec(v_remaining_4387_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 2, v___x_4399_);
v___x_4401_ = v___x_4393_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_value_4385_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_pos_4386_);
lean_ctor_set(v_reuseFailAlloc_4402_, 2, v___x_4399_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
v_fst_4380_ = v___x_4398_;
v_snd_4381_ = v___x_4401_;
goto v___jp_4379_;
}
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4408_; 
lean_dec(v_remaining_4387_);
v___x_4403_ = lean_box(v___x_4388_);
v___x_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4404_, 0, v_value_4385_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
v___x_4405_ = lean_box(0);
v___x_4406_ = lean_unsigned_to_nat(0u);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 2, v___x_4406_);
lean_ctor_set(v___x_4393_, 0, v___x_4405_);
v___x_4408_ = v___x_4393_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4405_);
lean_ctor_set(v_reuseFailAlloc_4409_, 1, v_pos_4386_);
lean_ctor_set(v_reuseFailAlloc_4409_, 2, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
v_fst_4380_ = v___x_4404_;
v_snd_4381_ = v___x_4408_;
goto v___jp_4379_;
}
}
}
}
v___jp_4379_:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = lean_st_ref_put(v_slot_4375_, v_snd_4381_);
v___x_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4383_, 0, v_fst_4380_);
v___x_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
return v___x_4384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4414_, lean_object* v_next_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4414_, v_next_4415_);
lean_dec(v_next_4415_);
lean_dec(v_slot_4414_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4418_, uint8_t v_a_4419_, lean_object* v___f_4420_, lean_object* v_x_4421_){
_start:
{
if (lean_obj_tag(v_x_4421_) == 0)
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4431_; 
lean_dec_ref(v___f_4420_);
v_a_4423_ = lean_ctor_get(v_x_4421_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v_x_4421_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4425_ = v_x_4421_;
v_isShared_4426_ = v_isSharedCheck_4431_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v_x_4421_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4431_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
return v___x_4429_;
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v_a_4432_ = lean_ctor_get(v_x_4421_, 0);
lean_inc(v_a_4432_);
lean_dec_ref_known(v_x_4421_, 1);
v___x_4433_ = lean_unsigned_to_nat(0u);
v___x_4434_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4432_, v_next_4418_);
lean_dec(v_a_4432_);
v___x_4435_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4433_, v_a_4419_, v___x_4434_, v___f_4420_);
return v___x_4435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4436_, lean_object* v_a_4437_, lean_object* v___f_4438_, lean_object* v_x_4439_, lean_object* v___y_4440_){
_start:
{
uint8_t v_a_12032__boxed_4441_; lean_object* v_res_4442_; 
v_a_12032__boxed_4441_ = lean_unbox(v_a_4437_);
v_res_4442_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4436_, v_a_12032__boxed_4441_, v___f_4438_, v_x_4439_);
lean_dec(v_next_4436_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4443_, lean_object* v___f_4444_, lean_object* v_____r_4445_, lean_object* v_st_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4449_ = lean_unsigned_to_nat(0u);
v___x_4450_ = lean_st_ref_swap(v___y_4447_, v_st_4446_);
lean_dec(v___x_4450_);
v___x_4451_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4452_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4449_, v_a_4443_, v___x_4451_, v___f_4444_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4453_, lean_object* v___f_4454_, lean_object* v_____r_4455_, lean_object* v_st_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
uint8_t v_a_12074__boxed_4459_; lean_object* v_res_4460_; 
v_a_12074__boxed_4459_ = lean_unbox(v_a_4453_);
v_res_4460_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_12074__boxed_4459_, v___f_4454_, v_____r_4455_, v_st_4456_, v___y_4457_);
lean_dec(v___y_4457_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4461_, lean_object* v_waiters_4462_, lean_object* v_capacity_4463_, lean_object* v_size_4464_, lean_object* v_buffer_4465_, lean_object* v_write_4466_, lean_object* v_read_4467_, lean_object* v_receivers_4468_, lean_object* v_nextId_4469_, uint8_t v_closed_4470_, lean_object* v_pos_4471_, lean_object* v___f_4472_, lean_object* v_a_4473_, lean_object* v_x_4474_){
_start:
{
if (lean_obj_tag(v_x_4474_) == 0)
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4484_; 
lean_dec_ref(v___f_4472_);
lean_dec(v_pos_4471_);
lean_dec(v_nextId_4469_);
lean_dec(v_receivers_4468_);
lean_dec(v_read_4467_);
lean_dec(v_write_4466_);
lean_dec_ref(v_buffer_4465_);
lean_dec(v_size_4464_);
lean_dec(v_capacity_4463_);
lean_dec_ref(v_waiters_4462_);
lean_dec_ref(v_snd_4461_);
v_a_4476_ = lean_ctor_get(v_x_4474_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v_x_4474_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4478_ = v_x_4474_;
v_isShared_4479_ = v_isSharedCheck_4484_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v_x_4474_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4484_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
lean_object* v___x_4482_; 
v___x_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4481_);
return v___x_4482_;
}
}
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_dec_ref_known(v_x_4474_, 1);
v___x_4485_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4485_, 0, v_snd_4461_);
lean_ctor_set(v___x_4485_, 1, v_waiters_4462_);
lean_ctor_set(v___x_4485_, 2, v_capacity_4463_);
lean_ctor_set(v___x_4485_, 3, v_size_4464_);
lean_ctor_set(v___x_4485_, 4, v_buffer_4465_);
lean_ctor_set(v___x_4485_, 5, v_write_4466_);
lean_ctor_set(v___x_4485_, 6, v_read_4467_);
lean_ctor_set(v___x_4485_, 7, v_receivers_4468_);
lean_ctor_set(v___x_4485_, 8, v_nextId_4469_);
lean_ctor_set(v___x_4485_, 9, v_pos_4471_);
lean_ctor_set_uint8(v___x_4485_, sizeof(void*)*10, v_closed_4470_);
v___x_4486_ = lean_box(0);
lean_inc(v_a_4473_);
v___x_4487_ = lean_apply_4(v___f_4472_, v___x_4486_, v___x_4485_, v_a_4473_, lean_box(0));
return v___x_4487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4488_, lean_object* v_waiters_4489_, lean_object* v_capacity_4490_, lean_object* v_size_4491_, lean_object* v_buffer_4492_, lean_object* v_write_4493_, lean_object* v_read_4494_, lean_object* v_receivers_4495_, lean_object* v_nextId_4496_, lean_object* v_closed_4497_, lean_object* v_pos_4498_, lean_object* v___f_4499_, lean_object* v_a_4500_, lean_object* v_x_4501_, lean_object* v___y_4502_){
_start:
{
uint8_t v_closed_boxed_4503_; lean_object* v_res_4504_; 
v_closed_boxed_4503_ = lean_unbox(v_closed_4497_);
v_res_4504_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4488_, v_waiters_4489_, v_capacity_4490_, v_size_4491_, v_buffer_4492_, v_write_4493_, v_read_4494_, v_receivers_4495_, v_nextId_4496_, v_closed_boxed_4503_, v_pos_4498_, v___f_4499_, v_a_4500_, v_x_4501_);
lean_dec(v_a_4500_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4505_, lean_object* v_x_4506_){
_start:
{
if (lean_obj_tag(v_x_4506_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v_fst_4505_);
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
lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4524_; 
v_isSharedCheck_4524_ = !lean_is_exclusive(v_x_4506_);
if (v_isSharedCheck_4524_ == 0)
{
lean_object* v_unused_4525_; 
v_unused_4525_ = lean_ctor_get(v_x_4506_, 0);
lean_dec(v_unused_4525_);
v___x_4518_ = v_x_4506_;
v_isShared_4519_ = v_isSharedCheck_4524_;
goto v_resetjp_4517_;
}
else
{
lean_dec(v_x_4506_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4524_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
lean_ctor_set(v___x_4518_, 0, v_fst_4505_);
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_fst_4505_);
v___x_4521_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_object* v___x_4522_; 
v___x_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
return v___x_4522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4526_, lean_object* v_x_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4526_, v_x_4527_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, uint8_t v___x_4533_, lean_object* v_x_4534_){
_start:
{
if (lean_obj_tag(v_x_4534_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4544_; 
lean_dec_ref(v_a_4531_);
v_a_4536_ = lean_ctor_get(v_x_4534_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4538_ = v_x_4534_;
v_isShared_4539_ = v_isSharedCheck_4544_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v_x_4534_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4544_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
lean_object* v___x_4542_; 
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4592_; 
v_a_4545_ = lean_ctor_get(v_x_4534_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4547_ = v_x_4534_;
v_isShared_4548_ = v_isSharedCheck_4592_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v_x_4534_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4592_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v_fst_4549_; 
v_fst_4549_ = lean_ctor_get(v_a_4545_, 0);
lean_inc(v_fst_4549_);
if (lean_obj_tag(v_fst_4549_) == 1)
{
lean_object* v_snd_4550_; lean_object* v___f_4551_; lean_object* v___x_4552_; lean_object* v___f_4553_; uint8_t v___x_4554_; 
v_snd_4550_ = lean_ctor_get(v_a_4545_, 1);
lean_inc(v_snd_4550_);
lean_dec(v_a_4545_);
v___f_4551_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4551_, 0, v_fst_4549_);
v___x_4552_ = lean_box(v_a_4530_);
lean_inc_ref(v___f_4551_);
v___f_4553_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4553_, 0, v___x_4552_);
lean_closure_set(v___f_4553_, 1, v___f_4551_);
v___x_4554_ = lean_unbox(v_snd_4550_);
lean_dec(v_snd_4550_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; lean_object* v___x_4556_; 
lean_dec_ref(v___f_4553_);
lean_del_object(v___x_4547_);
v___x_4555_ = lean_box(0);
v___x_4556_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4530_, v___f_4551_, v___x_4555_, v_a_4531_, v_a_4532_);
return v___x_4556_;
}
else
{
lean_object* v___x_4557_; lean_object* v_producers_4558_; lean_object* v_waiters_4559_; lean_object* v_capacity_4560_; lean_object* v_size_4561_; lean_object* v_buffer_4562_; lean_object* v_write_4563_; lean_object* v_read_4564_; lean_object* v_receivers_4565_; lean_object* v_nextId_4566_; uint8_t v_closed_4567_; lean_object* v_pos_4568_; lean_object* v___x_4569_; 
v___x_4557_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4531_);
v_producers_4558_ = lean_ctor_get(v___x_4557_, 0);
v_waiters_4559_ = lean_ctor_get(v___x_4557_, 1);
v_capacity_4560_ = lean_ctor_get(v___x_4557_, 2);
v_size_4561_ = lean_ctor_get(v___x_4557_, 3);
v_buffer_4562_ = lean_ctor_get(v___x_4557_, 4);
v_write_4563_ = lean_ctor_get(v___x_4557_, 5);
v_read_4564_ = lean_ctor_get(v___x_4557_, 6);
v_receivers_4565_ = lean_ctor_get(v___x_4557_, 7);
v_nextId_4566_ = lean_ctor_get(v___x_4557_, 8);
v_closed_4567_ = lean_ctor_get_uint8(v___x_4557_, sizeof(void*)*10);
v_pos_4568_ = lean_ctor_get(v___x_4557_, 9);
lean_inc_ref(v_producers_4558_);
v___x_4569_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4558_);
if (lean_obj_tag(v___x_4569_) == 1)
{
lean_object* v_val_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4588_; 
lean_inc(v_pos_4568_);
lean_inc(v_nextId_4566_);
lean_inc(v_receivers_4565_);
lean_inc(v_read_4564_);
lean_inc(v_write_4563_);
lean_inc_ref(v_buffer_4562_);
lean_inc(v_size_4561_);
lean_inc(v_capacity_4560_);
lean_inc_ref(v_waiters_4559_);
lean_dec_ref(v___x_4557_);
lean_dec_ref(v___f_4551_);
v_val_4570_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4572_ = v___x_4569_;
v_isShared_4573_ = v_isSharedCheck_4588_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_val_4570_);
lean_dec(v___x_4569_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4588_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v_fst_4574_; lean_object* v_snd_4575_; lean_object* v___x_4576_; lean_object* v___f_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
v_fst_4574_ = lean_ctor_get(v_val_4570_, 0);
lean_inc(v_fst_4574_);
v_snd_4575_ = lean_ctor_get(v_val_4570_, 1);
lean_inc(v_snd_4575_);
lean_dec(v_val_4570_);
v___x_4576_ = lean_box(v_closed_4567_);
lean_inc(v_a_4532_);
v___f_4577_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4577_, 0, v_snd_4575_);
lean_closure_set(v___f_4577_, 1, v_waiters_4559_);
lean_closure_set(v___f_4577_, 2, v_capacity_4560_);
lean_closure_set(v___f_4577_, 3, v_size_4561_);
lean_closure_set(v___f_4577_, 4, v_buffer_4562_);
lean_closure_set(v___f_4577_, 5, v_write_4563_);
lean_closure_set(v___f_4577_, 6, v_read_4564_);
lean_closure_set(v___f_4577_, 7, v_receivers_4565_);
lean_closure_set(v___f_4577_, 8, v_nextId_4566_);
lean_closure_set(v___f_4577_, 9, v___x_4576_);
lean_closure_set(v___f_4577_, 10, v_pos_4568_);
lean_closure_set(v___f_4577_, 11, v___f_4553_);
lean_closure_set(v___f_4577_, 12, v_a_4532_);
v___x_4578_ = lean_unsigned_to_nat(0u);
v___x_4579_ = lean_box(v___x_4533_);
v___x_4580_ = lean_io_promise_resolve(v___x_4579_, v_fst_4574_);
lean_dec(v_fst_4574_);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 0, v___x_4580_);
v___x_4582_ = v___x_4547_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4584_; 
if (v_isShared_4573_ == 0)
{
lean_ctor_set_tag(v___x_4572_, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4582_);
v___x_4584_ = v___x_4572_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4582_);
v___x_4584_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; 
v___x_4585_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4578_, v_a_4530_, v___x_4584_, v___f_4577_);
return v___x_4585_;
}
}
}
}
else
{
lean_object* v___x_4589_; lean_object* v___x_4590_; 
lean_dec(v___x_4569_);
lean_dec_ref(v___f_4553_);
lean_del_object(v___x_4547_);
v___x_4589_ = lean_box(0);
v___x_4590_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4530_, v___f_4551_, v___x_4589_, v___x_4557_, v_a_4532_);
return v___x_4590_;
}
}
}
else
{
lean_object* v___x_4591_; 
lean_dec(v_fst_4549_);
lean_del_object(v___x_4547_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4531_);
v___x_4591_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v___x_4596_, lean_object* v_x_4597_, lean_object* v___y_4598_){
_start:
{
uint8_t v_a_12186__boxed_4599_; uint8_t v___x_12188__boxed_4600_; lean_object* v_res_4601_; 
v_a_12186__boxed_4599_ = lean_unbox(v_a_4593_);
v___x_12188__boxed_4600_ = lean_unbox(v___x_4596_);
v_res_4601_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12186__boxed_4599_, v_a_4594_, v_a_4595_, v___x_12188__boxed_4600_, v_x_4597_);
lean_dec(v_a_4595_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_next_4604_, lean_object* v_x_4605_){
_start:
{
if (lean_obj_tag(v_x_4605_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4615_; 
lean_dec(v_next_4604_);
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
lean_object* v_a_4616_; uint8_t v___x_4617_; 
v_a_4616_ = lean_ctor_get(v_x_4605_, 0);
lean_inc(v_a_4616_);
lean_dec_ref_known(v_x_4605_, 1);
v___x_4617_ = lean_unbox(v_a_4616_);
if (v___x_4617_ == 0)
{
lean_object* v_capacity_4618_; uint8_t v___x_4619_; lean_object* v___x_4620_; lean_object* v___f_4621_; lean_object* v___f_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; uint8_t v___x_4626_; lean_object* v___x_4627_; 
v_capacity_4618_ = lean_ctor_get(v_a_4602_, 2);
lean_inc(v_capacity_4618_);
v___x_4619_ = 1;
v___x_4620_ = lean_box(v___x_4619_);
lean_inc(v_a_4603_);
lean_inc_n(v_a_4616_, 2);
v___f_4621_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4621_, 0, v_a_4616_);
lean_closure_set(v___f_4621_, 1, v_a_4602_);
lean_closure_set(v___f_4621_, 2, v_a_4603_);
lean_closure_set(v___f_4621_, 3, v___x_4620_);
lean_inc(v_next_4604_);
v___f_4622_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4622_, 0, v_next_4604_);
lean_closure_set(v___f_4622_, 1, v_a_4616_);
lean_closure_set(v___f_4622_, 2, v___f_4621_);
v___x_4623_ = lean_nat_mod(v_next_4604_, v_capacity_4618_);
lean_dec(v_capacity_4618_);
lean_dec(v_next_4604_);
v___x_4624_ = lean_unsigned_to_nat(0u);
v___x_4625_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4623_, v_a_4603_);
v___x_4626_ = lean_unbox(v_a_4616_);
lean_dec(v_a_4616_);
v___x_4627_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4624_, v___x_4626_, v___x_4625_, v___f_4622_);
return v___x_4627_;
}
else
{
lean_object* v___x_4628_; 
lean_dec(v_a_4616_);
lean_dec(v_next_4604_);
lean_dec_ref(v_a_4602_);
v___x_4628_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_next_4631_, lean_object* v_x_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4629_, v_a_4630_, v_next_4631_, v_x_4632_);
lean_dec(v_a_4630_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4635_, lean_object* v_next_4636_, lean_object* v_x_4637_){
_start:
{
if (lean_obj_tag(v_x_4637_) == 0)
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4647_; 
lean_dec(v_next_4636_);
v_a_4639_ = lean_ctor_get(v_x_4637_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v_x_4637_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4641_ = v_x_4637_;
v_isShared_4642_ = v_isSharedCheck_4647_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v_x_4637_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4647_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; 
v___x_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4644_);
return v___x_4645_;
}
}
}
else
{
lean_object* v_a_4648_; lean_object* v___f_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; 
v_a_4648_ = lean_ctor_get(v_x_4637_, 0);
lean_inc(v_a_4648_);
lean_dec_ref_known(v_x_4637_, 1);
lean_inc(v_a_4635_);
v___f_4649_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4649_, 0, v_a_4648_);
lean_closure_set(v___f_4649_, 1, v_a_4635_);
lean_closure_set(v___f_4649_, 2, v_next_4636_);
v___x_4650_ = lean_unsigned_to_nat(0u);
v___x_4651_ = 0;
v___x_4652_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4635_);
v___x_4653_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4650_, v___x_4651_, v___x_4652_, v___f_4649_);
return v___x_4653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4654_, lean_object* v_next_4655_, lean_object* v_x_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4654_, v_next_4655_, v_x_4656_);
lean_dec(v_a_4654_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4659_, lean_object* v_a_4660_){
_start:
{
lean_object* v___f_4662_; lean_object* v___x_4663_; uint8_t v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
lean_inc(v_a_4660_);
v___f_4662_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4662_, 0, v_a_4660_);
lean_closure_set(v___f_4662_, 1, v_next_4659_);
v___x_4663_ = lean_unsigned_to_nat(0u);
v___x_4664_ = 0;
v___x_4665_ = lean_st_ref_get(v_a_4660_);
v___x_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
v___x_4668_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4663_, v___x_4664_, v___x_4667_, v___f_4662_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4669_, lean_object* v_a_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4669_, v_a_4670_);
lean_dec(v_a_4670_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4673_, lean_object* v_a_4674_, lean_object* v_x_4675_){
_start:
{
if (lean_obj_tag(v_x_4675_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4685_; 
lean_dec(v_receiverId_4673_);
v_a_4677_ = lean_ctor_get(v_x_4675_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v_x_4675_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4679_ = v_x_4675_;
v_isShared_4680_ = v_isSharedCheck_4685_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v_x_4675_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4685_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4683_; 
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4682_);
return v___x_4683_;
}
}
}
else
{
lean_object* v_a_4686_; lean_object* v_receivers_4687_; lean_object* v___x_4688_; 
v_a_4686_ = lean_ctor_get(v_x_4675_, 0);
lean_inc(v_a_4686_);
lean_dec_ref_known(v_x_4675_, 1);
v_receivers_4687_ = lean_ctor_get(v_a_4686_, 7);
lean_inc(v_receivers_4687_);
lean_dec(v_a_4686_);
v___x_4688_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4687_, v_receiverId_4673_);
if (lean_obj_tag(v___x_4688_) == 1)
{
lean_object* v_val_4689_; lean_object* v___f_4690_; lean_object* v___x_4691_; uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; 
v_val_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_val_4689_);
lean_dec_ref_known(v___x_4688_, 1);
lean_inc(v_a_4674_);
v___f_4690_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4690_, 0, v_a_4674_);
lean_closure_set(v___f_4690_, 1, v_receiverId_4673_);
lean_closure_set(v___f_4690_, 2, v_receivers_4687_);
v___x_4691_ = lean_unsigned_to_nat(0u);
v___x_4692_ = 0;
v___x_4693_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4689_, v_a_4674_);
v___x_4694_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4691_, v___x_4692_, v___x_4693_, v___f_4690_);
return v___x_4694_;
}
else
{
lean_object* v___x_4695_; 
lean_dec(v___x_4688_);
lean_dec(v_receivers_4687_);
lean_dec(v_receiverId_4673_);
v___x_4695_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4696_, lean_object* v_a_4697_, lean_object* v_x_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4696_, v_a_4697_, v_x_4698_);
lean_dec(v_a_4697_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4701_, lean_object* v_a_4702_){
_start:
{
lean_object* v___f_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
lean_inc(v_a_4702_);
v___f_4704_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4704_, 0, v_receiverId_4701_);
lean_closure_set(v___f_4704_, 1, v_a_4702_);
v___x_4705_ = lean_unsigned_to_nat(0u);
v___x_4706_ = 0;
v___x_4707_ = lean_st_ref_get(v_a_4702_);
v___x_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4707_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
v___x_4710_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4705_, v___x_4706_, v___x_4709_, v___f_4704_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4711_, lean_object* v_a_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4711_, v_a_4712_);
lean_dec(v_a_4712_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_id_4719_, lean_object* v___y_4720_, lean_object* v___f_4721_, lean_object* v_x_4722_){
_start:
{
if (lean_obj_tag(v_x_4722_) == 0)
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4732_; 
lean_dec_ref(v___f_4721_);
lean_dec(v_id_4719_);
v_a_4724_ = lean_ctor_get(v_x_4722_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v_x_4722_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4726_ = v_x_4722_;
v_isShared_4727_ = v_isSharedCheck_4732_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v_x_4722_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4732_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
lean_object* v___x_4730_; 
v___x_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4730_, 0, v___x_4729_);
return v___x_4730_;
}
}
}
else
{
lean_object* v_a_4733_; uint8_t v___x_4734_; 
v_a_4733_ = lean_ctor_get(v_x_4722_, 0);
lean_inc(v_a_4733_);
lean_dec_ref_known(v_x_4722_, 1);
v___x_4734_ = lean_unbox(v_a_4733_);
lean_dec(v_a_4733_);
if (v___x_4734_ == 0)
{
lean_object* v___x_4735_; 
lean_dec_ref(v___f_4721_);
lean_dec(v_id_4719_);
v___x_4735_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__1));
return v___x_4735_;
}
else
{
lean_object* v___x_4736_; uint8_t v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4736_ = lean_unsigned_to_nat(0u);
v___x_4737_ = 0;
v___x_4738_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4719_, v___y_4720_);
v___x_4739_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4736_, v___x_4737_, v___x_4738_, v___f_4721_);
return v___x_4739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_id_4740_, lean_object* v___y_4741_, lean_object* v___f_4742_, lean_object* v_x_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_id_4740_, v___y_4741_, v___f_4742_, v_x_4743_);
lean_dec(v___y_4741_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v_val_4746_, lean_object* v_x_4747_){
_start:
{
if (lean_obj_tag(v_x_4747_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4757_; 
v_a_4749_ = lean_ctor_get(v_x_4747_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_x_4747_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4751_ = v_x_4747_;
v_isShared_4752_ = v_isSharedCheck_4757_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v_x_4747_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4757_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
lean_object* v___x_4755_; 
v___x_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4754_);
return v___x_4755_;
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4769_; 
v_a_4758_ = lean_ctor_get(v_x_4747_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v_x_4747_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4760_ = v_x_4747_;
v_isShared_4761_ = v_isSharedCheck_4769_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v_x_4747_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4769_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v_pos_4762_; uint8_t v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4766_; 
v_pos_4762_ = lean_ctor_get(v_a_4758_, 1);
lean_inc(v_pos_4762_);
lean_dec(v_a_4758_);
v___x_4763_ = lean_nat_dec_eq(v_pos_4762_, v_val_4746_);
lean_dec(v_pos_4762_);
v___x_4764_ = lean_box(v___x_4763_);
if (v_isShared_4761_ == 0)
{
lean_ctor_set(v___x_4760_, 0, v___x_4764_);
v___x_4766_ = v___x_4760_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v___x_4764_);
v___x_4766_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4767_; 
v___x_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
return v___x_4767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v_val_4770_, lean_object* v_x_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v_val_4770_, v_x_4771_);
lean_dec(v_val_4770_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v___x_4774_, uint8_t v_closed_4775_, lean_object* v___f_4776_, lean_object* v_x_4777_){
_start:
{
if (lean_obj_tag(v_x_4777_) == 0)
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4787_; 
lean_dec_ref(v___f_4776_);
lean_dec(v___x_4774_);
v_a_4779_ = lean_ctor_get(v_x_4777_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_x_4777_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4781_ = v_x_4777_;
v_isShared_4782_ = v_isSharedCheck_4787_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v_x_4777_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4787_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
lean_object* v___x_4785_; 
v___x_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
return v___x_4785_;
}
}
}
else
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4798_; 
v_a_4788_ = lean_ctor_get(v_x_4777_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v_x_4777_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4790_ = v_x_4777_;
v_isShared_4791_ = v_isSharedCheck_4798_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v_x_4777_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4798_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4792_; lean_object* v___x_4794_; 
v___x_4792_ = lean_st_ref_get(v_a_4788_);
lean_dec(v_a_4788_);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4792_);
v___x_4794_ = v___x_4790_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4792_);
v___x_4794_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
v___x_4796_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4774_, v_closed_4775_, v___x_4795_, v___f_4776_);
return v___x_4796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v___x_4799_, lean_object* v_closed_4800_, lean_object* v___f_4801_, lean_object* v_x_4802_, lean_object* v___y_4803_){
_start:
{
uint8_t v_closed_boxed_4804_; lean_object* v_res_4805_; 
v_closed_boxed_4804_ = lean_unbox(v_closed_4800_);
v_res_4805_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v___x_4799_, v_closed_boxed_4804_, v___f_4801_, v_x_4802_);
return v_res_4805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4806_, lean_object* v___x_4807_, lean_object* v___y_4808_, lean_object* v_x_4809_){
_start:
{
if (lean_obj_tag(v_x_4809_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4819_; 
lean_dec(v___x_4807_);
v_a_4811_ = lean_ctor_get(v_x_4809_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v_x_4809_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4813_ = v_x_4809_;
v_isShared_4814_ = v_isSharedCheck_4819_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v_x_4809_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4819_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4816_);
return v___x_4817_;
}
}
}
else
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4858_; 
v_a_4820_ = lean_ctor_get(v_x_4809_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v_x_4809_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4822_ = v_x_4809_;
v_isShared_4823_ = v_isSharedCheck_4858_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v_x_4809_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4858_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
uint8_t v_closed_4824_; 
v_closed_4824_ = lean_ctor_get_uint8(v_a_4820_, sizeof(void*)*10);
if (v_closed_4824_ == 0)
{
lean_object* v_capacity_4825_; lean_object* v_size_4826_; lean_object* v_receivers_4827_; lean_object* v___x_4828_; 
v_capacity_4825_ = lean_ctor_get(v_a_4820_, 2);
lean_inc(v_capacity_4825_);
v_size_4826_ = lean_ctor_get(v_a_4820_, 3);
lean_inc(v_size_4826_);
v_receivers_4827_ = lean_ctor_get(v_a_4820_, 7);
lean_inc(v_receivers_4827_);
lean_dec(v_a_4820_);
v___x_4828_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4827_, v_id_4806_);
lean_dec(v_receivers_4827_);
if (lean_obj_tag(v___x_4828_) == 1)
{
lean_object* v_val_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4847_; 
v_val_4829_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4831_ = v___x_4828_;
v_isShared_4832_ = v_isSharedCheck_4847_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_val_4829_);
lean_dec(v___x_4828_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4847_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
uint8_t v___x_4833_; 
v___x_4833_ = lean_nat_dec_eq(v_size_4826_, v___x_4807_);
lean_dec(v_size_4826_);
if (v___x_4833_ == 0)
{
lean_object* v___f_4834_; lean_object* v___x_4835_; lean_object* v___f_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
lean_del_object(v___x_4831_);
lean_del_object(v___x_4822_);
lean_inc(v_val_4829_);
v___f_4834_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4834_, 0, v_val_4829_);
v___x_4835_ = lean_box(v_closed_4824_);
lean_inc(v___x_4807_);
v___f_4836_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 5, 3);
lean_closure_set(v___f_4836_, 0, v___x_4807_);
lean_closure_set(v___f_4836_, 1, v___x_4835_);
lean_closure_set(v___f_4836_, 2, v___f_4834_);
v___x_4837_ = lean_nat_mod(v_val_4829_, v_capacity_4825_);
lean_dec(v_capacity_4825_);
lean_dec(v_val_4829_);
v___x_4838_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4837_, v___y_4808_);
v___x_4839_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4807_, v___x_4833_, v___x_4838_, v___f_4836_);
return v___x_4839_;
}
else
{
lean_object* v___x_4840_; lean_object* v___x_4842_; 
lean_dec(v_val_4829_);
lean_dec(v_capacity_4825_);
lean_dec(v___x_4807_);
v___x_4840_ = lean_box(v_closed_4824_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v___x_4840_);
v___x_4842_ = v___x_4822_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v___x_4840_);
v___x_4842_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
lean_object* v___x_4844_; 
if (v_isShared_4832_ == 0)
{
lean_ctor_set_tag(v___x_4831_, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4842_);
v___x_4844_ = v___x_4831_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4842_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
else
{
lean_object* v___x_4848_; lean_object* v___x_4850_; 
lean_dec(v___x_4828_);
lean_dec(v_size_4826_);
lean_dec(v_capacity_4825_);
lean_dec(v___x_4807_);
v___x_4848_ = lean_box(v_closed_4824_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v___x_4848_);
v___x_4850_ = v___x_4822_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
lean_object* v___x_4851_; 
v___x_4851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4850_);
return v___x_4851_;
}
}
}
else
{
lean_object* v___x_4853_; lean_object* v___x_4855_; 
lean_dec(v_a_4820_);
lean_dec(v___x_4807_);
v___x_4853_ = lean_box(v_closed_4824_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v___x_4853_);
v___x_4855_ = v___x_4822_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
lean_object* v___x_4856_; 
v___x_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
return v___x_4856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_4859_, lean_object* v___x_4860_, lean_object* v___y_4861_, lean_object* v_x_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4859_, v___x_4860_, v___y_4861_, v_x_4862_);
lean_dec(v___y_4861_);
lean_dec(v_id_4859_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_4865_, lean_object* v___f_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v___f_4869_; lean_object* v___x_4870_; lean_object* v___f_4871_; uint8_t v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
lean_inc_n(v___y_4867_, 2);
lean_inc(v_id_4865_);
v___f_4869_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4869_, 0, v_id_4865_);
lean_closure_set(v___f_4869_, 1, v___y_4867_);
lean_closure_set(v___f_4869_, 2, v___f_4866_);
v___x_4870_ = lean_unsigned_to_nat(0u);
v___f_4871_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4871_, 0, v_id_4865_);
lean_closure_set(v___f_4871_, 1, v___x_4870_);
lean_closure_set(v___f_4871_, 2, v___y_4867_);
v___x_4872_ = 0;
v___x_4873_ = lean_st_ref_get(v___y_4867_);
v___x_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
v___x_4875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4874_);
v___x_4876_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4870_, v___x_4872_, v___x_4875_, v___f_4871_);
v___x_4877_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4870_, v___x_4872_, v___x_4876_, v___f_4869_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_4878_, lean_object* v___f_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_4878_, v___f_4879_, v___y_4880_);
lean_dec(v___y_4880_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_4885_){
_start:
{
lean_object* v_state_4886_; lean_object* v_id_4887_; lean_object* v___f_4888_; lean_object* v___f_4889_; lean_object* v___f_4890_; lean_object* v___f_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v_state_4886_ = lean_ctor_get(v_ch_4885_, 0);
lean_inc_ref_n(v_state_4886_, 2);
v_id_4887_ = lean_ctor_get(v_ch_4885_, 1);
lean_inc(v_id_4887_);
v___f_4888_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_4889_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4889_, 0, v_ch_4885_);
v___f_4890_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_4891_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_4891_, 0, v_id_4887_);
lean_closure_set(v___f_4891_, 1, v___f_4890_);
v___x_4892_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4892_, 0, lean_box(0));
lean_closure_set(v___x_4892_, 1, lean_box(0));
lean_closure_set(v___x_4892_, 2, v_state_4886_);
lean_closure_set(v___x_4892_, 3, v___f_4891_);
v___x_4893_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_4893_, 0, lean_box(0));
lean_closure_set(v___x_4893_, 1, lean_box(0));
lean_closure_set(v___x_4893_, 2, v_state_4886_);
lean_closure_set(v___x_4893_, 3, v___f_4888_);
v___x_4894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4892_);
lean_ctor_set(v___x_4894_, 1, v___f_4889_);
lean_ctor_set(v___x_4894_, 2, v___x_4893_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_4895_, lean_object* v_ch_4896_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_4896_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_4898_, lean_object* v_receiverId_4899_, lean_object* v_a_4900_){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4899_, v_a_4900_);
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_4903_, lean_object* v_receiverId_4904_, lean_object* v_a_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_4903_, v_receiverId_4904_, v_a_4905_);
lean_dec(v_a_4905_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_4908_, lean_object* v_q_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4909_, v___y_4910_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_4913_, lean_object* v_q_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v_res_4917_; 
v_res_4917_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_4913_, v_q_4914_, v___y_4915_);
lean_dec(v___y_4915_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_4918_, lean_object* v_slot_4919_, lean_object* v_next_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4919_, v_next_4920_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_4924_, lean_object* v_slot_4925_, lean_object* v_next_4926_, lean_object* v_a_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_4924_, v_slot_4925_, v_next_4926_, v_a_4927_);
lean_dec(v_a_4927_);
lean_dec(v_next_4926_);
lean_dec(v_slot_4925_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4930_, lean_object* v_a_4931_){
_start:
{
lean_object* v___x_4933_; 
v___x_4933_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4931_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4934_, lean_object* v_a_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_4934_, v_a_4935_);
lean_dec(v_a_4935_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_4938_, lean_object* v_next_4939_, lean_object* v_a_4940_){
_start:
{
lean_object* v___x_4942_; 
v___x_4942_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4939_, v_a_4940_);
return v___x_4942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_4943_, lean_object* v_next_4944_, lean_object* v_a_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_4943_, v_next_4944_, v_a_4945_);
lean_dec(v_a_4945_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_4948_, lean_object* v_x_4949_, lean_object* v_x_4950_, lean_object* v___y_4951_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4949_, v_x_4950_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_4954_, lean_object* v_x_4955_, lean_object* v_x_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_4954_, v_x_4955_, v_x_4956_, v___y_4957_);
lean_dec(v___y_4957_);
return v_res_4959_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_4960_; 
v___x_4960_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_4960_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_4961_){
_start:
{
lean_object* v___x_4963_; 
v___x_4963_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4961_);
return v___x_4963_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l_Std_Broadcast_new___redArg(v_capacity_4964_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_4967_, lean_object* v_capacity_4968_, lean_object* v_h_4969_){
_start:
{
lean_object* v___x_4971_; 
v___x_4971_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_4968_);
return v___x_4971_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_4972_, lean_object* v_capacity_4973_, lean_object* v_h_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Std_Broadcast_new(v_00_u03b1_4972_, v_capacity_4973_, v_h_4974_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_4977_, lean_object* v_v_4978_){
_start:
{
lean_object* v___x_4980_; 
v___x_4980_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4977_, v_v_4978_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_4981_, lean_object* v_v_4982_, lean_object* v_a_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l_Std_Broadcast_trySend___redArg(v_ch_4981_, v_v_4982_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_4985_, lean_object* v_ch_4986_, lean_object* v_v_4987_){
_start:
{
lean_object* v___x_4989_; 
v___x_4989_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_4986_, v_v_4987_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_4990_, lean_object* v_ch_4991_, lean_object* v_v_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Std_Broadcast_trySend(v_00_u03b1_4990_, v_ch_4991_, v_v_4992_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_4995_){
_start:
{
lean_object* v___x_4997_; 
v___x_4997_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_4995_);
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
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
v_a_5006_ = lean_ctor_get(v___x_4997_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4997_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4997_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Std_Broadcast_subscribe___redArg(v_ch_5014_);
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_5017_, lean_object* v_ch_5018_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_5018_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_5020_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5020_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
v_a_5029_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_5020_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5020_);
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
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_5037_, lean_object* v_ch_5038_, lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l_Std_Broadcast_subscribe(v_00_u03b1_5037_, v_ch_5038_);
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_5041_){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5041_);
if (lean_obj_tag(v___x_5043_) == 0)
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
v_a_5044_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v___x_5043_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_5043_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5069_; 
v_a_5052_ = lean_ctor_get(v___x_5043_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v___x_5043_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5054_ = v___x_5043_;
v_isShared_5055_ = v_isSharedCheck_5069_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5043_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5069_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
uint8_t v___x_5056_; 
v___x_5056_ = lean_unbox(v_a_5052_);
lean_dec(v_a_5052_);
switch(v___x_5056_)
{
case 0:
{
lean_object* v___x_5057_; lean_object* v___x_5059_; 
v___x_5057_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5057_);
v___x_5059_ = v___x_5054_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5060_; 
v_reuseFailAlloc_5060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5057_);
v___x_5059_ = v_reuseFailAlloc_5060_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
return v___x_5059_;
}
}
case 1:
{
lean_object* v___x_5061_; lean_object* v___x_5063_; 
v___x_5061_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5061_);
v___x_5063_ = v___x_5054_;
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
default: 
{
lean_object* v___x_5065_; lean_object* v___x_5067_; 
v___x_5065_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5065_);
v___x_5067_ = v___x_5054_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5070_, lean_object* v_a_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l_Std_Broadcast_close___redArg(v_ch_5070_);
return v_res_5072_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5073_, lean_object* v_ch_5074_){
_start:
{
lean_object* v___x_5076_; 
v___x_5076_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5074_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5076_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5076_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5102_; 
v_a_5085_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5087_ = v___x_5076_;
v_isShared_5088_ = v_isSharedCheck_5102_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5076_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5102_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
uint8_t v___x_5089_; 
v___x_5089_ = lean_unbox(v_a_5085_);
lean_dec(v_a_5085_);
switch(v___x_5089_)
{
case 0:
{
lean_object* v___x_5090_; lean_object* v___x_5092_; 
v___x_5090_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 0, v___x_5090_);
v___x_5092_ = v___x_5087_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v___x_5090_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
case 1:
{
lean_object* v___x_5094_; lean_object* v___x_5096_; 
v___x_5094_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 0, v___x_5094_);
v___x_5096_ = v___x_5087_;
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
default: 
{
lean_object* v___x_5098_; lean_object* v___x_5100_; 
v___x_5098_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5088_ == 0)
{
lean_ctor_set(v___x_5087_, 0, v___x_5098_);
v___x_5100_ = v___x_5087_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5103_, lean_object* v_ch_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l_Std_Broadcast_close(v_00_u03b1_5103_, v_ch_5104_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5107_){
_start:
{
lean_object* v___y_5110_; 
if (lean_obj_tag(v_x_5107_) == 0)
{
lean_object* v_a_5114_; uint8_t v___x_5115_; 
v_a_5114_ = lean_ctor_get(v_x_5107_, 0);
lean_inc(v_a_5114_);
lean_dec_ref_known(v_x_5107_, 1);
v___x_5115_ = lean_unbox(v_a_5114_);
lean_dec(v_a_5114_);
switch(v___x_5115_)
{
case 0:
{
lean_object* v___x_5116_; 
v___x_5116_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5110_ = v___x_5116_;
goto v___jp_5109_;
}
case 1:
{
lean_object* v___x_5117_; 
v___x_5117_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5110_ = v___x_5117_;
goto v___jp_5109_;
}
default: 
{
lean_object* v___x_5118_; 
v___x_5118_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5110_ = v___x_5118_;
goto v___jp_5109_;
}
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5127_; 
v_a_5119_ = lean_ctor_get(v_x_5107_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v_x_5107_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5121_ = v_x_5107_;
v_isShared_5122_ = v_isSharedCheck_5127_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v_x_5107_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5127_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
lean_object* v___x_5125_; 
v___x_5125_ = lean_task_pure(v___x_5124_);
return v___x_5125_;
}
}
}
v___jp_5109_:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
lean_inc_ref(v___y_5110_);
v___x_5111_ = lean_mk_io_user_error(v___y_5110_);
v___x_5112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5112_, 0, v___x_5111_);
v___x_5113_ = lean_task_pure(v___x_5112_);
return v___x_5113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5128_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5132_, lean_object* v_v_5133_){
_start:
{
lean_object* v___f_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; uint8_t v___x_5138_; lean_object* v___x_5139_; 
v___f_5135_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5136_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5132_, v_v_5133_);
v___x_5137_ = lean_unsigned_to_nat(0u);
v___x_5138_ = 1;
v___x_5139_ = lean_io_bind_task(v___x_5136_, v___f_5135_, v___x_5137_, v___x_5138_);
return v___x_5139_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5140_, lean_object* v_v_5141_, lean_object* v_a_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l_Std_Broadcast_send___redArg(v_ch_5140_, v_v_5141_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5144_, lean_object* v_ch_5145_, lean_object* v_v_5146_){
_start:
{
lean_object* v___f_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; lean_object* v___x_5152_; 
v___f_5148_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5149_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5145_, v_v_5146_);
v___x_5150_ = lean_unsigned_to_nat(0u);
v___x_5151_ = 1;
v___x_5152_ = lean_io_bind_task(v___x_5149_, v___f_5148_, v___x_5150_, v___x_5151_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5153_, lean_object* v_ch_5154_, lean_object* v_v_5155_, lean_object* v_a_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Std_Broadcast_send(v_00_u03b1_5153_, v_ch_5154_, v_v_5155_);
return v_res_5157_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5158_){
_start:
{
lean_object* v___x_5160_; 
v___x_5160_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5158_);
return v___x_5160_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5161_, lean_object* v_a_5162_){
_start:
{
lean_object* v_res_5163_; 
v_res_5163_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5161_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5164_, lean_object* v_ch_5165_){
_start:
{
lean_object* v___x_5167_; 
v___x_5167_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5165_);
return v___x_5167_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5168_, lean_object* v_ch_5169_, lean_object* v_a_5170_){
_start:
{
lean_object* v_res_5171_; 
v_res_5171_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5168_, v_ch_5169_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5172_){
_start:
{
lean_object* v___x_5174_; 
v___x_5174_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5172_);
return v___x_5174_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5175_, lean_object* v_a_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5175_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5178_, lean_object* v_inst_5179_, lean_object* v_ch_5180_){
_start:
{
lean_object* v___x_5182_; 
v___x_5182_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5180_);
return v___x_5182_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5183_, lean_object* v_inst_5184_, lean_object* v_ch_5185_, lean_object* v_a_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5183_, v_inst_5184_, v_ch_5185_);
lean_dec(v_inst_5184_);
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5188_){
_start:
{
lean_object* v___x_5189_; 
v___x_5189_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5188_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5190_, lean_object* v_inst_5191_, lean_object* v_ch_5192_){
_start:
{
lean_object* v___x_5193_; 
v___x_5193_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5192_);
return v___x_5193_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5194_, lean_object* v_inst_5195_, lean_object* v_ch_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5194_, v_inst_5195_, v_ch_5196_);
lean_dec(v_inst_5195_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5198_){
_start:
{
lean_object* v___x_5200_; 
v___x_5200_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5198_);
return v___x_5200_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5201_, lean_object* v_a_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5201_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5204_, lean_object* v_ch_5205_){
_start:
{
lean_object* v___x_5207_; 
v___x_5207_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5205_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5208_, lean_object* v_ch_5209_, lean_object* v_a_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5208_, v_ch_5209_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5212_, lean_object* v_ch_5213_, lean_object* v_prio_5214_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5212_, v_ch_5213_, v_prio_5214_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5217_, lean_object* v_ch_5218_, lean_object* v_prio_5219_, lean_object* v_a_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5217_, v_ch_5218_, v_prio_5219_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5222_, lean_object* v_f_5223_, lean_object* v_ch_5224_, lean_object* v_prio_5225_){
_start:
{
lean_object* v___x_5227_; 
v___x_5227_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5223_, v_ch_5224_, v_prio_5225_);
return v___x_5227_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5228_, lean_object* v_f_5229_, lean_object* v_ch_5230_, lean_object* v_prio_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v_res_5233_; 
v_res_5233_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5228_, v_f_5229_, v_ch_5230_, v_prio_5231_);
return v_res_5233_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg(){
_start:
{
lean_object* v___x_5240_; 
v___x_5240_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__2));
return v___x_5240_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object* v___dummy_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
return v_res_5242_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5243_; 
v___x_5243_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5244_, lean_object* v_inst_5245_){
_start:
{
lean_object* v___x_5246_; 
v___x_5246_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5247_, lean_object* v_inst_5248_){
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5247_, v_inst_5248_);
lean_dec(v_inst_5248_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object* v_a_5250_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5251_, 0, v_a_5250_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object* v___f_5252_, lean_object* v_x_5253_){
_start:
{
if (lean_obj_tag(v_x_5253_) == 0)
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5263_; 
lean_dec_ref(v___f_5252_);
v_a_5255_ = lean_ctor_get(v_x_5253_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v_x_5253_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5257_ = v_x_5253_;
v_isShared_5258_ = v_isSharedCheck_5263_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v_x_5253_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5263_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
lean_object* v___x_5261_; 
v___x_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
return v___x_5261_;
}
}
}
else
{
lean_object* v_a_5264_; 
v_a_5264_ = lean_ctor_get(v_x_5253_, 0);
lean_inc(v_a_5264_);
lean_dec_ref_known(v_x_5253_, 1);
if (lean_obj_tag(v_a_5264_) == 0)
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5273_; 
lean_dec_ref(v___f_5252_);
v_a_5265_ = lean_ctor_get(v_a_5264_, 0);
v_isSharedCheck_5273_ = !lean_is_exclusive(v_a_5264_);
if (v_isSharedCheck_5273_ == 0)
{
v___x_5267_ = v_a_5264_;
v_isShared_5268_ = v_isSharedCheck_5273_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v_a_5264_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5273_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5270_; 
if (v_isShared_5268_ == 0)
{
v___x_5270_ = v___x_5267_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5265_);
v___x_5270_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
lean_object* v___x_5271_; 
v___x_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5271_, 0, v___x_5270_);
return v___x_5271_;
}
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5275_; uint8_t v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; 
v_a_5274_ = lean_ctor_get(v_a_5264_, 0);
lean_inc(v_a_5274_);
lean_dec_ref_known(v_a_5264_, 1);
v___x_5275_ = lean_unsigned_to_nat(0u);
v___x_5276_ = 0;
v___x_5277_ = lean_task_map(v___f_5252_, v_a_5274_, v___x_5275_, v___x_5276_);
v___x_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5277_);
return v___x_5278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5279_, lean_object* v_x_5280_, lean_object* v___y_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_5279_, v_x_5280_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object* v___f_5283_, lean_object* v_receiver_5284_){
_start:
{
lean_object* v___x_5286_; uint8_t v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; 
v___x_5286_ = lean_unsigned_to_nat(0u);
v___x_5287_ = 0;
v___x_5288_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5284_);
v___x_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5288_);
v___x_5290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5289_);
v___x_5291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5290_);
v___x_5292_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5286_, v___x_5287_, v___x_5291_, v___f_5283_);
return v___x_5292_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5293_, lean_object* v_receiver_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_5293_, v_receiver_5294_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg(){
_start:
{
lean_object* v___f_5303_; 
v___f_5303_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__2));
return v___f_5303_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object* v___dummy_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
return v_res_5305_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5306_; 
v___x_5306_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
return v___x_5306_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5307_, lean_object* v_inst_5308_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5310_, lean_object* v_inst_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5310_, v_inst_5311_);
lean_dec(v_inst_5311_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v_x_5317_){
_start:
{
if (lean_obj_tag(v_x_5317_) == 0)
{
lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5327_; 
v_a_5319_ = lean_ctor_get(v_x_5317_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v_x_5317_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5321_ = v_x_5317_;
v_isShared_5322_ = v_isSharedCheck_5327_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_dec(v_x_5317_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5327_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5324_; 
if (v_isShared_5322_ == 0)
{
v___x_5324_ = v___x_5321_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5319_);
v___x_5324_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
lean_object* v___x_5325_; 
v___x_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5325_, 0, v___x_5324_);
return v___x_5325_;
}
}
}
else
{
lean_object* v_a_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; uint8_t v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; 
v_a_5328_ = lean_ctor_get(v_x_5317_, 0);
lean_inc(v_a_5328_);
lean_dec_ref_known(v_x_5317_, 1);
v___x_5329_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__1));
v___x_5330_ = lean_unsigned_to_nat(0u);
v___x_5331_ = 0;
v___x_5332_ = lean_task_map(v___x_5329_, v_a_5328_, v___x_5330_, v___x_5331_);
v___x_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5332_);
return v___x_5333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object* v_x_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(v_x_5334_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v___f_5337_, lean_object* v___f_5338_, lean_object* v_receiver_5339_, lean_object* v_x_5340_){
_start:
{
lean_object* v___x_5342_; uint8_t v___x_5343_; lean_object* v___x_5344_; uint8_t v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; 
v___x_5342_ = lean_unsigned_to_nat(0u);
v___x_5343_ = 0;
v___x_5344_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5339_, v_x_5340_);
v___x_5345_ = 1;
v___x_5346_ = lean_io_bind_task(v___x_5344_, v___f_5337_, v___x_5342_, v___x_5345_);
v___x_5347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5346_);
v___x_5348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5348_, 0, v___x_5347_);
v___x_5349_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5342_, v___x_5343_, v___x_5348_, v___f_5338_);
return v___x_5349_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5350_, lean_object* v___f_5351_, lean_object* v_receiver_5352_, lean_object* v_x_5353_, lean_object* v___y_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5350_, v___f_5351_, v_receiver_5352_, v_x_5353_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v_x_5356_){
_start:
{
lean_object* v___x_5358_; 
v___x_5358_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5358_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v_x_5359_, lean_object* v___y_5360_){
_start:
{
lean_object* v_res_5361_; 
v_res_5361_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(v_x_5359_);
lean_dec_ref(v_x_5359_);
return v_res_5361_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(lean_object* v___f_5362_, lean_object* v_socket_5363_, lean_object* v_x_5364_, lean_object* v___y_5365_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = lean_apply_3(v___f_5362_, v_socket_5363_, v___y_5365_, lean_box(0));
return v___x_5367_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object* v___f_5368_, lean_object* v_socket_5369_, lean_object* v_x_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(v___f_5368_, v_socket_5369_, v_x_5370_, v___y_5371_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(lean_object* v___f_5374_, lean_object* v___x_5375_, lean_object* v_socket_5376_, lean_object* v_data_5377_){
_start:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; uint8_t v___x_5382_; 
v___x_5379_ = lean_unsigned_to_nat(0u);
v___x_5380_ = lean_array_get_size(v_data_5377_);
v___x_5381_ = lean_box(0);
v___x_5382_ = lean_nat_dec_lt(v___x_5379_, v___x_5380_);
if (v___x_5382_ == 0)
{
lean_object* v___x_5383_; 
lean_dec_ref(v_data_5377_);
lean_dec_ref(v_socket_5376_);
lean_dec_ref(v___x_5375_);
lean_dec_ref(v___f_5374_);
v___x_5383_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5383_;
}
else
{
lean_object* v___f_5384_; uint8_t v___x_5385_; 
v___f_5384_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_5384_, 0, v___f_5374_);
lean_closure_set(v___f_5384_, 1, v_socket_5376_);
v___x_5385_ = lean_nat_dec_le(v___x_5380_, v___x_5380_);
if (v___x_5385_ == 0)
{
if (v___x_5382_ == 0)
{
lean_object* v___x_5386_; 
lean_dec_ref(v___f_5384_);
lean_dec_ref(v_data_5377_);
lean_dec_ref(v___x_5375_);
v___x_5386_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5386_;
}
else
{
size_t v___x_5387_; size_t v___x_5388_; lean_object* v___x_873__overap_5389_; lean_object* v___x_5390_; 
v___x_5387_ = ((size_t)0ULL);
v___x_5388_ = lean_usize_of_nat(v___x_5380_);
v___x_873__overap_5389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5375_, v___f_5384_, v_data_5377_, v___x_5387_, v___x_5388_, v___x_5381_);
v___x_5390_ = lean_apply_1(v___x_873__overap_5389_, lean_box(0));
return v___x_5390_;
}
}
else
{
size_t v___x_5391_; size_t v___x_5392_; lean_object* v___x_876__overap_5393_; lean_object* v___x_5394_; 
v___x_5391_ = ((size_t)0ULL);
v___x_5392_ = lean_usize_of_nat(v___x_5380_);
v___x_876__overap_5393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5375_, v___f_5384_, v_data_5377_, v___x_5391_, v___x_5392_, v___x_5381_);
v___x_5394_ = lean_apply_1(v___x_876__overap_5393_, lean_box(0));
return v___x_5394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object* v___f_5395_, lean_object* v___x_5396_, lean_object* v_socket_5397_, lean_object* v_data_5398_, lean_object* v___y_5399_){
_start:
{
lean_object* v_res_5400_; 
v_res_5400_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(v___f_5395_, v___x_5396_, v_socket_5397_, v_data_5398_);
return v_res_5400_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_5406_; 
v___x_5406_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_5406_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_5407_; lean_object* v___f_5408_; lean_object* v___f_5409_; 
v___x_5407_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5408_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1));
v___f_5409_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5409_, 0, v___f_5408_);
lean_closure_set(v___f_5409_, 1, v___x_5407_);
return v___f_5409_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5(void){
_start:
{
lean_object* v___f_5410_; lean_object* v___f_5411_; lean_object* v___f_5412_; lean_object* v___x_5413_; 
v___f_5410_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5411_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4);
v___f_5412_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1));
v___x_5413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5413_, 0, v___f_5412_);
lean_ctor_set(v___x_5413_, 1, v___f_5411_);
lean_ctor_set(v___x_5413_, 2, v___f_5410_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_5415_; 
v___x_5415_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5);
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_5416_){
_start:
{
lean_object* v_res_5417_; 
v_res_5417_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
return v_res_5417_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5418_; 
v___x_5418_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5419_, lean_object* v_inst_5420_){
_start:
{
lean_object* v___x_5421_; 
v___x_5421_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5422_, lean_object* v_inst_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5422_, v_inst_5423_);
lean_dec(v_inst_5423_);
return v_res_5424_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5425_; 
v___x_5425_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5425_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5426_){
_start:
{
lean_object* v___x_5428_; 
v___x_5428_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5426_);
return v___x_5428_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5429_, lean_object* v_a_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5429_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5432_, lean_object* v_capacity_5433_, lean_object* v_h_5434_){
_start:
{
lean_object* v___x_5436_; 
v___x_5436_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5433_);
return v___x_5436_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5437_, lean_object* v_capacity_5438_, lean_object* v_h_5439_, lean_object* v_a_5440_){
_start:
{
lean_object* v_res_5441_; 
v_res_5441_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5437_, v_capacity_5438_, v_h_5439_);
return v_res_5441_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5442_, lean_object* v_v_5443_){
_start:
{
lean_object* v___x_5445_; 
v___x_5445_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5442_, v_v_5443_);
return v___x_5445_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5446_, lean_object* v_v_5447_, lean_object* v_a_5448_){
_start:
{
lean_object* v_res_5449_; 
v_res_5449_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5446_, v_v_5447_);
return v_res_5449_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5450_, lean_object* v_ch_5451_, lean_object* v_v_5452_){
_start:
{
lean_object* v___x_5454_; 
v___x_5454_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5451_, v_v_5452_);
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5455_, lean_object* v_ch_5456_, lean_object* v_v_5457_, lean_object* v_a_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5455_, v_ch_5456_, v_v_5457_);
return v_res_5459_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5461_, lean_object* v_v_5462_){
_start:
{
lean_object* v___f_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; uint8_t v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; 
v___f_5464_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5465_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5466_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5461_, v_v_5462_);
v___x_5467_ = lean_unsigned_to_nat(0u);
v___x_5468_ = 1;
v___x_5469_ = lean_io_bind_task(v___x_5466_, v___f_5464_, v___x_5467_, v___x_5468_);
v___x_5470_ = lean_io_wait(v___x_5469_);
v___x_5471_ = l_IO_ofExcept___redArg(v___x_5465_, v___x_5470_);
return v___x_5471_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5472_, lean_object* v_v_5473_, lean_object* v_a_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5472_, v_v_5473_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5476_, lean_object* v_ch_5477_, lean_object* v_v_5478_){
_start:
{
lean_object* v___f_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; uint8_t v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___f_5480_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5481_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5482_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5477_, v_v_5478_);
v___x_5483_ = lean_unsigned_to_nat(0u);
v___x_5484_ = 1;
v___x_5485_ = lean_io_bind_task(v___x_5482_, v___f_5480_, v___x_5483_, v___x_5484_);
v___x_5486_ = lean_io_wait(v___x_5485_);
v___x_5487_ = l_IO_ofExcept___redArg(v___x_5481_, v___x_5486_);
return v___x_5487_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5488_, lean_object* v_ch_5489_, lean_object* v_v_5490_, lean_object* v_a_5491_){
_start:
{
lean_object* v_res_5492_; 
v_res_5492_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5488_, v_ch_5489_, v_v_5490_);
return v_res_5492_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5493_){
_start:
{
lean_object* v___x_5495_; 
v___x_5495_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5493_);
return v___x_5495_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5496_, lean_object* v_a_5497_){
_start:
{
lean_object* v_res_5498_; 
v_res_5498_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5496_);
return v_res_5498_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5499_, lean_object* v_ch_5500_){
_start:
{
lean_object* v___x_5502_; 
v___x_5502_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5500_);
return v___x_5502_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5503_, lean_object* v_ch_5504_, lean_object* v_a_5505_){
_start:
{
lean_object* v_res_5506_; 
v_res_5506_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5503_, v_ch_5504_);
return v_res_5506_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5507_){
_start:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; 
v___x_5509_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5507_);
v___x_5510_ = lean_io_wait(v___x_5509_);
return v___x_5510_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5511_, lean_object* v_a_5512_){
_start:
{
lean_object* v_res_5513_; 
v_res_5513_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5511_);
return v_res_5513_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5514_, lean_object* v_inst_5515_, lean_object* v_ch_5516_){
_start:
{
lean_object* v___x_5518_; 
v___x_5518_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5516_);
return v___x_5518_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5519_, lean_object* v_inst_5520_, lean_object* v_ch_5521_, lean_object* v_a_5522_){
_start:
{
lean_object* v_res_5523_; 
v_res_5523_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5519_, v_inst_5520_, v_ch_5521_);
lean_dec(v_inst_5520_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5524_, lean_object* v_b_5525_, lean_object* v_f_5526_, lean_object* v_toBind_5527_, lean_object* v___f_5528_, lean_object* v_a_5529_){
_start:
{
if (lean_obj_tag(v_a_5529_) == 0)
{
lean_object* v___x_5530_; 
lean_dec(v___f_5528_);
lean_dec(v_toBind_5527_);
lean_dec(v_f_5526_);
v___x_5530_ = lean_apply_2(v_toPure_5524_, lean_box(0), v_b_5525_);
return v___x_5530_;
}
else
{
lean_object* v_val_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; 
lean_dec(v_toPure_5524_);
v_val_5531_ = lean_ctor_get(v_a_5529_, 0);
lean_inc(v_val_5531_);
lean_dec_ref_known(v_a_5529_, 1);
v___x_5532_ = lean_apply_2(v_f_5526_, v_val_5531_, v_b_5525_);
v___x_5533_ = lean_apply_4(v_toBind_5527_, lean_box(0), lean_box(0), v___x_5532_, v___f_5528_);
return v___x_5533_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5534_, lean_object* v_inst_5535_, lean_object* v_inst_5536_, lean_object* v_ch_5537_, lean_object* v_f_5538_, lean_object* v_b_5539_){
_start:
{
lean_object* v_toApplicative_5540_; lean_object* v_toBind_5541_; lean_object* v_toPure_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___f_5545_; lean_object* v___f_5546_; lean_object* v___x_5547_; 
v_toApplicative_5540_ = lean_ctor_get(v_inst_5535_, 0);
v_toBind_5541_ = lean_ctor_get(v_inst_5535_, 1);
lean_inc_n(v_toBind_5541_, 2);
v_toPure_5542_ = lean_ctor_get(v_toApplicative_5540_, 1);
lean_inc_n(v_toPure_5542_, 2);
lean_inc_ref(v_ch_5537_);
lean_inc(v_inst_5534_);
v___x_5543_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5543_, 0, lean_box(0));
lean_closure_set(v___x_5543_, 1, v_inst_5534_);
lean_closure_set(v___x_5543_, 2, v_ch_5537_);
lean_inc(v_inst_5536_);
v___x_5544_ = lean_apply_2(v_inst_5536_, lean_box(0), v___x_5543_);
lean_inc(v_f_5538_);
v___f_5545_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5545_, 0, v_toPure_5542_);
lean_closure_set(v___f_5545_, 1, v_inst_5534_);
lean_closure_set(v___f_5545_, 2, v_inst_5535_);
lean_closure_set(v___f_5545_, 3, v_inst_5536_);
lean_closure_set(v___f_5545_, 4, v_ch_5537_);
lean_closure_set(v___f_5545_, 5, v_f_5538_);
v___f_5546_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5546_, 0, v_toPure_5542_);
lean_closure_set(v___f_5546_, 1, v_b_5539_);
lean_closure_set(v___f_5546_, 2, v_f_5538_);
lean_closure_set(v___f_5546_, 3, v_toBind_5541_);
lean_closure_set(v___f_5546_, 4, v___f_5545_);
v___x_5547_ = lean_apply_4(v_toBind_5541_, lean_box(0), lean_box(0), v___x_5544_, v___f_5546_);
return v___x_5547_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5548_, lean_object* v_inst_5549_, lean_object* v_inst_5550_, lean_object* v_inst_5551_, lean_object* v_ch_5552_, lean_object* v_f_5553_, lean_object* v_____do__lift_5554_){
_start:
{
if (lean_obj_tag(v_____do__lift_5554_) == 0)
{
lean_object* v_a_5555_; lean_object* v___x_5556_; 
lean_dec(v_f_5553_);
lean_dec_ref(v_ch_5552_);
lean_dec(v_inst_5551_);
lean_dec_ref(v_inst_5550_);
lean_dec(v_inst_5549_);
v_a_5555_ = lean_ctor_get(v_____do__lift_5554_, 0);
lean_inc(v_a_5555_);
lean_dec_ref_known(v_____do__lift_5554_, 1);
v___x_5556_ = lean_apply_2(v_toPure_5548_, lean_box(0), v_a_5555_);
return v___x_5556_;
}
else
{
lean_object* v_a_5557_; lean_object* v___x_5558_; 
lean_dec(v_toPure_5548_);
v_a_5557_ = lean_ctor_get(v_____do__lift_5554_, 0);
lean_inc(v_a_5557_);
lean_dec_ref_known(v_____do__lift_5554_, 1);
v___x_5558_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5549_, v_inst_5550_, v_inst_5551_, v_ch_5552_, v_f_5553_, v_a_5557_);
return v___x_5558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5559_, lean_object* v_m_5560_, lean_object* v_00_u03b2_5561_, lean_object* v_inst_5562_, lean_object* v_inst_5563_, lean_object* v_inst_5564_, lean_object* v_ch_5565_, lean_object* v_f_5566_, lean_object* v_b_5567_){
_start:
{
lean_object* v___x_5568_; 
v___x_5568_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5562_, v_inst_5563_, v_inst_5564_, v_ch_5565_, v_f_5566_, v_b_5567_);
return v___x_5568_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5569_, lean_object* v_inst_5570_, lean_object* v_inst_5571_, lean_object* v_00_u03b2_5572_, lean_object* v_ch_5573_, lean_object* v_b_5574_, lean_object* v_f_5575_){
_start:
{
lean_object* v___x_5576_; 
v___x_5576_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5569_, v_inst_5570_, v_inst_5571_, v_ch_5573_, v_f_5575_, v_b_5574_);
return v___x_5576_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5577_, lean_object* v_inst_5578_, lean_object* v_inst_5579_){
_start:
{
lean_object* v___f_5580_; 
v___f_5580_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5580_, 0, v_inst_5577_);
lean_closure_set(v___f_5580_, 1, v_inst_5578_);
lean_closure_set(v___f_5580_, 2, v_inst_5579_);
return v___f_5580_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5581_, lean_object* v_m_5582_, lean_object* v_inst_5583_, lean_object* v_inst_5584_, lean_object* v_inst_5585_){
_start:
{
lean_object* v___f_5586_; 
v___f_5586_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5586_, 0, v_inst_5583_);
lean_closure_set(v___f_5586_, 1, v_inst_5584_);
lean_closure_set(v___f_5586_, 2, v_inst_5585_);
return v___f_5586_;
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
